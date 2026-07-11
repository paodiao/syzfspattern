#include "MountOptDependencyExtractor.h"
#include "FilesystemExtractor.h"   // for getStFromIcmp, getStFromTrunc, etc.
#include "llvm/IR/CFG.h"
#include <fstream>

using namespace llvm;
using namespace std;

// ───────────────────────────────────────────────
// Known mount-option dependency checker functions
// (collected across 7 filesystems × 3 kernel versions)
// ───────────────────────────────────────────────
static const set<string> CheckerFuncNames = {
    // ext4
    "ext4_check_opt_consistency", "ext4_check_quota_consistency",
    "ext4_validate_options", "ext4_check_test_dummy_encryption",
    "ext4_feature_set_ok", "ext4_check_feature_compatibility",
    "ext4_check_geometry", "ext2_feature_set_ok", "ext3_feature_set_ok",
    "handle_mount_opt",
    // xfs
    "xfs_fs_validate_params", "xfs_validate_new_dalign",
    // btrfs
    "check_ro_option", "btrfs_check_options", "check_dev_super",
    // f2fs
    "f2fs_check_quota_options", "f2fs_disable_checkpoint", "f2fs_remount",
    // erofs
    "erofs_fc_set_dax_mode", "check_layout_compatibility",
    "z_erofs_parse_cfgs",
    // ntfs3
    "ntfs_fs_reconfigure",
};

// ───────────────────────────────────────────────
// Hardcoded cross-function dependencies
// ───────────────────────────────────────────────
static void addHardcodedBtrfsDeps(FsDeps& deps) {
    // extent-tree-v2 restricts many operations — use string names since tokens are unknown
    struct { const char* A; const char* B; const char* rel; const char* file; int line; } btrfsHard[] = {
        {"extent_tree_v2","snapshot_create",  "mutual_exclusion", "fs/btrfs/ioctl.c",   806},
        {"extent_tree_v2","snapshot_delete",  "mutual_exclusion", "fs/btrfs/inode.c",  4743},
        {"extent_tree_v2","device_add",       "mutual_exclusion", "fs/btrfs/ioctl.c",  2681},
        {"extent_tree_v2","device_remove",    "mutual_exclusion", "fs/btrfs/volumes.c",2164},
        {"extent_tree_v2","scrub",            "mutual_exclusion", "fs/btrfs/ioctl.c",  3231},
        {"extent_tree_v2","device_replace",   "mutual_exclusion", "fs/btrfs/ioctl.c",  3340},
        {"extent_tree_v2","qgroup",           "mutual_exclusion", "fs/btrfs/qgroup.c", 1033},
        {"extent_tree_v2","relocation",       "mutual_exclusion", "fs/btrfs/volumes.c",3387},
    };
    for (auto& h : btrfsHard) {
        MountOptCrossDep dep;
        dep.opt_A = 0; dep.opt_B = 0;
        dep.opt_A_name = h.A;
        dep.opt_B_name = h.B;
        dep.relation = h.rel;
        dep.src_file = h.file;
        dep.src_line = h.line;
        deps.cross.push_back(dep);
    }
}

void MountOptDependencyExtractor::mergeHardcodedDeps(const string& fsname, FsDeps& deps) {
    if (fsname == "btrfs")
        addHardcodedBtrfsDeps(deps);
}

// ───────────────────────────────────────────────
// Helper: ICmp predicate → string
// ───────────────────────────────────────────────
string MountOptDependencyExtractor::predToStr(CmpInst::Predicate p) {
    switch (p) {
        case CmpInst::ICMP_EQ:  return "eq";
        case CmpInst::ICMP_NE:  return "ne";
        case CmpInst::ICMP_UGT:
        case CmpInst::ICMP_SGT: return "gt";
        case CmpInst::ICMP_ULT:
        case CmpInst::ICMP_SLT: return "lt";
        case CmpInst::ICMP_UGE:
        case CmpInst::ICMP_SGE: return "ge";
        case CmpInst::ICMP_ULE:
        case CmpInst::ICMP_SLE: return "le";
        default: return "";
    }
}

// ───────────────────────────────────────────────
// Trace a Load/GEP value back to its fs2options key
// ───────────────────────────────────────────────
string MountOptDependencyExtractor::traceToFs2Options(
    Value* V,
    map<string, set<pair<pair<uint32_t, string>, pair<int, int>>>>& fs2options) {

    // Strip through intermediate instructions: And(mask), LShr(offset), ZExt, Trunc
    while (isa<CastInst>(V) || isa<BinaryOperator>(V)) {
        if (auto* CI = dyn_cast<CastInst>(V))
            V = CI->getOperand(0);
        else if (auto* BO = dyn_cast<BinaryOperator>(V)) {
            // For And/LShr patterns, take the non-constant operand
            if (isa<Constant>(BO->getOperand(0)) && !isa<Constant>(BO->getOperand(1)))
                V = BO->getOperand(1);
            else if (isa<Constant>(BO->getOperand(1)) && !isa<Constant>(BO->getOperand(0)))
                V = BO->getOperand(0);
            else
                break; // both non-constant or both constant — stop
        } else
            break;
    }

    auto* LI = dyn_cast<LoadInst>(V);
    if (!LI) return "";

    Value* ptr = LI->getPointerOperand();
    if (auto* BCI = dyn_cast<BitCastInst>(ptr))
        ptr = BCI->getOperand(0);
    auto* GEP = dyn_cast<GetElementPtrInst>(ptr);
    if (!GEP) return "";

    if (!GEP->getSourceElementType()->isStructTy() ||
        !GEP->hasAllConstantIndices() || GEP->getNumIndices() != 2)
        return "";

    auto* offCI = dyn_cast<ConstantInt>(GEP->getOperand(2));
    if (!offCI) return "";

    string key = GEP->getSourceElementType()->getStructName().str() +
                 to_string(offCI->getZExtValue());
    if (fs2options.find(key) != fs2options.end())
        return key;
    return "";
}

// ───────────────────────────────────────────────
// Extract self-dependencies from ICmp→ConstantInt patterns
// ───────────────────────────────────────────────
void MountOptDependencyExtractor::extractSelfDeps(
    const set<Function*>& funcs,
    const map<int, pair<string, int>>& flagParams,
    const map<int, pair<string, int>>& intParams,
    map<pair<int, string>, map<int, string>>& enumParams,
    map<string, set<pair<pair<uint32_t, string>, pair<int, int>>>>& fs2options,
    FsDeps& deps) {

    for (auto* F : funcs) {
    for (auto& BB : *F) {
        for (auto& I : BB) {
            auto* BI = dyn_cast<BranchInst>(&I);
            if (!BI || !BI->isConditional()) continue;

            auto* icmp = dyn_cast<ICmpInst>(BI->getCondition());
            if (!icmp) continue;

            // Find which operand is a constant, which is an Instruction
            ConstantInt* C = nullptr;
            Instruction* opI = nullptr;
            if ((C = dyn_cast<ConstantInt>(icmp->getOperand(0))))
                opI = dyn_cast<Instruction>(icmp->getOperand(1));
            else if ((C = dyn_cast<ConstantInt>(icmp->getOperand(1))))
                opI = dyn_cast<Instruction>(icmp->getOperand(0));
            if (!C || !opI) continue;

            // Trace opI back to an fs2options entry
            string key = traceToFs2Options(opI, fs2options);
            if (key.empty()) continue;

            // Get the fs2options entries for this field
            auto& optSet = fs2options[key];
            if (optSet.empty()) continue;

            uint64_t cval = C->getZExtValue();
            auto pred = icmp->getPredicate();

            // Determine which option this field belongs to
            for (auto& entry : optSet) {
                int optToken = entry.second.first;
                string cfgType = entry.first.second;

                // Find the option name from our parameter maps
                string optName;
                auto fit = flagParams.find(optToken);
                if (fit != flagParams.end()) optName = fit->second.first;
                else {
                    auto iit = intParams.find(optToken);
                    if (iit != intParams.end()) optName = iit->second.first;
                    if (optName.empty() && !enumParams.empty()) {
                        for (auto& enumopt : enumParams) {
                            if (enumopt.first.first == optToken) {
                                optName = enumopt.first.second;
                                break;
                            }
                        }
                    }
                }
            
                if (optName.empty()) continue;

                // For assignint/assignenum: value range check
                // Follow interPro.cpp logic: predicate direction directly gives constraint type
                if (cfgType == "assignint" || cfgType == "assignenum") {
                    MountOptSelfConstraint sc;
                    sc.opt_token = optToken;
                    sc.opt_name = optName;
                    sc.dep_type = "range";

                    // ICMP_UGT(34)/ICMP_SGT(38): a > X is error → safe range is a <= X → max = X
                    if (pred == CmpInst::ICMP_UGT || pred == CmpInst::ICMP_SGT) {
                        sc.max_val = cval;
                    }
                    // ICMP_ULT(36)/ICMP_SLT(40): a < X is error → safe range is a >= X → min = X
                    else if (pred == CmpInst::ICMP_ULT || pred == CmpInst::ICMP_SLT) {
                        sc.min_val = cval;
                    }
                    // ICMP_UGE(35)/ICMP_SGE(39): a >= X is error → safe range is a <= X-1 → max = X-1
                    else if (pred == CmpInst::ICMP_UGE || pred == CmpInst::ICMP_SGE) {
                        sc.max_val = cval - 1;
                    }
                    // ICMP_ULE(37)/ICMP_SLE(41): a <= X is error → safe range is a >= X+1 → min = X+1
                    else if (pred == CmpInst::ICMP_ULE || pred == CmpInst::ICMP_SLE) {
                        sc.min_val = cval + 1;
                    }
                    // ICMP_NE: discrete valid values
                    else if (pred == CmpInst::ICMP_NE) {
                        sc.dep_type = "discrete";
                        sc.valid_values.insert(cval);
                    }
                    if (sc.max_val != 0 || sc.min_val != 0 || !sc.valid_values.empty())
                        deps.self.push_back(sc);
                }
            }
        }
    }
    // Extract enum valid values from enumParams as discrete self-deps
    for (auto& ep : enumParams) {
        int optnum = ep.first.first;
        auto& subvals = ep.second;
        if (subvals.empty()) continue;
        bool hasExisting = false;
        for (auto& s : deps.self) {
            if (s.opt_token == optnum && s.dep_type == "discrete") {
                hasExisting = true; break;
            }
        }
        if (hasExisting) continue;
        MountOptSelfConstraint sc;
        sc.opt_token = optnum;
        sc.opt_name = ep.first.second;
        sc.dep_type = "discrete";
        for (auto& sv : subvals)
            sc.valid_values.insert(static_cast<uint64_t>(sv.first));
        deps.self.push_back(sc);
    }
    } // for funcs
}

// ───────────────────────────────────────────────
// Extract cross-option dependencies
// ───────────────────────────────────────────────
void MountOptDependencyExtractor::extractCrossDeps(
    const set<Function*>& funcs,
    const set<string>& relatedSt,
    map<string, set<pair<pair<uint32_t, string>, pair<int, int>>>>& fs2options,
    map<pair<string, pair<uint32_t, string>>, OneLayerPairSet>& fs2options2onelayer,
    FsDeps& deps) {

    for (auto* F : funcs) {
    for (auto& BB : *F) {
        for (auto& I : BB) {
            auto* BI = dyn_cast<BranchInst>(&I);
            if (!BI || !BI->isConditional()) continue;

            auto* icmp = dyn_cast<ICmpInst>(BI->getCondition());
            if (!icmp) continue;

            // Try to trace both operands to fs2options entries
            string keyA = traceToFs2Options(icmp->getOperand(0), fs2options);
            string keyB = traceToFs2Options(icmp->getOperand(1), fs2options);

            // If both sides trace to different fs2options entries → cross-option dependency
            if (keyA.empty() || keyB.empty() || keyA == keyB) continue;

            auto& setA = fs2options[keyA];
            auto& setB = fs2options[keyB];
            if (setA.empty() || setB.empty()) continue;

            // Get option tokens from both sides
            int optA = setA.begin()->second.first;
            int optB = setB.begin()->second.first;
            if (optA == optB) continue; // same option, not cross

            MountOptCrossDep dep;
            dep.opt_A = optA;
            dep.opt_B = optB;
            dep.opt_A_name = "";
            dep.opt_B_name = "";
            dep.src_line = 0; // could extract from debug info

            auto pred = icmp->getPredicate();
            if (pred == CmpInst::ICMP_UGT || pred == CmpInst::ICMP_SGT)
                dep.relation = "must_be_smaller";
            else if (pred == CmpInst::ICMP_ULT || pred == CmpInst::ICMP_SLT)
                dep.relation = "must_be_greater";
            else if (pred == CmpInst::ICMP_EQ)
                dep.relation = "mutual_exclusion";
            else if (pred == CmpInst::ICMP_NE)
                dep.relation = "requires";
            else
                continue;

            deps.cross.push_back(dep);
            //修改：感觉少了个检测是不是错误路径的判断（条件分支里是否报错），不过可以先试着用一下
        }
    }

    // Also check fs2options2onelayer for propagated cross-dependencies
    for (auto& olentry : fs2options2onelayer) {
        auto& destKey = olentry.first;
        string destStruct = destKey.first;
        auto& srcSet = olentry.second;

        for (auto& olv : srcSet) {
            auto& srcKey = olv.first.first;
            // dest field depends on src field → if they're different options, cross-dep
            if (fs2options.find(destStruct) != fs2options.end() &&
                fs2options.find(srcKey) != fs2options.end()) {
                auto& destOpts = fs2options[destStruct];
                auto& srcOpts = fs2options[srcKey];
                if (!destOpts.empty() && !srcOpts.empty()) {
                    int optDest = destOpts.begin()->second.first;
                    int optSrc = srcOpts.begin()->second.first;
                    if (optDest != optSrc) {
                        MountOptCrossDep dep;
                        dep.opt_A = optSrc;
                        dep.opt_B = optDest;
                        dep.opt_A_name = "";
                        dep.opt_B_name = "";
                        dep.relation = "silent_enable";  // may be refineable via cfgtype
                        //修改：不一定是silent_enable，还要检查它是怎么设置的来确定，说不定是silent_disable呢？。。。不过我感觉不太会有这种依赖关系，就算了吧
                        dep.src_line = 0;
                        deps.cross.push_back(dep);
            }
        }
    }
}
    }
    } // for funcs
}

// ───────────────────────────────────────────────
// Extract silent dependencies: Branch(ICmp A) → Store(And/Or on B)
// ───────────────────────────────────────────────
void MountOptDependencyExtractor::extractSilentDeps(
    const set<Function*>& funcs,
    map<string, set<pair<pair<uint32_t, string>, pair<int, int>>>>& fs2options,
    FsDeps& deps) {

    for (auto* F : funcs) {
    for (auto& BB : *F) {
        for (auto& I : BB) {
            auto* BI = dyn_cast<BranchInst>(&I);
            if (!BI || !BI->isConditional()) continue;

            auto* icmp = dyn_cast<ICmpInst>(BI->getCondition());
            if (!icmp) continue;

            // Find the BB that executes when the condition is true
            BasicBlock* trueBB = BI->getSuccessor(0);

            // Look for Store(And/Or) in the true successor
            for (auto& SI : *trueBB) {
                auto* sti = dyn_cast<StoreInst>(&SI);
                if (!sti) continue;

                auto* storeVal = dyn_cast<Instruction>(sti->getValueOperand());
                if (!storeVal) continue;

                bool isAnd = storeVal->getOpcode() == Instruction::And;
                bool isOr  = storeVal->getOpcode() == Instruction::Or;
                if (!isAnd && !isOr) continue;

                // Trace ICmp operand to fs2options (source option A)
                string srcKey = traceToFs2Options(
                    isa<Instruction>(icmp->getOperand(0)) ? icmp->getOperand(0) : icmp->getOperand(1),
                    fs2options);
                if (srcKey.empty()) continue;

                // Trace Store destination to fs2options (target option B)
                Value* ptr = sti->getPointerOperand();
                if (auto* BCI = dyn_cast<BitCastInst>(ptr)) ptr = BCI->getOperand(0);
                auto* GEP = dyn_cast<GetElementPtrInst>(ptr);
                if (!GEP) continue;
                if (!GEP->getSourceElementType()->isStructTy() ||
                    !GEP->hasAllConstantIndices() || GEP->getNumIndices() != 2) continue;
                auto* offCI = dyn_cast<ConstantInt>(GEP->getOperand(2));
                if (!offCI) continue;
                string dstKey = GEP->getSourceElementType()->getStructName().str() +
                                to_string(offCI->getZExtValue());
                if (fs2options.find(dstKey) == fs2options.end()) continue;

                auto& srcSet = fs2options[srcKey];
                auto& dstSet = fs2options[dstKey];
                if (srcSet.empty() || dstSet.empty()) continue;

                int optA = srcSet.begin()->second.first;
                int optB = dstSet.begin()->second.first;
                if (optA == optB) continue;

                MountOptCrossDep dep;
                dep.opt_A = optA;
                dep.opt_B = optB;
                dep.opt_A_name = "";
                dep.opt_B_name = "";
                dep.relation = isAnd ? "silent_clear" : "silent_enable";
                dep.src_line = 0;
                deps.cross.push_back(dep);
            }
        }
    }
    } // for funcs
}

// ───────────────────────────────────────────────
// Main entry point
// ───────────────────────────────────────────────
void MountOptDependencyExtractor::extract(
    const string& fsname,
    Function* parseParamsFunc,
    const set<string>& relatedSt,
    map<string, set<pair<pair<uint32_t, string>, pair<int, int>>>>& fs2options,
    map<pair<string, pair<uint32_t, string>>, OneLayerPairSet>& fs2options2onelayer,
    const map<int, pair<string, int>>& flagParams,
    const map<int, pair<string, int>>& intParams,
    map<pair<int, string>, map<int, string>>& enumParams) {

    FsDeps deps;

    // Build checker function set: named checkers from the module + parse function
    set<Function*> checkerFuncs;
    Module* M = parseParamsFunc->getParent();
    for (auto& F : *M) {
        if (CheckerFuncNames.count(F.getName().str()))
            checkerFuncs.insert(&F);
    }
    if (parseParamsFunc && parseParamsFunc->getInstructionCount() > 0)
        checkerFuncs.insert(parseParamsFunc);

    if (!checkerFuncs.empty()) {
        outs() << "  [L2] extracting deps from " << checkerFuncs.size()
               << " functions\n";
        extractSelfDeps(checkerFuncs, flagParams, intParams, enumParams, fs2options, deps);
        extractCrossDeps(checkerFuncs, relatedSt, fs2options, fs2options2onelayer, deps);
        extractSilentDeps(checkerFuncs, fs2options, deps);
    }

    // Merge hardcoded cross-function dependencies
    mergeHardcodedDeps(fsname, deps);

    outs() << "  [L2] found " << deps.self.size() << " self-deps, "
           << deps.cross.size() << " cross-deps for " << fsname << "\n";

    Ctx->fs2deps[fsname] = deps;
}
