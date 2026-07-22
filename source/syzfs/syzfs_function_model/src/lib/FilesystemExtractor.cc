#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include "llvm/IR/Instruction.h"
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <llvm/IR/LegacyPassManager.h>
#include <map> 
#include <vector> 
#include <queue>
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"

#include "FilesystemExtractor.h"
#include "MountOptDependencyExtractor.h"
#include "Config.h"
#include "Common.h"
#include "Utils.h"

using namespace llvm;

std::map<std::string, std::string> comparisonOpposites = {
    {"<", ">="},
    {"<=", ">"},
    {">", "<="},
    {">=", "<"},
    {"=", "!="},
    {"!=", "="}
};

int findExponentOfTwo(uint64_t value) {
    // 检查值是否为0（0不是2的幂）
    if (value == 0) {
        return -1;
    }
    
    // 检查值是否只有一个1位（2的幂的特性）
    if ((value & (value - 1)) != 0) {
        return -1;
    }
    // 通用实现（无编译器特定函数）
    int exponent = 0;
    uint64_t temp = value;
    while (temp > 1) {
        temp >>= 1;
        exponent++;
    }
    return exponent;
    
}

void getAllCaseBBs(set<BasicBlock*>& caseBBs, BasicBlock* caseEntry, set<BasicBlock*>& all_bb, int DefaultIdx)
{
    queue<BasicBlock*> bfsBB;
    bfsBB.push(caseEntry);
    int caseEntryIdx = getBasicBlockIndex(caseEntry);
    while(!bfsBB.empty()) {
        BasicBlock* currBB = bfsBB.front();
        bfsBB.pop();
        caseBBs.insert(currBB);
        Instruction *TI = currBB->getTerminator();
        for (unsigned i = 0, e = TI->getNumSuccessors(); i != e; ++i) {
            BasicBlock* nextBB = TI->getSuccessor(i);
            int nextIdx = getBasicBlockIndex(nextBB);
            if(nextIdx < DefaultIdx && nextIdx > caseEntryIdx && all_bb.find(nextBB) != all_bb.end() && caseBBs.find(nextBB) == caseBBs.end()) {
                bfsBB.push(nextBB);
                all_bb.erase(nextBB);          
            }
        }
    }
}

set<string> FilesystemExtractorPass::BranchCondIsFileType(string srcFileName, BranchInst *BI) {
    set<string> res;
    if (DILocation *Loc = BI->getDebugLoc()) {
        int lineNum = Loc->getLine();
        if (srcFileName != "" && lineNum != 0) {
            if(startsWith(srcFileName, "fs") && Ctx->CaseSrcDir != "") {
                srcFileName = Ctx->CaseSrcDir + "/" + srcFileName;
            }
            ifstream file(srcFileName);
            gotoLine(file, lineNum);
			string line;
			getline(file, line);
			strip(line);
			if (line.size() == 0) {
                return res;
            }
			if(line.find("S_ISLNK") != std::string::npos) {
                res.insert("S_IFLNK");
            }
            if(line.find("S_ISREG") != std::string::npos) {
                res.insert("S_IFREG");
            }
            if(line.find("S_ISDIR") != std::string::npos) {
                res.insert("S_IFDIR");
            }
            if(line.find("S_ISCHR") != std::string::npos) {
                res.insert("S_IFCHR");
            }
            if(line.find("S_ISBLK") != std::string::npos) {
                res.insert("S_IFBLK");
            }
            if(line.find("S_ISFIFO") != std::string::npos) {
                res.insert("S_IFIFO");
            }
            if(line.find("S_ISSOCK") != std::string::npos) {
                res.insert("S_IFSOCK");
            }
        }
    }
    return res;
}

bool FilesystemExtractorPass::SwitchCondIsFileType(string srcFileName, SwitchInst *SWI) {
    if (DILocation *Loc = SWI->getDebugLoc()) {
        int lineNum = Loc->getLine();
        if (srcFileName != "" && lineNum != 0) {
            if(startsWith(srcFileName, "fs") && Ctx->CaseSrcDir != "") {
                srcFileName = Ctx->CaseSrcDir + "/" + srcFileName;
            }
            ifstream file(srcFileName);
            gotoLine(file, lineNum);
			string line;
			getline(file, line);
			strip(line);
			if (line.size() == 0) {
                return false;
            }
			if(line.find("& S_IFMT") != std::string::npos) {
                return true;
            }
        }
    }
    return false;
}

bool FilesystemExtractorPass::MountOptFieldIsOneBit01(string srcFileName, StoreInst *SI) {
    if (DILocation *Loc = SI->getDebugLoc()) {
        int lineNum = Loc->getLine();
        if (srcFileName != "" && lineNum != 0) {
            if(startsWith(srcFileName, "fs") && Ctx->CaseSrcDir != "") {
                srcFileName = Ctx->CaseSrcDir + "/" + srcFileName;
            }
            ifstream file(srcFileName);
            gotoLine(file, lineNum);
			string line;
			getline(file, line);
			strip(line);
			if (line.size() == 0) {
                return false;
            }
			if(endsWith(line, " = 1;") || endsWith(line, " = 0;") || endsWith(line, " = true;") || endsWith(line, " = false;")) {
                return true;
            }
        }
    }
    return false;
}

string FilesystemExtractorPass::MountOptFieldIsOneBitBooleanOrNegated(string srcFileName, StoreInst *SI) {
    outs() << "try to find bit field mount opt in file " << srcFileName << ":" << "\n";
    string res = "";
    if (DILocation *Loc = SI->getDebugLoc()) {
        int lineNum = Loc->getLine();
        if (srcFileName != "" && lineNum != 0) {
            if(startsWith(srcFileName, "fs") && Ctx->CaseSrcDir != "") {
                srcFileName = Ctx->CaseSrcDir + "/" + srcFileName;
            }
            ifstream file(srcFileName);
            gotoLine(file, lineNum);
			string line;
			getline(file, line);
			strip(line);
			if (line.size() == 0) {
                return "";
            }
            outs() << "get line " << lineNum << " in file " << srcFileName << ":" << line << "\n";
			if(endsWith(line, " = !result.negated;") || endsWith(line, " = result.negated;") || endsWith(line, " = result.boolean;") || endsWith(line, " = result.negated ? 0 : 1;") ||  endsWith(line, " = result.negated ? 1 : 0;")) {
                if(endsWith(line, " = !result.negated;")) {
                    res = "!result.negated;";
                }
                else if(endsWith(line, " = result.negated;")) {
                    res = "result.negated;";
                }
                else if(endsWith(line, " = result.boolean;")) {
                    res = "result.boolean;";
                }
                else if (endsWith(line, " = result.negated ? 0 : 1;")) {
                    res = "result.negated ? 0 : 1;";
                }
                else if(endsWith(line, " = result.negated ? 1 : 0;")) {
                    res = "result.negated ? 1 : 0;";
                }
            }
        }
    }
    return res;
}

bool ParseResultIsBoolean(Value* condv) {
    if(TruncInst* trunci = dyn_cast<TruncInst>(condv)) {
        // 1. 获取源操作数 (%31)
        Value *sourceValue = trunci->getOperand(0);
        
        // 3. 获取目标类型 (i1)
        //Type *destType = trunci->getDestTy();
        if(LoadInst* ldi = dyn_cast<LoadInst>(sourceValue)) {
            Value* ldpi = ldi->getPointerOperand();
            if(BitCastInst* bci = dyn_cast<BitCastInst>(ldpi)) {
                Value* bciv = bci->getOperand(0);
                if(GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(bciv)) {
                    Type* CastToTy = bci->getDestTy();
                    if(CastToTy->isPointerTy()) {
                        CastToTy = CastToTy->getPointerElementType();
                    }
                    Type *GepTy = gepi->getPointerOperand()->getType()->getPointerElementType();
                    if(IntegerType *intType = dyn_cast<IntegerType>(CastToTy)) {
                        if (intType->getBitWidth() == 8) {
                            if(GepTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2) {
                                auto offsetVal = gepi->getOperand(2);
                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                int offsetinst = offsetInt->getZExtValue();
                                if(offsetinst == 1) {
                                    if(GepTy->getStructName().str() == "struct.fs_parse_result") {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return false;
}

bool ParseResultIsInteger(Value* storev) {
    Value* ldv = nullptr;
    if(TruncInst* trunci = dyn_cast<TruncInst>(storev)) {
        ldv = trunci->getOperand(0);
    } else if(ZExtInst* zexti = dyn_cast<ZExtInst>(storev)) {
        ldv = zexti->getOperand(0);
    } else {
        ldv = storev;
    }
    if(LoadInst* ldi = dyn_cast<LoadInst>(ldv)) {
        Value* ldpi = ldi->getPointerOperand();
        if(BitCastInst* bci = dyn_cast<BitCastInst>(ldpi)) {
            Value* bciv = bci->getOperand(0);
            if(GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(bciv)) {
                Type* CastToTy = bci->getDestTy();
                if(CastToTy->isPointerTy()) {
                    CastToTy = CastToTy->getPointerElementType();
                }
                Type *GepTy = gepi->getPointerOperand()->getType()->getPointerElementType();
                if(IntegerType *intType = dyn_cast<IntegerType>(CastToTy)) {
                    if (intType->getBitWidth() == 32 || intType->getBitWidth() == 64) {
                        if(GepTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2) {
                            auto offsetVal = gepi->getOperand(2);
                            auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                            int offsetinst = offsetInt->getZExtValue();
                            if(offsetinst == 1) {
                                if(GepTy->getStructName().str() == "struct.fs_parse_result") {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return false;
}

string getFilesystemNameString(Value *currVal) {
    const GEPOperator *gep = dyn_cast<GEPOperator>(currVal);
    const llvm::GlobalVariable *strGlobal = nullptr;
    if(gep != nullptr) {
        strGlobal = dyn_cast<GlobalVariable>(gep->getPointerOperand());
    }
    if (strGlobal != nullptr && strGlobal->hasInitializer()) {
        const Constant *currConst = strGlobal->getInitializer();
        const ConstantDataArray *currDArray = dyn_cast<ConstantDataArray>(currConst);
        string res = "";
        raw_string_ostream ss(res);
        if(currDArray != nullptr) {
            ss << currDArray->getAsCString();
        } else {
            ss << *currConst;
        }
        return ss.str();
    }
    return "?";
}

// ───────────────────────────────────────────────
// strcmp-based enum chain detection for old API (f2fs match_token)
// ───────────────────────────────────────────────

static bool isStrcmpCall(CallInst* CI) {
    Function* F = CI->getCalledFunction();
    if (!F) return false;
    StringRef name = F->getName();
    return name.endswith("strcmp") || name.endswith("strncmp");
}

static std::string extractStringFromStrcmp(CallInst* strcmpCall) {
    for (int i = 0; i < (int)strcmpCall->arg_size(); i++) {
        Value* arg = strcmpCall->getOperand(i);
        if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(arg)) {
            if (GlobalVariable* gv = dyn_cast<GlobalVariable>(gep->getPointerOperand())) {
                if (gv->hasInitializer()) {
                    if (ConstantDataArray* cda = dyn_cast<ConstantDataArray>(gv->getInitializer())) {
                        std::string s = cda->getAsString().str();
                        if (!s.empty() && s.back() == '\0')
                            s.pop_back();
                        return s;
                    }
                }
            }
        }
    }
    return "";
}

static std::pair<int, bool> findStoreConstantToStruct(
    BasicBlock* BB, StructType* /*targetTy unused*/,
    std::string& outStructField, int& outEnumVal) {
    for (auto& I : *BB) {
        if (StoreInst* sti = dyn_cast<StoreInst>(&I)) {
            if (ConstantInt* ci = dyn_cast<ConstantInt>(sti->getValueOperand())) {
                Value* ptr = sti->getPointerOperand();
                if (BitCastInst* bci = dyn_cast<BitCastInst>(ptr))
                    ptr = bci->getOperand(0);
                if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(ptr)) {
                    Type* gepTy = gep->getPointerOperand()->getType()->getPointerElementType();
                    if (gepTy->isStructTy() && gep->hasAllConstantIndices() && gep->getNumIndices() == 2) {
                        ConstantInt* offCI = dyn_cast<ConstantInt>(gep->getOperand(2));
                        if (!offCI) continue;
                        int offset = offCI->getZExtValue();
                        outStructField = gepTy->getStructName().str() + std::to_string(offset);
                        outEnumVal = ci->getZExtValue();
                        return {outEnumVal, true};
                    }
                }
            }
        }
    }
    return {0, false};
}

static bool isStrcmpBranch(BranchInst* bi) {
    if (!bi->isConditional()) return false;
    Value* cond = bi->getCondition();
    ICmpInst* icmp = dyn_cast<ICmpInst>(cond);
    if (!icmp || icmp->getPredicate() != ICmpInst::ICMP_EQ) return false;
    ConstantInt* ci = nullptr;
    Value* other = nullptr;
    if ((ci = dyn_cast<ConstantInt>(icmp->getOperand(0)))) other = icmp->getOperand(1);
    else if ((ci = dyn_cast<ConstantInt>(icmp->getOperand(1)))) other = icmp->getOperand(0);
    if (!ci || !ci->isZero()) return false;
    CallInst* call = dyn_cast<CallInst>(other);
    return call && isStrcmpCall(call);
}

static void traceStrcmpEnumChain(
    BranchInst* firstBr,
    int cmd_value,
    std::map<std::string, std::set<std::pair<std::pair<uint32_t, std::string>, std::pair<int,int>>>>& res,
    std::map<int, std::map<int, std::string>>& enumCollect) {

    BranchInst* currBr = firstBr;
    int depth = 0;
    const int MAX_DEPTH = 20;

    while (currBr && depth < MAX_DEPTH) {
        depth++;
        ICmpInst* icmp = dyn_cast<ICmpInst>(currBr->getCondition());
        if (!icmp) break;

        CallInst* strcmpCall = nullptr;
        if (isa<CallInst>(icmp->getOperand(0)))
            strcmpCall = cast<CallInst>(icmp->getOperand(0));
        else if (isa<CallInst>(icmp->getOperand(1)))
            strcmpCall = cast<CallInst>(icmp->getOperand(1));
        if (!strcmpCall) break;

        std::string enumStr = extractStringFromStrcmp(strcmpCall);
        if (enumStr.empty()) break;

        BasicBlock* trueBB = currBr->getSuccessor(0);
        BasicBlock* falseBB = currBr->getSuccessor(1);

        // Heuristic: ensure trueBB is the "match" path (has store, not strcmp)
        BranchInst* falseBr = nullptr;
        for (auto& I : *falseBB)
            if ((falseBr = dyn_cast<BranchInst>(&I))) break;
        if (falseBr && isStrcmpBranch(falseBr))
            ; // orientation OK
        else if (falseBr && !isStrcmpBranch(falseBr)) {
            BranchInst* trueBrCheck = nullptr;
            for (auto& I : *trueBB)
                if ((trueBrCheck = dyn_cast<BranchInst>(&I))) break;
            if (isStrcmpBranch(trueBrCheck))
                std::swap(trueBB, falseBB);
        }

        std::string fieldKey;
        int enumVal = 0;
        auto found = findStoreConstantToStruct(trueBB, nullptr, fieldKey, enumVal);
        if (found.second) {
            res[fieldKey].insert(std::make_pair(
                std::make_pair((uint32_t)0xffffffff, std::string("assignenum")),
                std::make_pair(cmd_value, -1)));
            enumCollect[cmd_value][(int)enumVal] = enumStr;
        }

        BranchInst* nextBr = nullptr;
        for (auto& I : *falseBB)
            if ((nextBr = dyn_cast<BranchInst>(&I))) break;
        if (nextBr && isStrcmpBranch(nextBr))
            currBr = nextBr;
        else
            break;
    }
}

static BranchInst* firstBrOfBB(BasicBlock* BB) {
    for (auto& I : *BB) {
        if (BranchInst* bi = dyn_cast<BranchInst>(&I))
            return bi;
    }
    return nullptr;
}

GlobalVariable* FilesystemExtractorPass::getGlobalVaraible(StringRef varName)
{
    GlobalVariable* globalVar = nullptr;
    for(pair<Module*, StringRef> item : Ctx->Modules)
    {
        Module* M = item.first;
        GlobalVariable* tmp = M->getGlobalVariable(varName);
        if(tmp != nullptr && tmp->hasInitializer())
        {
            globalVar = tmp;
            break;
        }
    }
    return globalVar;
}

Function* FilesystemExtractorPass::getFunctionFromModules(StringRef funcName)
{
   Function* func = nullptr; 
   for(pair<Module*, StringRef> item : Ctx->Modules)
    {
        Module* M = item.first;
        Function* tmp = M->getFunction(funcName);
        if(tmp != nullptr && !tmp->isDeclaration() && tmp->getInstructionCount() > 0)
        {
            func = tmp;
            break;
        }
    }
    return func;
}

set<Instruction*> FilesystemExtractorPass::TryGetMountOptInIfCall(CallInst* ifCall) {
    set<Instruction*> res;
    Function *callee = ifCall->getCalledFunction();
    if(callee == nullptr)
    {
        callee = dyn_cast<Function>(ifCall->getCalledOperand()->stripPointerCasts());
    }
    if(callee == nullptr) return res;
    if(callee->isIntrinsic()) return res;
    if(callee->getInstructionCount() == 0)
    {
        callee = getFunctionFromModules(callee->getName());
    }
    if(callee == nullptr) return res;
    if(callee->getInstructionCount() == 0) return res;

    BasicBlock* firstBB = &callee->getEntryBlock();
    Instruction* termi = firstBB->getTerminator();
    if(termi->getOpcode() == llvm::Instruction::Ret) {
        if(termi->getNumOperands() == 0) return res;
        Value* retv = termi->getOperand(0);
        if(!dyn_cast<Instruction>(retv)) return res;
        Instruction* reti = dyn_cast<Instruction>(retv);
        res.insert(reti);
    } else {
        BasicBlock* lastBB = &callee->back();
        Instruction* termli = lastBB->getTerminator();
        if(termli->getOpcode() == llvm::Instruction::Ret) {
            if(termli->getNumOperands() == 0) return res;
            Value* retlv = termli->getOperand(0);
            if(!dyn_cast<Instruction>(retlv)) return res;
            Instruction* retli = dyn_cast<Instruction>(retlv);
            if (auto* phiInst = dyn_cast<PHINode>(retli)) {
                unsigned numIncoming = phiInst->getNumIncomingValues();
                for (unsigned i = 0; i < numIncoming; i++) {
                    BasicBlock* predecessor = phiInst->getIncomingBlock(i);
                    //Value* incomingValue = phiInst->getIncomingValue(i);
                    Instruction* predi = predecessor->getTerminator();
                    if(BranchInst* predbr = dyn_cast<BranchInst>(predi)) {
                        if(predbr->getNumSuccessors() != 2 || predbr->isUnconditional()) continue;
                        Instruction* bri = dyn_cast<Instruction>(predbr->getCondition());
                        if(bri) res.insert(bri);
                    }
                }
            }
        }
    }
    return res;
}

#define MAX_DEPTH_FIND_OPERATIONS 5

void FilesystemExtractorPass::getFileOperationsFromFillSuper(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, unsigned depth)
{

    if(visited.count(F))
    {
        return;
    }
    if(depth > MAX_DEPTH_FIND_OPERATIONS)
        return;
    visited.insert(F);
    if(F->getName() == "inode_init_always")
        return;
    outs() << "getFileOperationsFromFillSuper: " << F->getName() << "\n";
    for(inst_iterator iter = inst_begin(F); iter != inst_end(F); iter++)
    {
        Instruction* I = &*iter;
        if(I->getOpcode() == Instruction::Call)
        {
            CallInst* callInst = dyn_cast<CallInst>(I);
            if(Ctx->Callees[callInst].size() > 1)
                continue;
            for(Function* callee:Ctx->Callees[callInst])
            {
                getFileOperationsFromFillSuper(callee, filesystemInfoItem, visited, depth+1);
            }
        }
        else if(I->getOpcode() == Instruction::GetElementPtr)
        {
            GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(I);
            if(!gepInst->getSourceElementType()->isStructTy())
            {
                continue;
            }
            if(gepInst->getSourceElementType()->getStructName() == "struct.inode")
            {
                Type* gepPointerType = nullptr;
                Instruction *gepNext = getNextInstruction(I);
                Instruction *nearStore = I;
                if(!gepInst->getResultElementType()->isPointerTy())
                {
                    if(!gepNext || !dyn_cast<BitCastInst>(gepNext)) {
                        continue;
                    } else {
                        if(gepNext->getOperand(0) != gepInst) {
                            continue;
                        }
                        nearStore = gepNext;
                    }
                }
                if(!gepInst->getResultElementType()->isPointerTy()) {
                    if(gepNext && dyn_cast<BitCastInst>(gepNext)) {
                        BitCastInst* bci = dyn_cast<BitCastInst>(gepNext);
                        gepPointerType = bci->getDestTy();
                        while (gepPointerType->isPointerTy()) {
                            gepPointerType = gepPointerType->getPointerElementType();
                        }
                        if (!gepPointerType->isStructTy()) {
                            gepPointerType = nullptr;
                        }
                    }
                }
                else {
                    gepPointerType = gepInst->getResultElementType()->getPointerElementType();
                    if(!gepPointerType->isStructTy())
                    {
                        gepPointerType = nullptr;
                    }
                }
                if(gepPointerType && gepPointerType->getStructName() == "struct.file_operations")
                {
                    for(User* user:nearStore->users())
                    {
                        if(StoreInst* storeInst = dyn_cast<StoreInst>(user))
                        {
                            Value* op = storeInst->getValueOperand();
                            GlobalVariable* globalVar = dyn_cast<GlobalVariable>(op);
                            if(globalVar == nullptr)
                            {
                                if(BitCastOperator* bitcastOp = dyn_cast<BitCastOperator>(op))
                                {
                                    globalVar = dyn_cast<GlobalVariable>(bitcastOp->getOperand(0));
                                }
                            }
                            if(globalVar != nullptr)
                            {
                                if(!globalVar->hasInitializer())
                                {
                                    globalVar = getGlobalVaraible(globalVar->getName());
                                }
                            }
                            if(globalVar != nullptr)
                            {
                                bool flag = false;
                                for(GlobalVariable* gv:filesystemInfoItem->fileOperations)
                                {
                                    if(gv->getName() == globalVar->getName())
                                    {
                                        flag = true;
                                        break;
                                    }
                                }
                                if(flag)
                                    continue;
                                filesystemInfoItem->fileOperations.push_back(globalVar);
                                Ctx->Fs2InodeInitFuncs[filesystemInfoItem->name].insert(F);

                            }
                        }
                    }
                }
            }
        }
    }
}

#define MAX_DEPTH_FIND_OLD_PARSE_MOUNT_OPT 5

void FilesystemExtractorPass::getOldParseMountOptionsFromFillSuper(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, CallInst* UpperCall, unsigned depth)
{

    if(visited.count(F))
    {
        return;
    }
    if(depth > MAX_DEPTH_FIND_OLD_PARSE_MOUNT_OPT)
        return;
    visited.insert(F);
    if(F->getName() == "inode_init_always")
        return;
    outs() << "getOldParseMountOptionsFromFillSuper: " << F->getName() << "\n";
    for(inst_iterator iter = inst_begin(F); iter != inst_end(F); iter++)
    {
        Instruction* I = &*iter;
        if(I->getOpcode() == Instruction::Call)
        {
            CallInst* callInst = dyn_cast<CallInst>(I);
            if(Ctx->Callees[callInst].size() > 1)
                continue;
            Function* calledF = callInst->getCalledFunction();
            if(calledF && calledF->hasName()) {
                string calledFname = calledF->getName().str();
                if(calledFname == "match_token") {
                    Ctx->Fs2OldParseMountOptionsFuncs[filesystemInfoItem->name].insert(std::make_pair(F, UpperCall));
                    continue;
                }
            }
            for(Function* callee:Ctx->Callees[callInst])
            {
                getOldParseMountOptionsFromFillSuper(callee, filesystemInfoItem, visited, callInst, depth+1);
            }
        }
    }
}

set<Function*> FilesystemExtractorPass::findGetTreeFromInitFsCtx(Function* initFsCtx, set<GlobalVariable*>& fsctxoper)
{
    set<Function*> res;
    Value* targetOp = nullptr;
    set<Value*> targetOps;
    for(inst_iterator iter = inst_begin(initFsCtx); iter != inst_end(initFsCtx); iter++)
    {
        Instruction* I = &*iter;
        if(I->getOpcode() == Instruction::GetElementPtr)
        {
            GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(I);
            if(!gepInst->getSourceElementType()->isStructTy())
            {
                continue;
            }
            if(gepInst->getSourceElementType()->getStructName() == "struct.fs_context")
            {
                if(!gepInst->getResultElementType()->isPointerTy())
                {
                    continue;
                }
                if(!gepInst->getResultElementType()->getPointerElementType()->isStructTy())
                    continue;
                if(gepInst->getResultElementType()->getPointerElementType()->getStructName() == "struct.fs_context_operations")
                {
                    for(User* user:gepInst->users())
                    {
                        if(StoreInst* storeInst = dyn_cast<StoreInst>(user))
                        {
                            targetOp = storeInst->getValueOperand();
                            break;
                        }
                    }
                }

            }
        }
        if(targetOp != nullptr) {
            targetOps.insert(targetOp);
            targetOp = nullptr;
            //break;
        }
    }
    if(!targetOps.empty())
    {
        for(auto& top : targetOps) {
            targetOp = top;
            GlobalVariable* globalVar = dyn_cast<GlobalVariable>(targetOp);
            if(globalVar == nullptr)
            {
                if(BitCastOperator* bitcastOp = dyn_cast<BitCastOperator>(targetOp))
                {
                    globalVar = dyn_cast<GlobalVariable>(bitcastOp->getOperand(0));
                }
            }
            if(globalVar != nullptr)
            {
                if(!globalVar->hasInitializer())
                {
                    globalVar = getGlobalVaraible(globalVar->getName());
                }
            }
            if(globalVar != nullptr)
            {
                fsctxoper.insert(globalVar);
                ConstantStruct* constStruct = dyn_cast<ConstantStruct>(globalVar->getInitializer());
                Constant* getTreeFuncPtr = constStruct->getOperand(Ctx->StructFieldIdx["fs_context_operations"]["get_tree"]);
                if(!getTreeFuncPtr->isNullValue())
                {
                    Function* getTree = dyn_cast<Function>(getTreeFuncPtr);
                    if(getTree->getInstructionCount() == 0)
                        getTree = getFunctionFromModules(getTree->getName());
                    if(getTree != nullptr)
                        res.insert(getTree);
                }
            }
        }
    }
    return res;
}

void FilesystemExtractorPass::getFileOperationsFromEntry(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, unsigned depth)
{
    if(visited.count(F))
    {
        return;
    }
    if(depth > MAX_DEPTH_FIND_OPERATIONS)
        return;
    visited.insert(F);
    if(F->getName() == "inode_init_always" || F->getName() == "init_specail_inode")
        return;
    for(inst_iterator iter = inst_begin(F); iter != inst_end(F); iter++)
    {
        Instruction* I = &*iter;
        if(I->getOpcode() == Instruction::Call)
        {
            CallInst* callInst = dyn_cast<CallInst>(I);
            if(Ctx->Callees[callInst].size() > 1)
                continue;
            
            for(Function* callee:Ctx->Callees[callInst])
            {
                if(!callee->isVarArg())
                {
                    for(Value* arg: callInst->args())
                    {
                        if(Function* calledBack = dyn_cast<Function>(arg))
                        {
                            if(calledBack->getInstructionCount() == 0)
                                calledBack = getFunctionFromModules(calledBack->getName());
                            if(calledBack != nullptr)
                            {
                                getFileOperationsFromEntry(calledBack, filesystemInfoItem, visited, depth+1);
                            }
                        }
                    }
                }
                getFileOperationsFromEntry(callee, filesystemInfoItem, visited, depth+1);
            }
             
        }
        else if(I->getOpcode() == Instruction::GetElementPtr)
        {
            GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(I);
            Instruction *gepNext = getNextInstruction(I);
            if(!gepInst->getSourceElementType()->isStructTy())
            {
                continue;
            }
            if(gepInst->getSourceElementType()->getStructName() == "struct.inode")
            {
                Type* gepPointerType = nullptr;
                Instruction *gepNext = getNextInstruction(I);
                Instruction *nearStore = I;
                if(!gepInst->getResultElementType()->isPointerTy())
                {
                    if(!gepNext || !dyn_cast<BitCastInst>(gepNext)) {
                        continue;
                    } else {
                        if(gepNext->getOperand(0) != gepInst) {
                            continue;
                        }
                        nearStore = gepNext;
                    }
                }
                if(!gepInst->getResultElementType()->isPointerTy()) {
                    if(gepNext && dyn_cast<BitCastInst>(gepNext)) {
                        BitCastInst* bci = dyn_cast<BitCastInst>(gepNext);
                        gepPointerType = bci->getDestTy();
                        while (gepPointerType->isPointerTy()) {
                            gepPointerType = gepPointerType->getPointerElementType();
                        }
                        if (!gepPointerType->isStructTy()) {
                            gepPointerType = nullptr;
                        }
                    }
                }
                else {
                    gepPointerType = gepInst->getResultElementType()->getPointerElementType();
                    if(!gepPointerType->isStructTy())
                    {
                        gepPointerType = nullptr;
                    }
                }

                if(gepPointerType && gepPointerType->getStructName() == "struct.file_operations")
                {
                    for(User* user:nearStore->users())
                    {
                        if(StoreInst* storeInst = dyn_cast<StoreInst>(user))
                        {
                            Value* op = storeInst->getValueOperand();
                            GlobalVariable* globalVar = dyn_cast<GlobalVariable>(op);
                            if(globalVar == nullptr)
                            {
                                if(BitCastOperator* bitcastOp = dyn_cast<BitCastOperator>(op))
                                {
                                    globalVar = dyn_cast<GlobalVariable>(bitcastOp->getOperand(0));
                                }
                            }
                            if(globalVar != nullptr)
                            {
                                if(!globalVar->hasInitializer())
                                {
                                    globalVar = getGlobalVaraible(globalVar->getName());
                                }
                            }
                            if(globalVar != nullptr)
                            {
                                bool flag = false;
                                for(GlobalVariable* gv:filesystemInfoItem->fileOperations)
                                {
                                    if(gv->getName() == globalVar->getName())
                                    {
                                        flag = true;
                                        break;
                                    }
                                }
                                if(flag)
                                    continue;
                                filesystemInfoItem->fileOperations.push_back(globalVar);
                                Ctx->Fs2InodeInitFuncs[filesystemInfoItem->name].insert(F);
                            }
                        }
                    }
                }
            }
        }
    }
}

void FilesystemExtractorPass::getOldParseMountOptionsFromEntry(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, CallInst* UpperCall, unsigned depth)
{
    if(visited.count(F))
    {
        return;
    }
    if(depth > MAX_DEPTH_FIND_OLD_PARSE_MOUNT_OPT)
        return;
    visited.insert(F);
    if(F->getName() == "inode_init_always" || F->getName() == "init_specail_inode")
        return;
    for(inst_iterator iter = inst_begin(F); iter != inst_end(F); iter++)
    {
        Instruction* I = &*iter;
        if(I->getOpcode() == Instruction::Call)
        {
            CallInst* callInst = dyn_cast<CallInst>(I);
            if(Ctx->Callees[callInst].size() > 1)
                continue;

            Function* calledF = callInst->getCalledFunction();
            if(calledF && calledF->hasName()) {
                string calledFname = calledF->getName().str();
                if(calledFname == "match_token") {
                    Ctx->Fs2OldParseMountOptionsFuncs[filesystemInfoItem->name].insert(std::make_pair(F, UpperCall));
                    continue;
                }
            }
            for(Function* callee:Ctx->Callees[callInst])
            {
                if(!callee->isVarArg())
                {
                    for(Value* arg: callInst->args())
                    {
                        if(Function* calledBack = dyn_cast<Function>(arg))
                        {
                            if(calledBack->getInstructionCount() == 0)
                                calledBack = getFunctionFromModules(calledBack->getName());
                            if(calledBack != nullptr)
                            {
                                getOldParseMountOptionsFromEntry(calledBack, filesystemInfoItem, visited, nullptr, depth+1);
                            }
                        }
                    }
                }
                getOldParseMountOptionsFromEntry(callee, filesystemInfoItem, visited, callInst, depth+1);
            }
        }
    }
}

std::map<std::string, uint> PassGetTreeWrapper = {
    {"get_tree_keyed", 1},
    {"get_tree_single", 1},
    {"get_tree_nodev", 1},
    {"get_tree_bdev", 1},
    {"get_tree_mtd", 1},
};

std::map<uint, std::string> FileTypeConstToString = {
 {0140000, "S_IFSOCK"},
 {0120000, "S_IFLNK"},
 {0100000, "S_IFREG"},
 {0060000, "S_IFBLK"},
 {0040000, "S_IFDIR"},
 {0020000, "S_IFCHR"},
 {0010000, "S_IFIFO"},
 {0004000, "S_ISUID"},
 {0002000, "S_ISGID"},
 {0001000, "S_ISVTX"},
};

void FilesystemExtractorPass::TryGetAnotherExt4FillSuper(Function* ext4fillsuper, FilesystemInfoItem* filesystemInfoItem) {
    for (inst_iterator i = inst_begin(ext4fillsuper), e = inst_end(ext4fillsuper); i != e; ++i) {
		Instruction *I = &*i;
        if(CallInst* calli = dyn_cast<CallInst>(I)) {
            Function *callee = calli->getCalledFunction();
            if(callee == nullptr)
            {
                callee = dyn_cast<Function>(calli->getCalledOperand()->stripPointerCasts());
            }
            if(callee == nullptr) continue;
            if(callee->isIntrinsic()) continue;
            if(!callee->hasName()) continue;
            string funcname = callee->getName().str();
            if(!endsWith(funcname, "ext4_fill_super")) continue;
            if(callee->getInstructionCount() == 0)
            {
                callee = getFunctionFromModules(callee->getName());
            }
            if(callee == nullptr) continue;
            if(callee->getInstructionCount() == 0) continue;
            filesystemInfoItem->SyscallHandler.push_back(make_pair("mount", callee));
        }
    }
}

Function* FilesystemExtractorPass::TryGetActualInitFs(Function* initfsctx) {
    Function* res = nullptr;
    string initfsctxname = initfsctx->getName().str();
    for (inst_iterator i = inst_begin(initfsctx), e = inst_end(initfsctx); i != e; ++i) {
		Instruction *I = &*i;
        if(CallInst* calli = dyn_cast<CallInst>(I)) {
            Function *callee = calli->getCalledFunction();
            if(callee == nullptr)
            {
                callee = dyn_cast<Function>(calli->getCalledOperand()->stripPointerCasts());
            }
            if(callee == nullptr) continue;
            if(callee->isIntrinsic()) continue;
            if(!callee->hasName()) continue;
            string funcname = callee->getName().str();
            if(!endsWith(funcname, initfsctxname)) continue;
            if(callee->getInstructionCount() == 0)
            {
                callee = getFunctionFromModules(callee->getName());
            }
            if(callee == nullptr) continue;
            if(callee->getInstructionCount() == 0) continue;
            res = callee;
        }
    }
    return res;
}

void FilesystemExtractorPass::HandleFsTypeStruct(GlobalVariable* globalVar, FilesystemInfoItem* filesystemInfoItem, set<GlobalVariable*>& fsctxoper)
{
    ConstantStruct* constStruct = dyn_cast<ConstantStruct>(globalVar->getInitializer());
    outs() << "[+] global variable defination: " << *globalVar << "\n";
    outs() << "[+] type: " << globalVar->getValueType()->getStructName() << "\n";
    // constStruct->ge
    Constant* filesystemNameVal = constStruct->getOperand(Ctx->StructFieldIdx["file_system_type"]["name"]);
    string filesystemName = getFilesystemNameString(filesystemNameVal);
    outs() << "str: " << filesystemName << "\n";
    filesystemInfoItem->name = filesystemName;
    filesystemInfoItem->filesystemTypeStruct = globalVar;
    Constant* mountFuncPtr = constStruct->getOperand(Ctx->StructFieldIdx["file_system_type"]["mount"]);
    Constant* initfsctxFuncPtr = constStruct->getOperand(Ctx->StructFieldIdx["file_system_type"]["init_fs_context"]);
    if(!mountFuncPtr->isNullValue())
    {
        Function* mountFunc = dyn_cast<Function>(mountFuncPtr);
        if(mountFunc->getInstructionCount() == 0)
        {
            mountFunc = getFunctionFromModules(mountFunc->getName());
        }
        if(mountFunc->getInstructionCount() != 0)
        {
            Function* fillSuperFunc = nullptr;
            for(inst_iterator iter = inst_begin(mountFunc); iter != inst_end(mountFunc); iter++)
            {
                Instruction* I = &*iter;
                if(I->getOpcode() == Instruction::Call)
                {
                    CallInst* callInst = dyn_cast<CallInst>(I);
                    if(callInst->getCalledFunction() != nullptr && callInst->getCalledFunction()->getName() == "mount_bdev")
                    {
                        fillSuperFunc = dyn_cast<Function>(callInst->getArgOperand(4));
                        outs() << "fill super func: " << fillSuperFunc->getName() << "\n";
                        break;
                    }
                    else if(callInst->getCalledFunction() != nullptr && callInst->getCalledFunction()->getName() == "mount_nodev")
                    {
                        fillSuperFunc = dyn_cast<Function>(callInst->getArgOperand(3));
                        outs() << "fill super func: " << fillSuperFunc->getName() << "\n";
                        break;
                    }
                    else if(callInst->getCalledFunction() != nullptr && callInst->getCalledFunction()->getName() == "mount_single")
                    {
                        fillSuperFunc = dyn_cast<Function>(callInst->getArgOperand(3));
                        outs() << "fill super func: " << fillSuperFunc->getName() << "\n";
                        break;
                    }
                }
            }
            if(fillSuperFunc != nullptr)
            {
                if(fillSuperFunc->getInstructionCount() == 0)
                {
                    fillSuperFunc = getFunctionFromModules(fillSuperFunc->getName());
                }
                if(fillSuperFunc->getInstructionCount() != 0) {
                    set<Function*> visited;
                    set<Function*> visited2;
                    getFileOperationsFromFillSuper(fillSuperFunc, filesystemInfoItem, visited, 1); 
                    getOldParseMountOptionsFromFillSuper(fillSuperFunc, filesystemInfoItem, visited2, nullptr, 1);
                    filesystemInfoItem->SyscallHandler.push_back(make_pair("mount", fillSuperFunc));
                    if(fillSuperFunc->getName().str() == "ext4_fill_super") {
                        TryGetAnotherExt4FillSuper(fillSuperFunc, filesystemInfoItem);
                    }
                    if(filesystemInfoItem->fileOperations.size() == 0) {
                        getFileOperationsFromFillSuper(mountFunc, filesystemInfoItem, visited, 0);
                    }
                    if(Ctx->Fs2OldParseMountOptionsFuncs[filesystemInfoItem->name].size() == 0) {
                        getOldParseMountOptionsFromFillSuper(mountFunc, filesystemInfoItem, visited2, nullptr, 0);
                    }
                }
            }
            else
            {
                set<Function*> visited;
                set<Function*> visited2;
                getFileOperationsFromFillSuper(mountFunc, filesystemInfoItem, visited, 0); 
                getOldParseMountOptionsFromFillSuper(mountFunc, filesystemInfoItem, visited2, nullptr, 0);
                filesystemInfoItem->SyscallHandler.push_back(make_pair("mount", mountFunc));
            }
        }
    }
    if(!initfsctxFuncPtr->isNullValue())
    {
        Function* initfsctxFunc = dyn_cast<Function>(initfsctxFuncPtr);
        if(initfsctxFunc->getInstructionCount() == 0)
            initfsctxFunc = getFunctionFromModules(initfsctxFunc->getName());
        if(initfsctxFunc != nullptr)
        {
            set<Function*> getTrees = findGetTreeFromInitFsCtx(initfsctxFunc, fsctxoper);
            if (getTrees.empty()) {
                Function* initfsctxFunctmp = TryGetActualInitFs(initfsctxFunc);
                if(!initfsctxFunctmp) {
                    return;
                }
                else {
                    getTrees = findGetTreeFromInitFsCtx(initfsctxFunctmp, fsctxoper);
                    if(getTrees.empty()) {
                        return;
                    }
                }
            }
            for(auto& gt : getTrees) {
                Function* getTree = gt;
                Function* fillSuperFunc = nullptr;
                for (auto iter = inst_begin(getTree); iter != inst_end(getTree); iter++) {
                    Instruction* I = &*iter; 
                    if (I->getOpcode() != Instruction::Call) {
                        continue;
                    }
                    CallInst* callInst = dyn_cast<CallInst>(I);
                    Function* calledFunc = callInst->getCalledFunction();
                    if (calledFunc == nullptr) {
                        continue;
                    }
                    auto res = PassGetTreeWrapper.find(calledFunc->getName().str());
                    if (res != PassGetTreeWrapper.end()) {
                        fillSuperFunc = dyn_cast<Function>(callInst->getArgOperand((*res).second));
                        outs() << "fill super func (from initFsCtx): " << fillSuperFunc->getName() << "\n"; 
                        if (fillSuperFunc->getInstructionCount() == 0) {
                            fillSuperFunc = getFunctionFromModules(fillSuperFunc->getName());
                        }
                        if (fillSuperFunc->getInstructionCount() != 0) {
                            filesystemInfoItem->SyscallHandler.push_back(make_pair("mount", fillSuperFunc));
                            if(fillSuperFunc->getName().str() == "ext4_fill_super") {
                                TryGetAnotherExt4FillSuper(fillSuperFunc, filesystemInfoItem);
                            }
                        }
                    }
                    break;
                }
                set<Function*> visited;
                set<Function*> visited2;
                getFileOperationsFromEntry(getTree, filesystemInfoItem, visited, 0);
                getOldParseMountOptionsFromEntry(getTree, filesystemInfoItem, visited2, nullptr, 0);
            }
        }
    }
}


set<string> FilesystemExtractorPass::getOldFsParamsNames(Function* parseF) {
    set<string> res;
    for (inst_iterator i = inst_begin(parseF), e = inst_end(parseF); 
            i != e; ++i) {
        if (CallInst *CI = dyn_cast<CallInst>(&*i)) {

            auto getCalledF=CI->getCalledFunction();
            if (getCalledF && endsWith(getCalledF->getName().str(), "match_token") && CI->getNumOperands()==4){
                    
                if(ConstantExpr* fsparams_desc=dyn_cast<ConstantExpr>(CI->getOperand(1))){
                    if(GetElementPtrInst* GEP=dyn_cast<GetElementPtrInst>(fsparams_desc->getAsInstruction())){
                        if(GlobalVariable* GBV=dyn_cast<GlobalVariable>(GEP->getPointerOperand())){
                            if(GBV->hasName()) {
                                res.insert(GBV->getName().str());
                            }
                        }
                    }
                }
            }
        }
    }
    return res;
}

set<string> FilesystemExtractorPass::getFsParamsNames(Function* parseF) {
    set<string> res;
    for (inst_iterator i = inst_begin(parseF), e = inst_end(parseF); 
            i != e; ++i) {
        if (CallInst *CI = dyn_cast<CallInst>(&*i)) {

            auto getCalledF=CI->getCalledFunction();
            if (getCalledF && endsWith(getCalledF->getName().str(), "fs_parse") && CI->getNumOperands()==5){
                    
                if(ConstantExpr* fsparams_desc=dyn_cast<ConstantExpr>(CI->getOperand(1))){
                    if(GetElementPtrInst* GEP=dyn_cast<GetElementPtrInst>(fsparams_desc->getAsInstruction())){
                        if(GlobalVariable* GBV=dyn_cast<GlobalVariable>(GEP->getPointerOperand())){
                            if(GBV->hasName()) {
                                res.insert(GBV->getName().str());
                            }
                        }
                    }
                }
            }
        }
    }
    return res;
}

vector<GlobalVariable*> FilesystemExtractorPass::getFsOldParams(Module* M, set<string> paramsname) {
    vector<GlobalVariable*> res;
    for(auto gv = M->global_begin(); gv != M->global_end(); gv++) 
    {
        GlobalVariable* globalVar = &(*gv);
        if(globalVar == nullptr) {
            continue;
        }
        if(globalVar->getValueType()->isArrayTy())
        {
            if(!globalVar->hasName()) continue;
            string ArName = globalVar->getName().str();
            if(paramsname.find(ArName) == paramsname.end()) continue;
            auto ArTy = globalVar->getValueType();
            auto elemType = ArTy->getArrayElementType();
            int elemNum = ArTy->getArrayNumElements();
            if(elemNum == 0) continue;
            
            if(elemType->isStructTy())
            {
                string elemTyName = elemType->getStructName().str();
                {
                    if(elemTyName == "struct.match_token") {
                        res.push_back(globalVar);
                        //return globalVar;
                    }
                }
            }
        }
    }
    return res;
}

vector<GlobalVariable*> FilesystemExtractorPass::getFsParams(Module* M, set<string> paramsname) {
    vector<GlobalVariable*> res;
    for(auto gv = M->global_begin(); gv != M->global_end(); gv++) 
    {
        GlobalVariable* globalVar = &(*gv);
        if(globalVar == nullptr) {
            continue;
        }
        if(globalVar->getValueType()->isArrayTy())
        {
            if(!globalVar->hasName()) continue;
            string ArName = globalVar->getName().str();
            if(paramsname.find(ArName) == paramsname.end()) continue;
            auto ArTy = globalVar->getValueType();
            auto elemType = ArTy->getArrayElementType();
            int elemNum = ArTy->getArrayNumElements();
            if(elemNum == 0) continue;
            
            if(elemType->isStructTy())
            {
                string elemTyName = elemType->getStructName().str();
                {
                    if(elemTyName == "struct.fs_parameter_spec") {
                        res.push_back(globalVar);
                        //return globalVar;
                    }
                }
            }
        }
    }
    return res;
}

std::map<int, std::string> FilesystemExtractorPass::getPotentialFlagsinOldParams(GlobalVariable* fsparams, std::map<int, std::pair<std::string, int>>& intParams, std::map<int, std::string>& enumParams)
{
    //可能多种挂载选项参数字符串对应同一个挂载选项，但我只收集一种，这对于定向模糊测试指定挂载选项参数够用了
    std::map<int, std::string> res;
    if(!fsparams) {
        return res;
    }
    if (!fsparams->isConstant() || !fsparams->hasInitializer()) {
        return res;
    }
    Constant *fsparaminit = fsparams->getInitializer();
    if(auto *aggZero = dyn_cast<ConstantAggregateZero>(fsparaminit))
    {
        return res;
    }
    if(auto *arrayConst = dyn_cast<ConstantArray>(fsparaminit))
    {
        auto *structType = dyn_cast<StructType>(arrayConst->getType()->getElementType());
        if (!structType) {
            return res;
        }
        
        if (!structType->hasName() || structType->getName().str() != "struct.match_token") {
            return res;
        }
        for (unsigned i = 0; i < arrayConst->getNumOperands(); ++i)
        {
            Constant *elemConst = arrayConst->getAggregateElement(i);

            if (!elemConst) continue;
            if (dyn_cast<ConstantAggregateZero>(elemConst)) continue;

            ConstantStruct* structConst = dyn_cast<ConstantStruct>(elemConst);
            if(!structConst) continue;

            Constant* paramPatternVal = structConst->getOperand(Ctx->StructFieldIdx["match_token"]["pattern"]);
            string paramPattern = getFilesystemNameString(paramPatternVal);
            if(paramPattern == "?") continue;

            int optValue = -1;
            Constant *optField = structConst->getOperand(Ctx->StructFieldIdx["match_token"]["token"]);
            if (optField) {
                if (auto *optInt = dyn_cast<ConstantInt>(optField)) {
                    optValue = static_cast<int>(optInt->getZExtValue());
                }
            }
            if(optValue == -1) continue;

            // Enum-type options (strcmp-based): patterns with %s (e.g. "background_gc=%s")
            if (paramPattern.find("%s") != std::string::npos) {
                string cleanName = paramPattern;
                size_t eqPos = paramPattern.find("=%s");
                if (eqPos != std::string::npos)
                    cleanName = paramPattern.substr(0, eqPos);
                // Store placeholder — enum values filled later by traceStrcmpEnumChain
                if (enumParams.find(optValue) == enumParams.end())
                    enumParams[optValue] = cleanName;
                continue;
            }

            // Int-type options: patterns containing % (e.g. "active_logs=%u")
            if(paramPattern.find("%") != std::string::npos) {
                int radix = 0;
                if (paramPattern.find("%o") != std::string::npos)
                    radix = 8;
                else if(paramPattern.find("%u") != std::string::npos)
                    radix = 10;

                if(radix != 0)
                    intParams[optValue] = std::make_pair(paramPattern, radix);
                continue;
            }

            res[optValue] = paramPattern;
        }
    }

    return res;
}

std::map<int, std::pair<std::string, int>> FilesystemExtractorPass::getFlagsinParams(GlobalVariable* fsparams, std::map<int, std::pair<std::string, int>>& intParams)
{
    std::map<int, std::pair<std::string, int>> res;
    if(!fsparams) {
        return res;
    }
    if (!fsparams->isConstant() || !fsparams->hasInitializer()) {
        return res;
    }
    Constant *fsparaminit = fsparams->getInitializer();
    if(auto *aggZero = dyn_cast<ConstantAggregateZero>(fsparaminit))
    {
        return res;
    }
    if(auto *arrayConst = dyn_cast<ConstantArray>(fsparaminit))
    {
        auto *structType = dyn_cast<StructType>(arrayConst->getType()->getElementType());
        if (!structType) {
            return res;
        }
        
        if (!structType->hasName() || structType->getName().str() != "struct.fs_parameter_spec") {
            return res;
        }
        for (unsigned i = 0; i < arrayConst->getNumOperands(); ++i)
        {
            Constant *elemConst = arrayConst->getAggregateElement(i);

            if (!elemConst) continue;
            if (dyn_cast<ConstantAggregateZero>(elemConst)) continue;

            ConstantStruct* structConst = dyn_cast<ConstantStruct>(elemConst);
            if(!structConst) continue;

            Constant* typeFuncPtr = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["type"]);

            Constant* paramNameVal = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["name"]);
            string paramName = getFilesystemNameString(paramNameVal);
            if(paramName == "?") continue;

            int optValue = -1;
            Constant *optField = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["opt"]);
            if (optField) {
                if (auto *optInt = dyn_cast<ConstantInt>(optField)) {
                    optValue = static_cast<int>(optInt->getZExtValue());
                }
            }
            if(optValue == -1) continue;

            // Check for int-type parameters (fs_param_is_u32, fs_param_is_s32)
            if(!typeFuncPtr->isNullValue()) {
                if (auto *typeFunc = dyn_cast<Function>(typeFuncPtr)) {
                    StringRef funcName = typeFunc->getName();
                    if (funcName.endswith("_u32") || funcName.endswith("_s32") ||
                        funcName.endswith("_u64") || funcName.endswith("_u32oct")) {
                        // Detect radix: check data field for inttoptr (i64 8 to i8*)
                        int radix = 10;
                        Constant* dataField = structConst->getOperand(
                            Ctx->StructFieldIdx["fs_parameter_spec"]["data"]);
                        if (dataField && !dataField->isNullValue()) {
                            if (auto* CE = dyn_cast<ConstantExpr>(dataField)) {
                                if (CE->getOpcode() == Instruction::IntToPtr) {
                                    if (auto* radixCI = dyn_cast<ConstantInt>(CE->getOperand(0))) {
                                        if (radixCI->getZExtValue() == 8)
                                            radix = 8;
                                    }
                                }
                            }
                        }
                        intParams[optValue] = std::make_pair(paramName, radix);
                    }
                }
                continue;
            }

            // Flag-type parameters (fs_param_is_flag, null function pointer)
            Constant* flagsField = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["flags"]);
            if(flagsField) {
                if(auto *flagsInt = dyn_cast<ConstantInt>(flagsField)) {
                    uint32_t flagsValue = static_cast<uint32_t>(flagsInt->getZExtValue());
                    if(flagsValue & 0x0002) // fs_param_neg_with_no flag
                    {
                        res[optValue] = std::make_pair(paramName, 1);
                    }
                    else
                    {
                        res[optValue] = std::make_pair(paramName, 0);
                    }
                }
            }
        }
    }

    return res;
}

std::map<std::pair<int, std::string>, std::map<int, std::string>> FilesystemExtractorPass::getEnumsinParams(GlobalVariable* fsparams)
{
    std::map<std::pair<int, std::string>, std::map<int, std::string>> res;
    if(!fsparams) {
        return res;
    }
    if (!fsparams->isConstant() || !fsparams->hasInitializer()) {
        //errs() << "fsparams is not constant or has no initializer\n";
        return res;
    }
    Constant *fsparaminit = fsparams->getInitializer();
    if(auto *aggZero = dyn_cast<ConstantAggregateZero>(fsparaminit))
    {
        return res;
    }
    if(auto *arrayConst = dyn_cast<ConstantArray>(fsparaminit))
    {
        auto *structType = dyn_cast<StructType>(arrayConst->getType()->getElementType());
        if (!structType) {
            //errs() << "Array elements are not structs\n";
            return res;
        }
        
        if (!structType->hasName() || structType->getName().str() != "struct.fs_parameter_spec") {
            //errs() << "elements are not fsparam structs\n";
            return res;
        }
        for (unsigned i = 0; i < arrayConst->getNumOperands(); ++i)
        {
            Constant *elemConst = arrayConst->getAggregateElement(i);

            if (!elemConst) continue;
            if (dyn_cast<ConstantAggregateZero>(elemConst)) continue;

            ConstantStruct* structConst = dyn_cast<ConstantStruct>(elemConst);
            if(!structConst) continue;

            Constant* typeFuncPtr = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["type"]);
            if(typeFuncPtr->isNullValue()) continue;
            Function* typeFunc = dyn_cast<Function>(typeFuncPtr);
            if(!typeFunc) continue;
            if(!typeFunc->hasName() || typeFunc->getName().str() != "fs_param_is_enum") continue;

            Constant* paramNameVal = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["name"]);
            string paramName = getFilesystemNameString(paramNameVal);
            if(paramName == "?") continue;

            int optValue = -1;
            Constant *optField = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["opt"]);
            if (optField) {
                if (auto *optInt = dyn_cast<ConstantInt>(optField)) {
                    optValue = static_cast<int>(optInt->getZExtValue());
                }
            }
            if(optValue == -1) continue;

            Constant *enumfield = structConst->getOperand(Ctx->StructFieldIdx["fs_parameter_spec"]["data"]);
            if (!enumfield) continue;

            if (auto *bitcastExpr = dyn_cast<ConstantExpr>(enumfield)) {
                if (bitcastExpr->getOpcode() == Instruction::BitCast) {
                    Value *operand = bitcastExpr->getOperand(0);
                    
                    if (GlobalVariable *targetGV = dyn_cast<GlobalVariable>(operand)) {
                        //errs() << "Found target global variable: " << targetGV->getName() << "\n";
                        
                        Type *targetType = targetGV->getValueType();
                        if (targetType->isArrayTy()) {
                            //errs() << "Target is an array of type: "<< *targetType << "\n";
                            
                            if (targetGV->hasInitializer()) {
                                Constant *targetInit = targetGV->getInitializer();
                                
                                if (auto *ConstantTableArray = dyn_cast<ConstantArray>(targetInit)) {
                                    auto *enumstructType = dyn_cast<StructType>(ConstantTableArray->getType()->getElementType());
                                    if (!enumstructType) {
                                        //errs() << "Array elements are not structs\n";
                                        continue;
                                    }
        
                                    if (!enumstructType->hasName() || enumstructType->getName().str() != "struct.constant_table") {
                                        //errs() << "elements are not fsparam structs\n";
                                        continue;
                                    }

                                    for (unsigned i = 0; i < ConstantTableArray->getNumOperands(); ++i)
                                    {
                                        Constant *enumelemConst = ConstantTableArray->getAggregateElement(i);

                                        if (!enumelemConst) continue;
                                        if (dyn_cast<ConstantAggregateZero>(enumelemConst)) continue;

                                        ConstantStruct* enumstructConst = dyn_cast<ConstantStruct>(enumelemConst);
                                        if(!enumstructConst) continue;

                                        Constant* enumNameVal = enumstructConst->getOperand(Ctx->StructFieldIdx["constant_table"]["name"]);
                                        string enumName = getFilesystemNameString(enumNameVal);
                                        if(enumName == "?") continue;

                                        int enumValue = -1;
                                        Constant *enumvalueField = enumstructConst->getOperand(Ctx->StructFieldIdx["constant_table"]["value"]);
                                        if (enumvalueField) {
                                            if (auto *enumvalueInt = dyn_cast<ConstantInt>(enumvalueField)) {
                                                enumValue = static_cast<int>(enumvalueInt->getZExtValue());
                                            }
                                        }
                                        if(enumValue == -1) continue;
                                        res[std::make_pair(optValue, paramName)][enumValue] = enumName;
                                    }
                                } 
                                else if (auto *aggZero = dyn_cast<ConstantAggregateZero>(targetInit)) {
                                    continue;
                                }
                                else {
                                    //errs() << "Unsupported target array initializer: " << *targetInit << "\n";
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    return res;
}

void FilesystemExtractorPass::findAllRelatedSt(GetElementPtrInst* flaggep, set<string>& relatedSt)
{
    queue<GetElementPtrInst*> q;
    q.push(flaggep);
    while(!q.empty()) {
        GetElementPtrInst* currentGep = q.front();
        q.pop();
        Type *StTy = currentGep->getPointerOperand()->getType()->getPointerElementType();
        if (!StTy->isStructTy() || !currentGep->hasAllConstantIndices() || !(currentGep->getNumIndices() == 2)) {
            continue;
        }
        relatedSt.insert(currentGep->getSourceElementType()->getStructName().str());
        Value* currentSt = currentGep->getPointerOperand();
        if(dyn_cast<GetElementPtrInst>(currentSt)) {
            GetElementPtrInst* UpperGep0 = dyn_cast<GetElementPtrInst>(currentSt);
            q.push(UpperGep0);
            continue;
        }
        if(!dyn_cast<LoadInst>(currentSt)) continue;
        LoadInst* LdSt = dyn_cast<LoadInst>(currentSt);
        Value* StPValue = LdSt->getPointerOperand();
        StoreInst* Sti = nullptr;
        for(User *U: StPValue->users()) {
            if(dyn_cast<StoreInst>(U)) {
                Sti = dyn_cast<StoreInst>(U);
                break;
            }
        }
        if(!Sti) continue;

        Value* StValue = Sti->getValueOperand();
        if(dyn_cast<GetElementPtrInst>(StValue)) {
            GetElementPtrInst* UpperGep1 = dyn_cast<GetElementPtrInst>(StValue);
            q.push(UpperGep1);
            continue;
        }

        if(!dyn_cast<LoadInst>(StValue))
        {
            if(!dyn_cast<BitCastInst>(StValue)) continue;

            BitCastInst* bci = dyn_cast<BitCastInst>(StValue);
            Value* bciv = bci->getOperand(0);
            if(!dyn_cast<LoadInst>(bciv)) continue;
            StValue = bciv;
            
        }
        LoadInst* LdUpper = dyn_cast<LoadInst>(StValue);
        Value* UpperSt = LdUpper->getPointerOperand();
        if(!dyn_cast<GetElementPtrInst>(UpperSt)) continue;
        GetElementPtrInst* UpperGep = dyn_cast<GetElementPtrInst>(UpperSt);
        q.push(UpperGep);
    }
}

void FilesystemExtractorPass::CollectBitFieldSet(StoreInst* si, int cmd_value, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& res, set<string>& relatedSt, string BitFieldType) {
    if(BitFieldType == "result.negated;" || BitFieldType == "!result.negated;" || BitFieldType == "result.boolean;" || BitFieldType == "result.negated ? 0 : 1;" || BitFieldType == "result.negated ? 1 : 0;") {
        Value* stpi = si->getPointerOperand();
        if(GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(stpi)) {
            Value* stv = si->getValueOperand();
            if(Instruction* stvi = dyn_cast<Instruction>(stv)) {
                if(stvi->getOpcode() == Instruction::Or) {
                    Instruction* ori1 = dyn_cast<Instruction>(stvi->getOperand(0));
                    Instruction* ori2 = dyn_cast<Instruction>(stvi->getOperand(1));
                    Instruction* andi = nullptr;
                    if(ori1 && ori1->getOpcode() == Instruction::And) {
                        andi = ori1;
                    } else if(ori2 && ori2->getOpcode() == Instruction::And) {
                        andi = ori2;
                    }
                    if(andi) {
                        ConstantInt* constantInt = dyn_cast<ConstantInt>(andi->getOperand(1));
                        if(constantInt) {
                            uint64_t tmp = ~(constantInt->getSExtValue());
                            int tmpe = findExponentOfTwo(tmp);
                            if(tmpe != -1) {
                                uint64_t flagcollect = tmpe;
                                Type *flagPTy = gepi->getPointerOperand()->getType();
                                Type *flagTy = flagPTy->getPointerElementType();
                                if (flagTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2)
                                {
                                    auto offsetVal = gepi->getOperand(2);
                                    auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                    int offsetinst = offsetInt->getZExtValue();
                                    string flagtost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst) + ":" + std::to_string(flagcollect);
                                    if(BitFieldType == "!result.negated;" || BitFieldType == "result.boolean;" || BitFieldType == "result.negated ? 0 : 1;") {
                                        res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, "bitfieldclear"), std::make_pair(cmd_value, -2)));
                                        res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, "bitfieldset"), std::make_pair(cmd_value, -3)));
                                    } else {
                                        res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, "bitfieldset"), std::make_pair(cmd_value, -2)));
                                        res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, "bitfieldclear"), std::make_pair(cmd_value, -3)));
                                    }
                                    
                                    string tost = gepi->getSourceElementType()->getStructName().str();
                                    if(relatedSt.find(tost) == relatedSt.end()) {
                                        findAllRelatedSt(gepi, relatedSt);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

GetElementPtrInst* TryGetGEPFromCall(Value* flagTarget, CallInst* callToParseF) {
    GetElementPtrInst* res = nullptr;
    if(!callToParseF) return res;
    if(!flagTarget) return res;
    if(!dyn_cast<LoadInst>(flagTarget)) return res;
    LoadInst* ldflagtarget = dyn_cast<LoadInst>(flagTarget);
    Value* argaddr = ldflagtarget->getPointerOperand();
    
    for(User *U: argaddr->users()) {
        if(dyn_cast<StoreInst>(U)) {
            StoreInst* starg = dyn_cast<StoreInst>(U);
            Value* argvalue = starg->getValueOperand();
            Value* argaddrvalue = starg->getPointerOperand();
            if(argaddrvalue != argaddr) continue;
            if(dyn_cast<Argument>(argvalue)) continue;
            Argument* ArgV = dyn_cast<Argument>(argvalue);
            unsigned int ArgNum = ArgV->getArgNo();
            Value* actualArg = callToParseF->getOperand(ArgNum);
            if(dyn_cast<GetElementPtrInst>(actualArg)) {
                res = dyn_cast<GetElementPtrInst>(actualArg);
            }
            else {
                for(User *ArgU: actualArg->users()) {
                    if(dyn_cast<LoadInst>(ArgU)) {
                        //LoadInst* ldarg = dyn_cast<LoadInst>(ArgU);
                        Value* ldv = dyn_cast<Value>(ArgU);
                        for(User *ArgvU: ldv->users()) {
                            if(dyn_cast<StoreInst>(ArgvU)) {
                                StoreInst* StToGEP = dyn_cast<StoreInst>(ArgvU);
                                Value* StToGEPv = StToGEP->getValueOperand();
                                if(StToGEPv != ldv) continue;
                                Value* StToGEPp = StToGEP->getPointerOperand();
                                if(dyn_cast<GetElementPtrInst>(StToGEPp)) {
                                    res = dyn_cast<GetElementPtrInst>(StToGEPp);
                                    return res;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    return res;
}

std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int,int>>>> FilesystemExtractorPass::collectOldParamsParse(Function* parseF, CallInst* CallToParseF, std::map<int, std::string> flagParams, std::map<int, std::pair<std::string, int>>& intParams, std::map<int, std::string> enumParams, std::set<string>& relatedSt, std::map<int, std::map<int, std::string>>& enumCollect) 
{
    outs() << "start analyze old param parse func " << parseF->getName() << ": " << "\n";
    std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> res;
    Value* parsedvalue = nullptr;
    std::set<llvm::BasicBlock *> all_bb;
    std::set<Value*> parsedstorevalues;
    llvm::DominatorTree *DT = new llvm::DominatorTree(*parseF);
    for (auto &bb : *parseF) {
        all_bb.insert(&bb);
    }

    string srcfilename = parseF->getParent()->getSourceFileName();

    for (inst_iterator i = inst_begin(parseF), e = inst_end(parseF); 
				i != e; ++i) {
		Instruction *I = &*i;

		if (CallInst *CI = dyn_cast<CallInst>(I)) {
			auto getCalledF=CI->getCalledFunction();
            if (getCalledF && endsWith(getCalledF->getName().str(), "match_token") && CI->getNumOperands()==4) {
                parsedvalue = dyn_cast<Value>(CI);
                parsedstorevalues.insert(parsedvalue);
                for(User *U: parsedvalue->users()) {
                    if(dyn_cast<StoreInst>(U)) {
                        StoreInst* Sti = dyn_cast<StoreInst>(U);
                        Value* optvalue = Sti->getValueOperand();
                        if(optvalue != parsedvalue) continue;
                        Value* optstorevalue = Sti->getPointerOperand();
                        parsedstorevalues.insert(optstorevalue);
                    }
                }
                break;
            }
		}
	}

    while (!all_bb.empty())
    {
        auto bb = *all_bb.begin();
        all_bb.erase(bb);
        for (auto &i : *bb)
        {
            switch (i.getOpcode())
            {
                case llvm::Instruction::Switch: {
                    if(!parsedvalue) break;
                    //outs() << parseF->getName() <<" switch: " << i << "\n";
                    auto si = llvm::dyn_cast<llvm::SwitchInst>(&i);
                    Value* targetSwitchCond = si->getCondition();
                    if(!dyn_cast<LoadInst>(targetSwitchCond)) break;
                    LoadInst* swoptld = dyn_cast<LoadInst>(targetSwitchCond);
                    Value* swoptldpt = swoptld->getPointerOperand();
                    if(parsedstorevalues.find(swoptldpt) == parsedstorevalues.end()) break;
                    //outs() << "find switch token in " << parseF->getName() << ": " << *si << "\n";
                    BasicBlock* DefaultBB = si->getDefaultDest();
                    int DefaultIdx = getBasicBlockIndex(DefaultBB);
                    //if(parsedvalue != targetSwitchCond && parsedvalue != targetSwitchCond->stripPointerCasts()) break;
                    for (auto cis = si->case_begin(), cie = si->case_end(); cis != cie; cis++)
                    {
                        auto cmd_val = cis->getCaseValue();
                        auto sb = cis->getCaseSuccessor();
                        all_bb.erase(sb);
                        //std::set<llvm::BasicBlock *> visited_in_cmd;
                        auto cmd_value = cmd_val->getValue().getZExtValue();
                        set<BasicBlock*> caseBBs;
                        getAllCaseBBs(caseBBs, sb, all_bb, DefaultIdx);
                        if(flagParams.find(cmd_value) != flagParams.end())
                        {   
                            uint32_t flagcollect = 0xffffffff;
                            bool getflag = false;
                            //string optName = flagParams[cmd_value].first;
                            
                            for(BasicBlock* caseblock : caseBBs) {
                                for(auto &i : *caseblock)
                                {
                                    if(auto sti = dyn_cast<llvm::StoreInst>(&i)) {
                                        string configtype = "";
                                        Value *storevalue = sti->getValueOperand();
                                        bool isBit = false;
                                        if(auto andor = dyn_cast<llvm::Instruction>(storevalue))
                                        {
                                            isBit = MountOptFieldIsOneBit01(srcfilename, sti);
                                            if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                            {
                                                BinaryOperator* binOp = dyn_cast<BinaryOperator>(andor);
                                                for(int i = 0; i < binOp->getNumOperands(); i++)
                                                {
                                                    ConstantInt* constantInt = dyn_cast<ConstantInt>(binOp->getOperand(i));
                                                    if(constantInt == nullptr)
                                                    continue;
                                                    // tmp += " " + to_string(constantInt->getZExtValue());
                                                    if(andor->getOpcode() == Instruction::And) 
                                                    {
                                                        if(isBit) {
                                                            configtype = "bitfieldclear";
                                                            uint64_t tmp = ~(constantInt->getSExtValue());
                                                            int tmpe = findExponentOfTwo(tmp);
                                                            if(tmpe == -1) continue;
                                                            flagcollect = tmpe;
                                                        } else {
                                                            configtype = "clear";
                                                            flagcollect &= ~(constantInt->getSExtValue());
                                                        }
                                                    }
                                                    else
                                                    {
                                                        if(isBit) {
                                                            configtype = "bitfieldset";
                                                            uint64_t tmp = constantInt->getZExtValue();
                                                            int tmpe = findExponentOfTwo(tmp);
                                                            if(tmpe == -1) continue;
                                                            flagcollect = tmpe;
                                                        } else {
                                                            configtype = "set";
                                                            flagcollect &= constantInt->getZExtValue();
                                                        }
                                                    }
                                                     
                                                    getflag = true;
                                                }
                                            }
                                        }
                                        else if(auto storeconst = dyn_cast<ConstantInt>(storevalue)) {
                                            uint32_t storeint = storeconst->getZExtValue();
                                            if(storeint == 1) {
                                                configtype = "assigntrue";
                                                flagcollect = 0xfffffff1;
                                                getflag = true;
                                            } 
                                            else if(storeint == 0) {
                                                configtype = "assignfalse";
                                                flagcollect = 0xfffffff0;
                                                getflag = true;
                                            }
                                        }
                                        if(getflag)
                                        {
                                            Value* flagtarget = sti->getPointerOperand();
                                            //outs() << "get flag in " << parseF->getName() << ": " << *flagtarget << "\n";
                                            if(isBit) {
                                                if(dyn_cast<BitCastInst>(flagtarget)) {
                                                    BitCastInst* bcifromgep = dyn_cast<BitCastInst>(flagtarget);
                                                    flagtarget = bcifromgep->getOperand(0);
                                                }
                                            }
                                            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(flagtarget);
                                            if(!GEP) {
                                                GEP = TryGetGEPFromCall(flagtarget, CallToParseF);
                                            }

                                            if(!GEP) {
                                                getflag = false;
                                                continue;
                                            }

                                            Type *flagPTy = GEP->getPointerOperand()->getType();
                                            Type *flagTy = flagPTy->getPointerElementType();
                                            if (flagTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                            {
                                                auto offsetVal = GEP->getOperand(2);
                                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                int offsetinst = offsetInt->getZExtValue();
                                                string flagtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                if(isBit) {
                                                    flagtost = flagtost + ":" + std::to_string(flagcollect);
                                                }
                                                if((configtype == "set" || configtype == "clear") && !is_power_of_2(flagcollect)) {
                                                    vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(flagcollect);
                                                    for(uint32_t splitflag : splitflagcollect) {
                                                        res[flagtost].insert(std::make_pair(std::make_pair(splitflag, configtype), std::make_pair(cmd_value, -4)));
                                                    }
                                                }
                                                res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, configtype), std::make_pair(cmd_value, -4)));
                                                string tost = GEP->getSourceElementType()->getStructName().str();
                                                if(relatedSt.find(tost) == relatedSt.end()) {
                                                    findAllRelatedSt(GEP, relatedSt);
                                                }
                                            }
                                            getflag = false;
                                        }
                                    }
                                    /*else if(auto calli = dyn_cast<llvm::CallInst>(&i)) {
                                        auto setorclearFunc=calli->getCalledFunction();
                                        if(setorclearFunc && (setorclearFunc->getName().str() == "set_bit" || setorclearFunc->getName().str() == "clear_bit")) {
                                            ConstantInt* constantInt = dyn_cast<ConstantInt>(calli->getOperand(1));
                                            if(constantInt != nullptr) {
                                                flagcollect &= constantInt->getZExtValue();
                                                getflag = true;
                                            }
                                        }
                                    }*/
                                }        
                            }
                        } else if (intParams.find(cmd_value) != intParams.end()) {
                            // int option: detect store(LoadInst from alloca → GEP(struct_field))
                            for(BasicBlock* caseblock : caseBBs) {
                                for (auto &i : *sb) {
                                    if (auto sti = dyn_cast<StoreInst>(&i)) {
                                        Value* storeval = sti->getValueOperand();
                                        if (isa<ConstantInt>(storeval)) continue;
                                        if (auto inst = dyn_cast<Instruction>(storeval))
                                            if (inst->isBinaryOp()) continue;
                                        if(TruncInst* trunci = dyn_cast<TruncInst>(storeval))
                                            storeval = trunci->getOperand(0);
                                        if (auto ldi = dyn_cast<LoadInst>(storeval)) {
                                            Value* ptr = sti->getPointerOperand();
                                            if (BitCastInst* bci = dyn_cast<BitCastInst>(ptr))
                                                ptr = bci->getOperand(0);
                                            if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(ptr)) {
                                                Type* gepTy = gep->getSourceElementType();
                                                if (gepTy->isStructTy() && gep->hasAllConstantIndices() && gep->getNumIndices() == 2) {
                                                    int offset = dyn_cast<ConstantInt>(gep->getOperand(2))->getZExtValue();
                                                    string fieldKey = gepTy->getStructName().str() + std::to_string(offset);
                                                    res[fieldKey].insert({{0xffffffff, "assignint"}, {cmd_value, -5}});
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else if (enumParams.find(cmd_value) != enumParams.end()) {
                            // strcmp-based enum chain detection (for old API)
                            for(BasicBlock* caseblock : caseBBs) {
                                for (auto &ei : *caseblock) {
                                    if (BranchInst* bi = dyn_cast<BranchInst>(&ei)) {
                                        if (isStrcmpBranch(bi)) {
                                            traceStrcmpEnumChain(bi, cmd_value, res, enumCollect);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
    return res;
}

void trygetmountoptfieldid(Function* CF, string srcFileName, string& flagst, bool isopt1) {
    for(inst_iterator iter = inst_begin(CF); iter != inst_end(CF); iter++)
    {
        Instruction* I = &*iter;
        if(StoreInst* sti = dyn_cast<StoreInst>(I)) {
            Value* stipv = sti->getPointerOperand();
            if(GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(stipv)) {
                Type *flagPTy = gepi->getPointerOperand()->getType();
                Type *flagTy = flagPTy->getPointerElementType();
                if (flagTy->isStructTy() && flagTy->getStructName().str() == "struct.ext4_sb_info" && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2)
                {
                    if (DILocation *Loc = sti->getDebugLoc()) {
                        int lineNum = Loc->getLine();
                        if (srcFileName != "" && lineNum != 0) {
                            if(startsWith(srcFileName, "fs") && GlobalCtx.CaseSrcDir != "") {
                                srcFileName = GlobalCtx.CaseSrcDir + "/" + srcFileName;
                            }
                            ifstream file(srcFileName);
                            gotoLine(file, lineNum);
                            string line;
                            getline(file, line);
                            strip(line);
                            if (line.size() == 0) {
                                continue;
                            }
                            if(line.find("sbi->s_mount_opt |=") != std::string::npos && isopt1) {
                                auto offsetVal = gepi->getOperand(2);
                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                int offsetinst = offsetInt->getZExtValue();
                                flagst = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                return;
                            } else if(line.find("sbi->s_mount_opt2 |=") != std::string::npos && !isopt1) {
                                auto offsetVal = gepi->getOperand(2);
                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                int offsetinst = offsetInt->getZExtValue();
                                flagst = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                return;
                            }
                        }
                    }
                }
            }
        }
    }
}

// Helper: get byte offset of a field in struct.ext4_fs_context using LLVM StructLayout
// First tries debug info (kernel compiled with -g), falls back to hardcoded index table
static int getExt4FsContextFieldOffset(Module* M, const std::string& fieldName) {
    StructType* fcTy = StructType::getTypeByName(M->getContext(), "struct.ext4_fs_context");
    if (!fcTy) return -1;
    const DataLayout& DL = M->getDataLayout();
    const StructLayout* layout = DL.getStructLayout(fcTy);

    // Try debug info first: iterate DICompositeType members
    // Note: requires kernel compiled with -g -fno-eliminate-unused-debug-types
    // for DICompositeType to appear in CU's retainedTypes
    if (NamedMDNode* CU_Nodes = M->getNamedMetadata("llvm.dbg.cu")) {
        DebugInfoFinder DIFinder;
        DIFinder.processModule(*M);
        for (auto* CUNode : CU_Nodes->operands()) {
            DICompileUnit* CU = dyn_cast<DICompileUnit>(CUNode);
            if (!CU) continue;
            for (auto* RetainedType : CU->getRetainedTypes()) {
                DICompositeType* DCTy = dyn_cast<DICompositeType>(RetainedType);
                if (!DCTy) continue;
                if (DCTy->getName() == "ext4_fs_context") {
                    DINodeArray elements = DCTy->getElements();
                    for (unsigned i = 0; i < elements.size(); i++) {
                        DIDerivedType* member = dyn_cast<DIDerivedType>(elements[i]);
                        if (member && member->getName() == fieldName) {
                            if (i < fcTy->getNumElements())
                                return layout->getElementOffset(i);
                        }
                    }
                }
            }
            // Also search subprogram local variables: the type may only be
            // referenced via a local variable, not in retainedTypes.
            for (auto* SP : DIFinder.subprograms()) {
                if (SP->getUnit() != CU) continue;
                for (auto* Node : SP->getRetainedNodes()) {
                    DILocalVariable* LV = dyn_cast<DILocalVariable>(Node);
                    if (!LV) continue;
                    DIType* Ty = LV->getType();
                    while (auto* DT = dyn_cast<DIDerivedType>(Ty))
                        Ty = DT->getBaseType();
                    DICompositeType* DCTy = dyn_cast<DICompositeType>(Ty);
                    if (!DCTy || DCTy->getName() != "ext4_fs_context")
                        continue;
                    DINodeArray elements = DCTy->getElements();
                    for (unsigned i = 0; i < elements.size(); i++) {
                        DIDerivedType* member = dyn_cast<DIDerivedType>(elements[i]);
                        if (member && member->getName() == fieldName) {
                            if (i < fcTy->getNumElements())
                                return layout->getElementOffset(i);
                        }
                    }
                }
            }
        }
    }

    // Fallback: hardcoded field index table (for IR built without debug info)
    static const std::map<std::string, unsigned> fieldIndex = {
        {"s_sb_block",            26},
        {"s_commit_interval",     8},
        {"s_min_batch_time",      20},
        {"s_max_batch_time",      19},
        {"journal_devnum",        6},
        {"s_stripe",              9},
        {"s_want_extra_isize",    11},
        {"s_inode_readahead_blks", 10},
        {"journal_ioprio",        14},
        {"s_li_wait_mult",        12},
        {"s_max_dir_size_kb",     13},
        {"vals_s_mount_opt2",     17},
    };
    auto it = fieldIndex.find(fieldName);
    if (it != fieldIndex.end()) {
        unsigned idx = it->second;
        if (idx < fcTy->getNumElements())
            return layout->getElementOffset(idx);
    }
    return -1;
}

std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int,int>>>> FilesystemExtractorPass::collectExt4ParamParse(Module* Ext4Super, std::set<string>& relatedSt) {
    std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int,int>>>> res;
    GlobalVariable* ext4MountOptConsts = nullptr;
    string smountopt1 = "";
    string smountopt2 = "";
    unsigned int opt_set = 0x0001;
    unsigned int opt_clear = 0x0002;
    unsigned int opt_2 = 0x0100;
    for (Module::global_iterator gi = Ext4Super->global_begin(); 
			gi != Ext4Super->global_end(); ++gi) {
		GlobalVariable* GV = &*gi;
		if(GV == nullptr) {
            continue;
        }
        if(GV->getValueType()->isArrayTy())
        {
            if(!GV->hasName()) continue;
            string ArName = GV->getName().str();
            if(ArName != "ext4_mount_opts") continue;
            if (!GV->isConstant() || !GV->hasInitializer()) continue;
            auto ArTy = GV->getValueType();
            auto elemType = ArTy->getArrayElementType();
            int elemNum = ArTy->getArrayNumElements();
            if(elemNum == 0) continue;
            
            if(elemType->isStructTy())
            {
                string elemTyName = elemType->getStructName().str();
                {
                    if(elemTyName == "struct.mount_opts") {
                        ext4MountOptConsts = GV;
                        break;
                        //return globalVar;
                    }
                }
            }
        }
	}
    if(!ext4MountOptConsts) {
        return res;
    }
    for (auto &F: *Ext4Super) {
        Function* cf = &F;
        trygetmountoptfieldid(cf, Ext4Super->getSourceFileName(), smountopt1, true);
        trygetmountoptfieldid(cf, Ext4Super->getSourceFileName(), smountopt2, false);
    }
    if(smountopt1 == "") {
        return res;
    }
    
    Constant *fsparaminit = ext4MountOptConsts->getInitializer();
    if(auto *aggZero = dyn_cast<ConstantAggregateZero>(fsparaminit))
    {
        return res;
    }
    
    // Phase 3: find ext4_param_specs[] (new kernel) or tokens[] (old kernel)
    // and build optIdToName (optid → option name) from its entries.
    // Auto-detect kernel version by struct type, not by caller flag.
    map<int, string> optIdToName;
    GlobalVariable* foundParamSpecs = nullptr;
    bool isnew = false;

    for (Module::global_iterator gi = Ext4Super->global_begin();
         gi != Ext4Super->global_end(); ++gi) {
        GlobalVariable* GV = &*gi;
        if (!GV || !GV->getValueType()->isArrayTy()) continue;
        if (!GV->isConstant() || !GV->hasInitializer()) continue;

        auto* arrTy = GV->getValueType();
        auto* elemTy = arrTy->getArrayElementType();
        if (!elemTy->isStructTy()) continue;

        string stName = elemTy->getStructName().str();
        if (stName == "struct.fs_parameter_spec") {
            foundParamSpecs = GV;
            isnew = true;
            break;
        }
        if (stName == "struct.match_token") {
            foundParamSpecs = GV;
            isnew = false;
            break;
        }
    }

    if (foundParamSpecs && foundParamSpecs->hasInitializer()) {
        auto* arr = dyn_cast<ConstantArray>(foundParamSpecs->getInitializer());
        if (arr) {
            for (unsigned i = 0; i < arr->getNumOperands(); ++i) {
                auto* st = dyn_cast<ConstantStruct>(arr->getAggregateElement(i));
                if (!st) continue;

                int optValue = -1;
                string name;

                if (isnew) {
                    name = getFilesystemNameString(st->getOperand(0));
                    auto* ci = dyn_cast<ConstantInt>(st->getOperand(2));
                    if (ci) optValue = ci->getZExtValue();
                } else {
                    name = getFilesystemNameString(
                        st->getOperand(Ctx->StructFieldIdx["match_token"]["pattern"]));
                    auto* ci = dyn_cast<ConstantInt>(
                        st->getOperand(Ctx->StructFieldIdx["match_token"]["token"]));
                    if (ci) optValue = ci->getZExtValue();
                    size_t eq = name.find('=');
                    if (eq != string::npos) name = name.substr(0, eq);
                }

                if (name == "?" || name.empty() || optValue == -1) continue;
                optIdToName[optValue] = name;
            }
        }
    }

    if(auto *arrayConst = dyn_cast<ConstantArray>(fsparaminit))
    {   relatedSt.insert("struct.ext4_sb_info");
        for (unsigned i = 0; i < arrayConst->getNumOperands(); ++i)
        {
            Constant *elemConst = arrayConst->getAggregateElement(i);

            if (!elemConst) continue;
            if (dyn_cast<ConstantAggregateZero>(elemConst)) continue;

            ConstantStruct* structConst = dyn_cast<ConstantStruct>(elemConst);
            if(!structConst) continue;

            int optid = -1;
            Constant* tokencons = structConst->getOperand(Ctx->StructFieldIdx["mount_opts"]["token"]);
            if (tokencons) {
                if (auto *optInt = dyn_cast<ConstantInt>(tokencons)) {
                    optid = static_cast<int>(optInt->getZExtValue());
                    //res[optValue] = paramName;
                }
            }
            if(optid == -1) continue;

            unsigned int optmountcons = 0;
            Constant* mountoptcons = structConst->getOperand(Ctx->StructFieldIdx["mount_opts"]["mount_opt"]);
            if (mountoptcons) {
                if (auto *optInt = dyn_cast<ConstantInt>(mountoptcons)) {
                    optmountcons = static_cast<int>(optInt->getZExtValue());
                    //res[optValue] = paramName;
                }
            }
            if(optmountcons == 0) {
                // Int-type options: mount_opt == 0 in ext4_param_specs
                // Map mount option name → ext4_fs_context field (name is
                // version-independent via optIdToName; token numbers change)
                static const struct { const char* optName; const char* field; } intOptByName[] = {
                    {"sb",                    "s_sb_block"},
                    {"commit",                "s_commit_interval"},
                    {"min_batch_time",        "s_min_batch_time"},
                    {"max_batch_time",        "s_max_batch_time"},
                    {"journal_dev",           "journal_devnum"},
                    {"stripe",                "s_stripe"},
                    {"debug_want_extra_isize","s_want_extra_isize"},
                    {"inode_readahead_blks",  "s_inode_readahead_blks"},
                    {"journal_ioprio",        "journal_ioprio"},
                    {"max_dir_size_kb",       "s_max_dir_size_kb"},
                    {"mb_optimize_scan",      "vals_s_mount_opt2"},
                    {"fc_debug_max_replay",   "s_fc_debug_max_replay"},
                };
                if (optIdToName.count(optid)) {
                    const string& optName = optIdToName[optid];
                    for (auto& im : intOptByName) {
                        if (optName == im.optName) {
                            int off = getExt4FsContextFieldOffset(Ext4Super, im.field);
                            if (off >= 0) {
                                string key = "struct.ext4_fs_context" + std::to_string(off);
                                res[key].insert({{0xffffffff, "assignint"}, {optid, -5}});
                            }
                            break;
                        }
                    }
                }
                // Opt_init_itable has mount_opt != 0 — handled in the flag branch below
                continue;
            }

            unsigned int optflagscons = 0;
            Constant *flagscons = structConst->getOperand(Ctx->StructFieldIdx["mount_opts"]["flags"]);
            if (flagscons) {
                if (auto *optInt = dyn_cast<ConstantInt>(flagscons)) {
                    optflagscons = static_cast<int>(optInt->getZExtValue());
                    //res[optValue] = paramName;
                }
            }
            if(optflagscons == 0) continue;

            if(optflagscons & opt_set) {
                if(optflagscons & opt_2) {
                    if(smountopt2 != "") {
                        if(!is_power_of_2(optmountcons)) {
                            vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(optmountcons);
                            for(uint32_t splitflag : splitflagcollect) {
                                res[smountopt2].insert(std::make_pair(std::make_pair(splitflag, "set"), std::make_pair(optid, -1)));
                            }
                        }
                        res[smountopt2].insert(std::make_pair(std::make_pair(optmountcons, "set"), std::make_pair(optid, -1)));
                    }
                } else {
                    if(!is_power_of_2(optmountcons)) {
                        vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(optmountcons);
                        for(uint32_t splitflag : splitflagcollect) {
                            res[smountopt1].insert(std::make_pair(std::make_pair(splitflag, "set"), std::make_pair(optid, -1)));
                        }
                    }
                    res[smountopt1].insert(std::make_pair(std::make_pair(optmountcons, "set"), std::make_pair(optid, -1)));
                    // Opt_init_itable (60): also stores int to s_li_wait_mult
                    if (optIdToName.count(optid) && optIdToName[optid] == "init_itable") {
                        int off = getExt4FsContextFieldOffset(Ext4Super, "s_li_wait_mult");
                        if (off >= 0) {
                            string key = "struct.ext4_fs_context" + std::to_string(off);
                            res[key].insert({{0xffffffff, "assignint"}, {optid, -5}});
                        }
                    }
                }
            } else if (optflagscons & opt_clear) {
                if(optflagscons & opt_2) {
                    if(smountopt2 != "") {
                        if(!is_power_of_2(optmountcons)) {
                            vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(optmountcons);
                            for(uint32_t splitflag : splitflagcollect) {
                                res[smountopt2].insert(std::make_pair(std::make_pair(splitflag, "clear"), std::make_pair(optid, -1)));
                            }
                        }
                        res[smountopt2].insert(std::make_pair(std::make_pair(optmountcons, "clear"), std::make_pair(optid, -1)));
                    }
                } else {
                    if(!is_power_of_2(optmountcons)) {
                        vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(optmountcons);
                        for(uint32_t splitflag : splitflagcollect) {
                            res[smountopt1].insert(std::make_pair(std::make_pair(splitflag, "clear"), std::make_pair(optid, -1)));
                        }
                    }
                    res[smountopt1].insert(std::make_pair(std::make_pair(optmountcons, "clear"), std::make_pair(optid, -1)));
                }
            }
        }
    }
    return res;
}

bool judgeBrIsNo(BasicBlock* bb0, BasicBlock* bb1) {
    bool isno = false;
    int bb0idx = getBasicBlockIndex(bb0);
    int bb1idx = getBasicBlockIndex(bb1);
    if (bb0idx < bb1idx) {
        isno = false;
    } else {
        isno = true;
    }
    string b0name = "";
    string b1name = "";
    if(bb0->hasName()) b0name = bb0->getName().str();
    if(bb1->hasName()) b1name = bb1->getName().str();
    if(b0name.find(".then") != std::string::npos || b0name.find(".true") != std::string::npos || b1name.find(".false") != std::string::npos) {
        isno = false;
    } else if (b0name.find(".false") != std::string::npos || b1name.find(".true") != std::string::npos || b1name.find(".then") != std::string::npos)
    {
        isno = true;
    }
    return isno;
}

std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int,int>>>> FilesystemExtractorPass::collectParamsParse(Function* parseF, std::map<std::pair<int, std::string>, std::map<int, std::string>> enumParams, std::map<int, std::pair<std::string, int>> flagParams, std::map<int, std::pair<std::string, int>>& intParams, std::set<string>& relatedSt) 
{
    outs() << "start analyze param parse func " << parseF->getName() << ": " << "\n";
    std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> res;
    Value* parsedvalue = nullptr;
    std::set<llvm::BasicBlock *> all_bb;
    std::set<Value*> parsedstorevalues;
    llvm::DominatorTree *DT = new llvm::DominatorTree(*parseF);
    for (auto &bb : *parseF) {
        all_bb.insert(&bb);
    }
    std::set<int> enumoptnum;
    std::map<int, std::map<int, std::string>> enumopttoenum;
    for(auto& enumopt : enumParams) {
        std::pair<int, string> enumoptstr = enumopt.first;
        std::map<int, string> enumnumstr = enumopt.second;
        enumoptnum.insert(enumoptstr.first);
        enumopttoenum[enumoptstr.first] = enumnumstr;
    }

    string srcfilename = parseF->getParent()->getSourceFileName();

    for (inst_iterator i = inst_begin(parseF), e = inst_end(parseF); 
				i != e; ++i) {
		Instruction *I = &*i;

		if (CallInst *CI = dyn_cast<CallInst>(I)) {
			auto getCalledF=CI->getCalledFunction();
            if (getCalledF && endsWith(getCalledF->getName().str(), "fs_parse") && CI->getNumOperands()==5) {
                parsedvalue = dyn_cast<Value>(CI);
                parsedstorevalues.insert(parsedvalue);
                for(User *U: parsedvalue->users()) {
                    if(dyn_cast<StoreInst>(U)) {
                        StoreInst* Sti = dyn_cast<StoreInst>(U);
                        Value* optvalue = Sti->getValueOperand();
                        if(optvalue != parsedvalue) continue;
                        Value* optstorevalue = Sti->getPointerOperand();
                        parsedstorevalues.insert(optstorevalue);
                    }
                }
                break;
            }
		}
	}

    while (!all_bb.empty())
    {
        auto bb = *all_bb.begin();
        all_bb.erase(bb);
        for (auto &i : *bb)
        {
            switch (i.getOpcode())
            {
                case llvm::Instruction::Switch: {
                    if(!parsedvalue) break;
                    //outs() << parseF->getName() <<" switch: " << i << "\n";
                    auto si = llvm::dyn_cast<llvm::SwitchInst>(&i);
                    Value* targetSwitchCond = si->getCondition();
                    if(!dyn_cast<LoadInst>(targetSwitchCond)) break;
                    LoadInst* swoptld = dyn_cast<LoadInst>(targetSwitchCond);
                    Value* swoptldpt = swoptld->getPointerOperand();
                    if(parsedstorevalues.find(swoptldpt) == parsedstorevalues.end()) break;
                    //outs() << "find switch opt in " << parseF->getName() << ": " << *si << "\n";
                    //if(parsedvalue != targetSwitchCond && parsedvalue != targetSwitchCond->stripPointerCasts()) break;
                    for (auto cis = si->case_begin(), cie = si->case_end(); cis != cie; cis++)
                    {
                        auto cmd_val = cis->getCaseValue();
                        auto sb = cis->getCaseSuccessor();
                        all_bb.erase(sb);
                        //std::set<llvm::BasicBlock *> visited_in_cmd;
                        auto cmd_value = cmd_val->getValue().getZExtValue();
                        if(flagParams.find(cmd_value) != flagParams.end())
                        {   
                            uint32_t flagcollect = 0xffffffff;
                            bool getflag = false;
                            //string optName = flagParams[cmd_value].first;
                            if(flagParams[cmd_value].second)
                            {
                                for (auto &i : *sb) {
                                    if(auto si = llvm::dyn_cast<llvm::StoreInst>(&i))
                                    {
                                        string BitFieldSetType = MountOptFieldIsOneBitBooleanOrNegated(srcfilename, si);
                                        if(BitFieldSetType != "") {
                                            CollectBitFieldSet(si, cmd_value, res, relatedSt, BitFieldSetType);
                                        }
                                    }
                                    else if(auto bi = llvm::dyn_cast<llvm::BranchInst>(&i))
                                    {
                                        if(bi->getNumSuccessors() != 2) continue;
                                        //outs() << "find no flag and its branch in " << parseF->getName() << ": " << *bi << "\n";
                                        string configtype = "";
                                        Value* CondNegatedOrBoolean = bi->getCondition();
                                        //BasicBlock* brblock1 = nullptr;
                                        //BasicBlock* brblock2 = nullptr;
                                        //outs() << "get BranchInst in " << parseF->getName() << " with opt num " << cmd_value << ": " << *bi << "\n";
                                        BasicBlock* brblock1 = nullptr;
                                        BasicBlock* brblock2 = nullptr;
                                        bool isno = false;
                                        isno = judgeBrIsNo(bi->getSuccessor(0), bi->getSuccessor(1));
                                        if(ParseResultIsBoolean(CondNegatedOrBoolean)) {
                                            if(isno) {
                                                brblock1 = bi->getSuccessor(0);
                                                brblock2 = bi->getSuccessor(1);
                                            } else {
                                                brblock1 = bi->getSuccessor(1);
                                                brblock2 = bi->getSuccessor(0);
                                            }
                                        } else {
                                            if(isno) {
                                                brblock1 = bi->getSuccessor(1);
                                                brblock2 = bi->getSuccessor(0);
                                            } else {
                                                brblock1 = bi->getSuccessor(0);
                                                brblock2 = bi->getSuccessor(1);
                                            }
                                        }
                                        all_bb.erase(brblock1);
                                        all_bb.erase(brblock2);

                                        for(auto &brb1i : *brblock1)
                                        {
                                            if(auto sti = dyn_cast<llvm::StoreInst>(&brb1i)) {
                                                Value *storevalue = sti->getValueOperand();
                                                bool isBit = false;
                                                if(auto andor = dyn_cast<llvm::Instruction>(storevalue))
                                                {
                                                    isBit = MountOptFieldIsOneBit01(srcfilename, sti);
                                                    if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                                    {
                                                        //outs() << "find and or store in branch of" << parseF->getName() << ": " << *sti << "\n";
                                                        BinaryOperator* binOp = dyn_cast<BinaryOperator>(andor);
                                                        for(int i = 0; i < binOp->getNumOperands(); i++)
                                                        {
                                                            ConstantInt* constantInt = dyn_cast<ConstantInt>(binOp->getOperand(i));
                                                            if(constantInt == nullptr)
                                                            continue;
                                                            // tmp += " " + to_string(constantInt->getZExtValue());
                                                            if(andor->getOpcode() == Instruction::And) 
                                                            {
                                                                if(isBit) {
                                                                    configtype = "bitfieldclear";
                                                                    uint64_t tmp = ~(constantInt->getSExtValue());
                                                                    int tmpe = findExponentOfTwo(tmp);
                                                                    if(tmpe == -1) continue;
                                                                    flagcollect = tmpe;
                                                                } else {
                                                                    configtype = "clear";
                                                                    flagcollect &= ~(constantInt->getSExtValue());
                                                                }
                                                            }
                                                            else
                                                            {
                                                                if(isBit) {
                                                                    configtype = "bitfieldset";
                                                                    uint64_t tmp = constantInt->getZExtValue();
                                                                    int tmpe = findExponentOfTwo(tmp);
                                                                    if(tmpe == -1) continue;
                                                                    flagcollect = tmpe;
                                                                } else {
                                                                    configtype = "set";
                                                                    flagcollect &= constantInt->getZExtValue();
                                                                }
                                                            }
                                                            
                                                            getflag = true;
                                                        }
                                                    }
                                                }
                                                else if(auto storeconst = dyn_cast<ConstantInt>(storevalue)) {
                                                    uint32_t storeint = storeconst->getZExtValue();
                                                    if(storeint == 1) {
                                                        configtype = "assigntrue";
                                                        flagcollect = 0xfffffff1;
                                                        getflag = true;
                                                    } 
                                                    else if(storeint == 0) {
                                                        configtype = "assignfalse";
                                                        flagcollect = 0xfffffff0;
                                                        getflag = true;
                                                    }
                                                }
                                                if(getflag)
                                                {
                                                    Value* flagtarget = sti->getPointerOperand();
                                                    if(isBit) {
                                                        if(dyn_cast<BitCastInst>(flagtarget)) {
                                                            BitCastInst* bcifromgep = dyn_cast<BitCastInst>(flagtarget);
                                                            flagtarget = bcifromgep->getOperand(0);
                                                        }
                                                    }
                                                    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(flagtarget);
                                                    if(!GEP) {
                                                        getflag = false;
                                                        continue;
        
                                                    }
                                                    Type *flagPTy = GEP->getPointerOperand()->getType();
                                                    Type *flagTy = flagPTy->getPointerElementType();
                                                    if (flagTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                                    {
                                                        auto offsetVal = GEP->getOperand(2);
                                                        auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                        int offsetinst = offsetInt->getZExtValue();
                                                        string flagtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                        if(isBit) {
                                                            flagtost = flagtost + ":" + std::to_string(flagcollect);
                                                        }
                                                        if((configtype == "set" || configtype == "clear") && !is_power_of_2(flagcollect)) {
                                                            vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(flagcollect);
                                                            for(uint32_t splitflag : splitflagcollect) {
                                                                res[flagtost].insert(std::make_pair(std::make_pair(splitflag, configtype), std::make_pair(cmd_value, -2)));
                                                            }
                                                        }
                                                        res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, configtype), std::make_pair(cmd_value, -2)));
                                                        string tost = GEP->getSourceElementType()->getStructName().str();
                                                        if(relatedSt.find(tost) == relatedSt.end()) {
                                                            findAllRelatedSt(GEP, relatedSt);
                                                        }
                                                    }
                                                    getflag = false;
                                                }
                                            }
                                            /*else if(auto calli = dyn_cast<llvm::CallInst>(&brb1i)) {
                                                auto setorclearFunc=calli->getCalledFunction();
                                                if(setorclearFunc && (setorclearFunc->getName().str() == "set_bit" || setorclearFunc->getName().str() == "clear_bit")) {
                                                    ConstantInt* constantInt = dyn_cast<ConstantInt>(calli->getOperand(1));
                                                    if(constantInt != nullptr) {
                                                        flagcollect &= constantInt->getZExtValue();
                                                        getflag = true;
                                                    }
                                                }
                                            }*/
                                        }
                                        for(auto &brb2i : *brblock2)
                                        {
                                            if(auto sti = dyn_cast<llvm::StoreInst>(&brb2i)) {
                                                Value *storevalue = sti->getValueOperand();
                                                bool isBit = false;
                                                if(auto andor = dyn_cast<llvm::Instruction>(storevalue))
                                                {
                                                    isBit = MountOptFieldIsOneBit01(srcfilename, sti);
                                                    if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                                    {
                                                        BinaryOperator* binOp = dyn_cast<BinaryOperator>(andor);
                                                        for(int i = 0; i < binOp->getNumOperands(); i++)
                                                        {
                                                            ConstantInt* constantInt = dyn_cast<ConstantInt>(binOp->getOperand(i));
                                                            if(constantInt == nullptr)
                                                            continue;
                                                            // tmp += " " + to_string(constantInt->getZExtValue());
                                                            if(andor->getOpcode() == Instruction::And) 
                                                            {
                                                                if(isBit) {
                                                                    configtype = "bitfieldclear";
                                                                    uint64_t tmp = ~(constantInt->getSExtValue());
                                                                    int tmpe = findExponentOfTwo(tmp);
                                                                    if(tmpe == -1) continue;
                                                                    flagcollect = tmpe;
                                                                } else {
                                                                    configtype = "clear";
                                                                    flagcollect &= ~(constantInt->getSExtValue());
                                                                }
                                                            }
                                                            else
                                                            {
                                                                if(isBit) {
                                                                    configtype = "bitfieldset";
                                                                    uint64_t tmp = constantInt->getZExtValue();
                                                                    int tmpe = findExponentOfTwo(tmp);
                                                                    if(tmpe == -1) continue;
                                                                    flagcollect = tmpe;
                                                                } else {
                                                                    configtype = "set";
                                                                    flagcollect &= constantInt->getZExtValue();
                                                                }
                                                            }
                                                            
                                                            getflag = true;
                                                        }
                                                    }
                                                }
                                                else if(auto storeconst = dyn_cast<ConstantInt>(storevalue)) {
                                                    uint32_t storeint = storeconst->getZExtValue();
                                                    if(storeint == 1) {
                                                        configtype = "assigntrue";
                                                        flagcollect = 0xfffffff1;
                                                        getflag = true;
                                                    } 
                                                    else if(storeint == 0) {
                                                        configtype = "assignfalse";
                                                        flagcollect = 0xfffffff0;
                                                        getflag = true;
                                                    }
                                                }
                                                if(getflag)
                                                {
                                                    Value* flagtarget = sti->getPointerOperand();
                                                    if(isBit) {
                                                        if(dyn_cast<BitCastInst>(flagtarget)) {
                                                            BitCastInst* bcifromgep = dyn_cast<BitCastInst>(flagtarget);
                                                            flagtarget = bcifromgep->getOperand(0);
                                                        }
                                                    }
                                                    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(flagtarget);
                                                    if(!GEP) {
                                                        getflag = false;
                                                        continue;
        
                                                    }
                                                    Type *flagPTy = GEP->getPointerOperand()->getType();
                                                    Type *flagTy = flagPTy->getPointerElementType();
                                                    if (flagTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                                    {
                                                        auto offsetVal = GEP->getOperand(2);
                                                        auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                        int offsetinst = offsetInt->getZExtValue();
                                                        string flagtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                        if(isBit) {
                                                            flagtost = flagtost + ":" + std::to_string(flagcollect);
                                                        }
                                                        if((configtype == "set" || configtype == "clear") && !is_power_of_2(flagcollect)) {
                                                            vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(flagcollect);
                                                            for(uint32_t splitflag : splitflagcollect) {
                                                                res[flagtost].insert(std::make_pair(std::make_pair(splitflag, configtype), std::make_pair(cmd_value, -3)));
                                                            }
                                                        }
                                                        res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, configtype), std::make_pair(cmd_value, -3)));
                                                        string tost = GEP->getSourceElementType()->getStructName().str();
                                                        if(relatedSt.find(tost) == relatedSt.end()) {
                                                            findAllRelatedSt(GEP, relatedSt);
                                                        }
                                                    }
                                                    getflag = false;
                                                }
                                            }
                                            /*else if(auto calli = dyn_cast<llvm::CallInst>(&brb2i)) {
                                                auto setorclearFunc=calli->getCalledFunction();
                                                if(setorclearFunc && (setorclearFunc->getName().str() == "set_bit" || setorclearFunc->getName().str() == "clear_bit")) {
                                                    ConstantInt* constantInt = dyn_cast<ConstantInt>(calli->getOperand(1));
                                                    if(constantInt != nullptr) {
                                                        flagcollect &= constantInt->getZExtValue();
                                                        getflag = true;
                                                    }
                                                }
                                            }*/
                                        }
                                        // strcmp-based enum chain detection (e.g. f2fs old API)
                                        /*for (auto &ei : *sb) {
                                            if (BranchInst* bi = dyn_cast<BranchInst>(&ei)) {
                                                if (isStrcmpBranch(bi)) {
                                                    traceStrcmpEnumChain(bi, cmd_value, res);
                                                    break;
                                                }
                                            }
                                        } */
                                    }
                                }
                            }
                            else
                            {
                                for(auto &i : *sb)
                                {
                                    if(auto sti = dyn_cast<llvm::StoreInst>(&i)) {
                                        string configtype = "";
                                        Value *storevalue = sti->getValueOperand();
                                        bool isBit = false;
                                        if(auto andor = dyn_cast<llvm::Instruction>(storevalue))
                                        {
                                            isBit = MountOptFieldIsOneBit01(srcfilename, sti);
                                            if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                            {
                                                BinaryOperator* binOp = dyn_cast<BinaryOperator>(andor);
                                                for(int i = 0; i < binOp->getNumOperands(); i++)
                                                {
                                                    ConstantInt* constantInt = dyn_cast<ConstantInt>(binOp->getOperand(i));
                                                    if(constantInt == nullptr)
                                                    continue;
                                                    // tmp += " " + to_string(constantInt->getZExtValue());
                                                    if(andor->getOpcode() == Instruction::And) 
                                                        {
                                                            if(isBit) {
                                                                configtype = "bitfieldclear";
                                                                uint64_t tmp = ~(constantInt->getSExtValue());
                                                                int tmpe = findExponentOfTwo(tmp);
                                                                if(tmpe == -1) continue;
                                                                flagcollect = tmpe;
                                                            } else {
                                                                configtype = "clear";
                                                                flagcollect &= ~(constantInt->getSExtValue());
                                                            }
                                                        }
                                                        else
                                                        {
                                                            if(isBit) {
                                                                configtype = "bitfieldset";
                                                                uint64_t tmp = constantInt->getZExtValue();
                                                                int tmpe = findExponentOfTwo(tmp);
                                                                if(tmpe == -1) continue;
                                                                flagcollect = tmpe;
                                                            } else {
                                                                configtype = "set";
                                                                flagcollect &= constantInt->getZExtValue();
                                                            }
                                                        }
                                                     
                                                    getflag = true;
                                                }
                                            }
                                        }
                                        else if(auto storeconst = dyn_cast<ConstantInt>(storevalue)) {
                                            uint32_t storeint = storeconst->getZExtValue();
                                            if(storeint == 1) {
                                                configtype = "assigntrue";
                                                flagcollect = 0xfffffff1;
                                                getflag = true;
                                            } 
                                            else if(storeint == 0) {
                                                configtype = "assignfalse";
                                                flagcollect = 0xfffffff0;
                                                getflag = true;
                                            }
                                        }
                                        if(getflag)
                                        {
                                            Value* flagtarget = sti->getPointerOperand();
                                            //outs() << "get flag in " << parseF->getName() << ": " << *flagtarget << "\n";
                                            if(isBit) {
                                                if(dyn_cast<BitCastInst>(flagtarget)) {
                                                    BitCastInst* bcifromgep = dyn_cast<BitCastInst>(flagtarget);
                                                    flagtarget = bcifromgep->getOperand(0);
                                                }
                                            }
                                            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(flagtarget);
                                            if(!GEP) {
                                                getflag = false;
                                                continue;

                                            }
                                            Type *flagPTy = GEP->getPointerOperand()->getType();
                                            Type *flagTy = flagPTy->getPointerElementType();
                                            if (flagTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                            {
                                                auto offsetVal = GEP->getOperand(2);
                                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                int offsetinst = offsetInt->getZExtValue();
                                                string flagtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                if(isBit) {
                                                    flagtost = flagtost + ":" + std::to_string(flagcollect);
                                                }
                                                if((configtype == "set" || configtype == "clear") && !is_power_of_2(flagcollect)) {
                                                    vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(flagcollect);
                                                    for(uint32_t splitflag : splitflagcollect) {
                                                        res[flagtost].insert(std::make_pair(std::make_pair(splitflag, configtype), std::make_pair(cmd_value, -1)));
                                                    }
                                                }
                                                res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, configtype), std::make_pair(cmd_value, -1)));
                                                string tost = GEP->getSourceElementType()->getStructName().str();
                                                if(relatedSt.find(tost) == relatedSt.end()) {
                                                    findAllRelatedSt(GEP, relatedSt);
                                                }
                                            }
                                            getflag = false;
                                        }
                                    }
                                    /*else if(auto calli = dyn_cast<llvm::CallInst>(&i)) {
                                        auto setorclearFunc=calli->getCalledFunction();
                                        if(setorclearFunc && (setorclearFunc->getName().str() == "set_bit" || setorclearFunc->getName().str() == "clear_bit")) {
                                            ConstantInt* constantInt = dyn_cast<ConstantInt>(calli->getOperand(1));
                                            if(constantInt != nullptr) {
                                                flagcollect &= constantInt->getZExtValue();
                                                getflag = true;
                                            }
                                        }
                                    }*/
                                }
                            }
                        }
                        else if(enumoptnum.find(cmd_value) != enumoptnum.end())
                        {
                            uint32_t flagcollect = 0xffffffff;
                            bool getflag = false;
                            for(auto &i : *sb)
                            {
                                if(auto sti = dyn_cast<llvm::StoreInst>(&i)) {
                                    Value *storevalue = sti->getValueOperand();
                                    if(auto andor = dyn_cast<llvm::Instruction>(storevalue) && ParseResultIsInteger(storevalue))
                                    {
                                        Value* enumtarget = sti->getPointerOperand();
                                        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(enumtarget);
                                        if(!GEP) continue;
                                        Type *enumPTy = GEP->getPointerOperand()->getType();
		                                Type *enumTy = enumPTy->getPointerElementType();
                                        if (enumTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                        {
                                            auto offsetVal = GEP->getOperand(2);
                                            auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                            int offsetinst = offsetInt->getZExtValue();
                                            string enumtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                            res[enumtost].insert(std::make_pair(std::make_pair(0xffffffff, "assignenum"), std::make_pair(cmd_value, -1)));
                                            string tost = GEP->getSourceElementType()->getStructName().str();
                                            if(relatedSt.find(tost) == relatedSt.end()) {
                                                findAllRelatedSt(GEP, relatedSt);
                                            }
                                        }
                                        
                                    }
                                }
                                else if(auto swti = dyn_cast<llvm::SwitchInst>(&i)) {
                                    string configtype = "";
                                    Value* enumSwitchCond = swti->getCondition();
                                    //if(!ParseResultIsInteger(enumSwitchCond)) continue;
                                    std::map<int, string> enuminttostrpair = enumopttoenum[cmd_value];
                                    if(enuminttostrpair.size() == 0) continue;
                                    for (auto swtis = swti->case_begin(), swtie = swti->case_end(); swtis != swtie; swtis++) {
                                        auto enum_val = swtis->getCaseValue();
                                        auto enumb = swtis->getCaseSuccessor();
                                        all_bb.erase(enumb);
                                        //std::set<llvm::BasicBlock *> visited_in_cmd;
                                        auto enum_value = enum_val->getValue().getZExtValue();
                                        //std::pair<int, string> currenumopt = std::make_pair(enum_value ,enuminttostrpair[enum_value]);
                                        if(enuminttostrpair.find(enum_value) != enuminttostrpair.end()) {
                                            for(auto &i : *enumb) {
                                                if(auto sti = dyn_cast<llvm::StoreInst>(&i)) {
                                                    Value *storevalue = sti->getValueOperand();
                                                    if(auto andor = dyn_cast<llvm::Instruction>(storevalue))
                                                    {
                                                        if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                                        {
                                                            BinaryOperator* binOp = dyn_cast<BinaryOperator>(andor);
                                                            for(int i = 0; i < binOp->getNumOperands(); i++)
                                                            {
                                                                ConstantInt* constantInt = dyn_cast<ConstantInt>(binOp->getOperand(i));
                                                                if(constantInt == nullptr)
                                                                continue;
                                                                // tmp += " " + to_string(constantInt->getZExtValue());
                                                                if(andor->getOpcode() == Instruction::And) 
                                                                {
                                                                    configtype = "enumclear";
                                                                     flagcollect &= ~(constantInt->getZExtValue());
                                                                }
                                                                else
                                                                {
                                                                    configtype = "enumset";
                                                                    flagcollect &= constantInt->getZExtValue();
                                                                }
                                                                 
                                                                getflag = true;
                                                            }
                                                        }
                                                    }
                                                    if(getflag)
                                                    {
                                                        Value* flagtarget = sti->getPointerOperand();
                                                        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(flagtarget);
                                                        if(!GEP) {
                                                            getflag = false;
                                                            continue;
            
                                                        }
                                                        Type *flagPTy = GEP->getPointerOperand()->getType();
                                                        Type *flagTy = flagPTy->getPointerElementType();
                                                        if (flagTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                                        {
                                                            auto offsetVal = GEP->getOperand(2);
                                                            auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                            int offsetinst = offsetInt->getZExtValue();
                                                            string flagtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                            if((configtype == "enumset" || configtype == "enumclear") && !is_power_of_2(flagcollect)) {
                                                                vector<uint32_t> splitflagcollect = splitToPowersOfTwo32bits(flagcollect);
                                                                for(uint32_t splitflag : splitflagcollect) {
                                                                    res[flagtost].insert(std::make_pair(std::make_pair(splitflag, configtype), std::make_pair(cmd_value, enum_value)));
                                                                }
                                                            }
                                                            res[flagtost].insert(std::make_pair(std::make_pair(flagcollect, configtype), std::make_pair(cmd_value, enum_value)));
                                                            string tost = GEP->getSourceElementType()->getStructName().str();
                                                            if(relatedSt.find(tost) == relatedSt.end()) {
                                                                findAllRelatedSt(GEP, relatedSt);
                                                            }
                                                        }
                                                        getflag = false;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else if (intParams.find(cmd_value) != intParams.end()) {
                            // int option: detect stores whose value traces to ParseResultIsInteger
                            for (auto &i : *sb) {
                                if (auto sti = dyn_cast<StoreInst>(&i)) {
                                    Value* storeval = sti->getValueOperand();
                                    if (isa<ConstantInt>(storeval)) continue;
                                    if (auto inst = dyn_cast<Instruction>(storeval))
                                        if (inst->isBinaryOp()) continue;
                                    Value* root = storeval;
                                    while (isa<CastInst>(root))
                                        root = cast<CastInst>(root)->getOperand(0);
                                    while (isa<BinaryOperator>(root))
                                        root = cast<BinaryOperator>(root)->getOperand(0);
                                    if (ParseResultIsInteger(root)) {
                                        Value* ptr = sti->getPointerOperand();
                                        if (BitCastInst* bci = dyn_cast<BitCastInst>(ptr))
                                            ptr = bci->getOperand(0);
                                        if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(ptr)) {
                                            Type* gepTy = gep->getSourceElementType();
                                            if (gepTy->isStructTy() && gep->hasAllConstantIndices() && gep->getNumIndices() == 2) {
                                                int offset = dyn_cast<ConstantInt>(gep->getOperand(2))->getZExtValue();
                                                string fieldKey = gepTy->getStructName().str() + std::to_string(offset);
                                                res[fieldKey].insert({{0xffffffff, "assignint"}, {cmd_value, -5}});
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
    return res;
}

OneLayerPairSet FilesystemExtractorPass::getStFromTrunc(TruncInst* trunci, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& ParamsParse, bool isnobranch)
{
    OneLayerPairSet res;
    bool MaybeBitField = false;
    int BitFieldOff = 0;
    
    // 1. 获取源操作数 (%31)
    Value *sourceValue = trunci->getOperand(0);
        
    // 3. 获取目标类型 (i1)
    Type *destType = trunci->getDestTy();

    uint32_t flagv = 0xfffffff1;
    if(isnobranch) flagv = 0xfffffff0;
                            
    // 4. 判断目标类型是否是 i1
    if (IntegerType *intType = dyn_cast<IntegerType>(destType)) {
        if (intType->getBitWidth() == 1) {
            Value* MaybeLdi = sourceValue;
            Instruction* TruncSrci = dyn_cast<Instruction>(MaybeLdi);
            if(TruncSrci && TruncSrci->getOpcode() == llvm::Instruction::And) {
                MaybeBitField = true;
                MaybeLdi = TruncSrci->getOperand(0);
                Instruction* andi = dyn_cast<Instruction>(MaybeLdi);
                if(andi && andi->getOpcode() == llvm::Instruction::LShr) {
                    ConstantInt* BitLShrConstInt = dyn_cast<ConstantInt>(andi->getOperand(1));
                    if(BitLShrConstInt) {
                        MaybeLdi = andi->getOperand(0);
                        BitFieldOff = BitLShrConstInt->getZExtValue();
                    } 
                }
            }
            if(LoadInst* ldi=dyn_cast<LoadInst>(MaybeLdi)) {
                Value* ldiv = ldi->getPointerOperand();
                Instruction* ldpoi = dyn_cast<Instruction>(ldiv);
                if(ldpoi && ldpoi->getOpcode() == llvm::Instruction::BitCast) {
                    ldiv = ldpoi->getOperand(0);
                    MaybeBitField = true;
                }
                if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(ldiv)) {
                    Type *GepTy = GEP->getPointerOperand()->getType()->getPointerElementType();
		            if(GepTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2) {
                        auto offsetVal = GEP->getOperand(2);
                        auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                        int offsetinst = offsetInt->getZExtValue();
                        string itrunctost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                        if(ParamsParse.find(itrunctost) != ParamsParse.end()) {
                            std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[itrunctost];
                            for(auto &flop: temp) {
                                std::pair<uint32_t, string> flandconf = flop.first;
                                uint32_t flagc = flandconf.first;
                                if(flagc == flagv) {
                                    res.insert(std::make_pair(std::make_pair(itrunctost, flandconf), std::make_pair(std::string(""), (uint64_t)0)));
                                }
                            }
                        }
                        if(MaybeBitField) {
                            itrunctost = itrunctost + ":" + std::to_string(BitFieldOff);
                            if(ParamsParse.find(itrunctost) != ParamsParse.end()) {
                                std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[itrunctost];
                                for(auto &flop: temp) {
                                    std::pair<uint32_t, string> flandconf = flop.first;
                                    uint32_t flagc = flandconf.first;
                                    if(flagc == BitFieldOff) {
                                        res.insert(std::make_pair(std::make_pair(itrunctost, flandconf), std::make_pair(std::string(""), (uint64_t)0)));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return res;
}

OneLayerPairSet FilesystemExtractorPass::getStFromIcmp(ICmpInst* icmp, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& ParamsParse)
{
    OneLayerPairSet res;
    // Get cmp_op string from ICmp predicate for assignint/enum cases
    auto getCmpOp = [](CmpInst::Predicate p) -> string {
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
    };
    string cmpOp = getCmpOp(icmp->getPredicate());

    // For ALL predicates: detect Load(GEP) vs Constant for assignint/enum
    auto *icmpOp1 = icmp->getOperand(0);
    auto *icmpOp2 = icmp->getOperand(1);
    Instruction* cmpI = nullptr;
    ConstantInt* cmpC = nullptr;
    if (dyn_cast<ConstantInt>(icmpOp1) && !dyn_cast<ConstantInt>(icmpOp2)) {
        cmpC = dyn_cast<ConstantInt>(icmpOp1);
        cmpI = dyn_cast<Instruction>(icmpOp2);
    } else if (dyn_cast<ConstantInt>(icmpOp2) && !dyn_cast<ConstantInt>(icmpOp1)) {
        cmpC = dyn_cast<ConstantInt>(icmpOp2);
        cmpI = dyn_cast<Instruction>(icmpOp1);
    }
    if (cmpI && cmpC && cmpI->getOpcode() == llvm::Instruction::Load) {
        LoadInst* ldInt = dyn_cast<LoadInst>(cmpI);
        Value* ldIntPtr = ldInt->getPointerOperand();
        if (BitCastInst* bci = dyn_cast<BitCastInst>(ldIntPtr))
            ldIntPtr = bci->getOperand(0);
        if (GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(ldIntPtr)) {
            Type* gepiTy = gepi->getPointerOperand()->getType()->getPointerElementType();
            if (gepiTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2) {
                int offsetinst = dyn_cast<ConstantInt>(gepi->getOperand(2))->getZExtValue();
                string icmptost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                if (ParamsParse.find(icmptost) != ParamsParse.end()) {
                    std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[icmptost];
                    for (auto &flop: temp) {
                        string cfgty = flop.first.second;
                        if (cfgty == "assignint" || cfgty == "assignenum") {
                            res.insert(std::make_pair(std::make_pair(icmptost, flop.first), std::make_pair(cmpOp, cmpC->getZExtValue())));
                        }
                    }
                }
            }
        }
    }

    if (icmp->isEquality()) {
        bool MaybeBitField = false;
        int BitFieldOff = 0;
        auto *op1 = icmp->getOperand(0);
        auto *op2 = icmp->getOperand(1);
        //llvm::Value *icmp_value = nullptr;
        ConstantInt* cmpInt = nullptr;
        uint32_t cmpintvalue = 1;
        Instruction* opi = nullptr;
        if (dyn_cast<ConstantInt>(op1) && !dyn_cast<ConstantInt>(op2)) {
            cmpInt = dyn_cast<ConstantInt>(op1);
            cmpintvalue = cmpInt->getZExtValue();
            opi = dyn_cast<Instruction>(op2);
                        
        } else if (dyn_cast<ConstantInt>(op2) && !dyn_cast<ConstantInt>(op1)) {
            cmpInt = dyn_cast<ConstantInt>(op2);
            cmpintvalue = cmpInt->getZExtValue();
            opi = dyn_cast<Instruction>(op1);
        } else {
        }
        if(cmpintvalue == 0) {
            if(opi) {
                if(opi->getOpcode() == llvm::Instruction::Load) {
                    //暂时处理不了if里用局部变量的情况。。。情况太复杂了
                }
                set<Instruction*> pendinsts;
                pendinsts.insert(opi);
                if(opi->getOpcode() == llvm::Instruction::Call) {
                    pendinsts.clear();
                    CallInst* ifCall = dyn_cast<CallInst>(opi);
                    pendinsts = TryGetMountOptInIfCall(ifCall);
                }
                for(Instruction* pendinst : pendinsts) {
                    MaybeBitField = false;
                    BitFieldOff = 0;
                    opi = pendinst;
                    if(opi && opi->getOpcode() == llvm::Instruction::ZExt) {
                        opi = dyn_cast<Instruction>(opi->getOperand(0));
                        MaybeBitField = true;
                    }
                    if(opi && opi->getOpcode() == llvm::Instruction::And) {
                        auto *andop1 = opi->getOperand(0);
                        auto *andop2 = opi->getOperand(1);
                        Instruction* andi = nullptr;
                        LoadInst* ldi = nullptr;
                        GetElementPtrInst* gepi = nullptr;
                        uint32_t andv = 0;
                        if(dyn_cast<ConstantInt>(andop1) && !dyn_cast<ConstantInt>(andop2)) {
                            andi = dyn_cast<Instruction>(andop2);
                            auto andInt = dyn_cast<ConstantInt>(andop1);
                            andv = andInt->getZExtValue();
                        } else if(dyn_cast<ConstantInt>(andop2) && !dyn_cast<ConstantInt>(andop1)) {
                            andi = dyn_cast<Instruction>(andop1);
                            auto andInt = dyn_cast<ConstantInt>(andop2);
                            andv = andInt->getZExtValue();
                        }
                        if(andi && andi->getOpcode() == llvm::Instruction::LShr) {
                            ConstantInt* BitLShrConstInt = dyn_cast<ConstantInt>(andi->getOperand(1));
                            if(BitLShrConstInt) {
                                andi = dyn_cast<Instruction>(andi->getOperand(0));
                                BitFieldOff = BitLShrConstInt->getZExtValue();
                                MaybeBitField = true;
                            }
                        }
                        //outs() << "get ICmpInst in " << currentF->getName() << ": " << *icmp << "\n";
                        if(andi && dyn_cast<LoadInst>(andi) && andv != 0) {
                            ldi = dyn_cast<LoadInst>(andi);
                            llvm::Value* ldpo = ldi->getPointerOperand();
                            Instruction* ldpoi = dyn_cast<Instruction>(ldpo);
                            if(ldpoi) {
                                if(ldpoi->getOpcode() == llvm::Instruction::BitCast) {
                                    gepi = dyn_cast<GetElementPtrInst>(ldpoi->getOperand(0));
                                    MaybeBitField = true;
                                }
                                gepi = dyn_cast<GetElementPtrInst>(ldpo);
                                if(gepi) {
                                    Type *gepiPTy = gepi->getPointerOperand()->getType();
                                    Type *gepiTy = gepiPTy->getPointerElementType();
                                    if (gepiTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2) {
                                        auto offsetVal = gepi->getOperand(2);
                                        auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                        int offsetinst = offsetInt->getZExtValue();
                                        string icmptost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                        if(ParamsParse.find(icmptost) != ParamsParse.end()) {
                                            std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[icmptost];
                                            for(auto &flop: temp) {
                                                std::pair<uint32_t, string> flandconf = flop.first;
                                                uint32_t flagc = flandconf.first;
                                                //TODO: 理论上这里我应该要过滤掉assigntrue、assignfalse、assignenum，不过他们的flag值本身也通不过下面这个检查，被自然过滤掉了
                                                if(flagc == andv) {
                                                    res.insert(std::make_pair(std::make_pair(icmptost, flandconf), std::make_pair(std::string(""), (uint64_t)0)));
                                                }
                                            }
                                        }
                                        if(MaybeBitField) {
                                            icmptost = icmptost + ":" + std::to_string(BitFieldOff);
                                            if(ParamsParse.find(icmptost) != ParamsParse.end()) {
                                                std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[icmptost];
                                                for(auto &flop: temp) {
                                                    std::pair<uint32_t, string> flandconf = flop.first;
                                                    uint32_t flagc = flandconf.first;
                                                    if(flagc == andv) {
                                                        res.insert(std::make_pair(std::make_pair(icmptost, flandconf), std::make_pair(std::string(""), (uint64_t)0)));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } 
                        }
                    }
                } 
            }
        } else {
            // cmpintvalue != 0: examine struct field pattern
            if(opi) {
                // Existing bitmask pattern: (flags & MASK) == CONST
                if(opi->getOpcode() == llvm::Instruction::And) {
                    auto *andop1 = opi->getOperand(0);
                    auto *andop2 = opi->getOperand(1);
                    Instruction* andi = nullptr;
                    LoadInst* ldi = nullptr;
                    GetElementPtrInst* gepi = nullptr;
                    uint32_t andv = 0;
                    if(dyn_cast<ConstantInt>(andop1) && !dyn_cast<ConstantInt>(andop2)) {
                        andi = dyn_cast<Instruction>(andop2);
                        auto andInt = dyn_cast<ConstantInt>(andop1);
                        andv = andInt->getZExtValue();
                    } else if(dyn_cast<ConstantInt>(andop2) && !dyn_cast<ConstantInt>(andop1)) {
                        andi = dyn_cast<Instruction>(andop1);
                        auto andInt = dyn_cast<ConstantInt>(andop2);
                        andv = andInt->getZExtValue();
                    }
                    if(andi && dyn_cast<LoadInst>(andi) && andv != 0) {
                        ldi = dyn_cast<LoadInst>(andi);
                        llvm::Value* ldpo = ldi->getPointerOperand();
                        Instruction* ldpoi = dyn_cast<Instruction>(ldpo);
                        if(ldpoi) {
                            gepi = dyn_cast<GetElementPtrInst>(ldpo);
                            if(gepi) {
                                Type *gepiPTy = gepi->getPointerOperand()->getType();
                                Type *gepiTy = gepiPTy->getPointerElementType();
                                if(gepiTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2) {
                                    auto offsetVal = gepi->getOperand(2);
                                    auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                    int offsetinst = offsetInt->getZExtValue();
                                    string icmptost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                    if(ParamsParse.find(icmptost) != ParamsParse.end()) {
                                        std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[icmptost];
                                        for(auto &flop: temp) {
                                            std::pair<uint32_t, string> flandconf = flop.first;
                                            uint32_t flagc = flandconf.first;
                                            string cfgty = flandconf.second;
                                            std::pair<int, int> optandty = flop.second;
                                            int optnum1 = optandty.first;
                                            if(flagc == cmpintvalue && (cfgty == "set" || cfgty == "enumset")) {
                                                for(auto & flop2 : temp) {
                                                    std::pair<uint32_t, string> flandconf2 = flop2.first;
                                                    uint32_t flagc2 = flandconf2.first;
                                                    string cfgty2 = flandconf2.second;
                                                    std::pair<int, int> optandty2 = flop2.second;
                                                    int optnum2 = optandty2.first;
                                                    if(flagc2 == andv && optnum2 == optnum1 && (cfgty == "clear" || cfgty == "enumclear")) {
                                                        res.insert(std::make_pair(std::make_pair(icmptost, flandconf), std::make_pair(std::string(""), (uint64_t)0)));
                                                    }
                                                }
                                            }
                                            // assignint / assignenum: Load(GEP) & MASK == CONST
                                            if((cfgty == "assignint" || cfgty == "assignenum") && flagc == 0xffffffff) {
                                                res.insert(std::make_pair(std::make_pair(icmptost, flandconf), std::make_pair(cmpOp, (uint64_t)cmpintvalue)));
                                            }
                                        }
                                    }
                                }
                            } 
                        } 
                    }
                }
            }
        }
    }
    return res;
}

void TryOneBitfieldStore(StoreInst* sti, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& ParamsParse, std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet>& res)
{
    Value* StPValue = sti->getPointerOperand();
    Value* StValue = sti->getValueOperand();
    Type* StPType = StPValue->getType();
    GetElementPtrInst* toGep = dyn_cast<GetElementPtrInst>(StPValue);
    if(!toGep) {
        return;
    }
    Type *toGepTy = toGep->getPointerOperand()->getType()->getPointerElementType();
    if(!toGepTy->isStructTy() || !toGep->hasAllConstantIndices() || toGep->getNumIndices() != 2) {
        return;
    }
    Instruction* OrInst = dyn_cast<Instruction>(StValue);
    if(!OrInst || OrInst->getOpcode() != llvm::Instruction::Or) {
        return;
    }
    Instruction* toandi = dyn_cast<Instruction>(OrInst->getOperand(0));
    if(!toandi || toandi->getOpcode() != llvm::Instruction::And) {
        return;
    }
    Instruction* ShlInst = dyn_cast<Instruction>(OrInst->getOperand(1));
    if(!ShlInst || ShlInst->getOpcode() != llvm::Instruction::Shl) {
        return;
    }
    ConstantInt* ShlConst = dyn_cast<ConstantInt>(ShlInst->getOperand(1));
    if(!ShlConst) {
        return;
    }
    Instruction* fromandi = dyn_cast<Instruction>(ShlInst->getOperand(0));
    if(!fromandi || fromandi->getOpcode() != llvm::Instruction::And) {
        return;
    }
    ConstantInt* fromAndConst = dyn_cast<ConstantInt>(fromandi->getOperand(1));
    if(!fromAndConst || fromAndConst->getZExtValue() != 1) {
        return;
    }
    Instruction* LShrInst = dyn_cast<Instruction>(fromandi->getOperand(0));
    if(!LShrInst || LShrInst->getOpcode() != llvm::Instruction::LShr) {
        return;
    }
    ConstantInt* LShrConst = dyn_cast<ConstantInt>(LShrInst->getOperand(1));
    if(!LShrConst) {
        return;
    }
    LoadInst* fromload = dyn_cast<LoadInst>(LShrInst->getOperand(0));
    if(!fromload) {
        return;
    }
    GetElementPtrInst* fromGep = dyn_cast<GetElementPtrInst>(fromload->getPointerOperand());
    if(!fromGep) {
        return;
    }
    Type *fromGepTy = fromGep->getPointerOperand()->getType()->getPointerElementType();
    if(!fromGepTy->isStructTy() || !fromGep->hasAllConstantIndices() || fromGep->getNumIndices() != 2) {
        return;
    }
    ConstantInt* toandConst = dyn_cast<ConstantInt>(toandi->getOperand(1));
    if(!toandConst) {
        return;
    }
    LoadInst* toload = dyn_cast<LoadInst>(toandi->getOperand(0));
    if(!toload) {
        return;
    }
    Value* toloadv = toload->getPointerOperand();
    if(toloadv != StPValue) {
        return;
    }

    auto fromoffsetVal = fromGep->getOperand(2);
    auto fromoffsetInt = dyn_cast<ConstantInt>(fromoffsetVal);
    int fromoffsetinst = fromoffsetInt->getZExtValue();
    int frombitfieldoff = LShrConst->getZExtValue();
    string fromtost = fromGep->getSourceElementType()->getStructName().str() + std::to_string(fromoffsetinst) + ":" + std::to_string(frombitfieldoff);
    if(ParamsParse.find(fromtost) != ParamsParse.end()) {
        auto tooffsetVal = toGep->getOperand(2);
        auto tooffsetInt = dyn_cast<ConstantInt>(tooffsetVal);
        int tooffsetinst = tooffsetInt->getZExtValue();
        int tobitfieldoff = ShlConst->getZExtValue();
        string totost = toGep->getSourceElementType()->getStructName().str() + std::to_string(tooffsetinst) + ":" + std::to_string(tobitfieldoff);
        std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[fromtost];
        for(auto& flagtoopt : temp) {
            std::pair<uint32_t, string> flagcc = flagtoopt.first;
            uint32_t flagc = flagcc.first;
            string cfgtype = flagcc.second;
            res[std::make_pair(totost, std::make_pair(flagc, cfgtype))].insert(std::make_pair(std::make_pair(fromtost, flagcc), std::make_pair(std::string(""), (uint64_t)0)));
        }
    }
}

std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> FilesystemExtractorPass::collectOneLayerParamsProp(llvm::Function* currentF, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> ParamsParse)
{
    std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> res;
    std::set<llvm::BasicBlock *> all_bb;
    //llvm::DominatorTree *DT = new llvm::DominatorTree(*currentF);
    //bool getcmpzero = false;
    for (auto &bb : *currentF) {
        all_bb.insert(&bb);
    }
    while (!all_bb.empty())
    {
        OneLayerPairSet currStAndConst;
        auto bb = *all_bb.begin();
        all_bb.erase(bb);
        for (auto &i : *bb)
        {
            switch (i.getOpcode())
            {
                case llvm::Instruction::Store: {
                    auto sti = llvm::dyn_cast<llvm::StoreInst>(&i);
                    Value* StPValue = sti->getPointerOperand();
                    Value* StValue = sti->getValueOperand();
                    Type* StPType = StPValue->getType();
                    set<GetElementPtrInst*> toGeps;
                    /*while (StPType->isPointerTy()) {
                        StPType = StPType->getPointerElementType();
                    }
                    if (!StPType->isStructTy()) {
                        continue;

                    }*/
                    //string stpstr = StPType->getStructName().str();
                    if(Instruction* StValueInst = dyn_cast<Instruction>(StValue)) {
                        if(StValueInst->getOpcode() == llvm::Instruction::Or) {
                            TryOneBitfieldStore(sti, ParamsParse, res);
                            continue;
                        }
                    }
                    if(dyn_cast<TruncInst>(StValue)) {
                       Instruction* StCastI =  dyn_cast<Instruction>(StValue);
                       StValue = StCastI->getOperand(0);
                       if(!StValue) continue;
                    }
                    if(!dyn_cast<LoadInst>(StValue)) continue;
                    LoadInst* Ldi = dyn_cast<LoadInst>(StValue);
                    Value* LdPValue = Ldi->getPointerOperand();
                    if(!dyn_cast<GetElementPtrInst>(LdPValue)) continue;
                    if(!dyn_cast<GetElementPtrInst>(StPValue)) {
                        if(dyn_cast<AllocaInst>(StPValue)) {
                            AllocaInst* SttoLocal = dyn_cast<AllocaInst>(StPValue);
                            if(SttoLocal->getAllocatedType()->isIntegerTy()) {
                                for(User *us : StPValue->users()) {
                                    if(dyn_cast<LoadInst>(us)) {
                                        //LoadInst* ldarg = dyn_cast<LoadInst>(ArgU);
                                        Value* ldv = dyn_cast<Value>(us);
                                        for(User *ArgvU: ldv->users()) {
                                            if(dyn_cast<StoreInst>(ArgvU)) {
                                                StoreInst* StToGEP = dyn_cast<StoreInst>(ArgvU);
                                                Value* StToGEPv = StToGEP->getValueOperand();
                                                if(StToGEPv != ldv) continue;
                                                Value* StToGEPp = StToGEP->getPointerOperand();
                                                if(dyn_cast<GetElementPtrInst>(StToGEPp)) {
                                                    GetElementPtrInst* toGep = dyn_cast<GetElementPtrInst>(StToGEPp);
                                                    toGeps.insert(toGep);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    else {
                        GetElementPtrInst* toGep = dyn_cast<GetElementPtrInst>(StPValue);
                        toGeps.insert(toGep);
                    }
                    if(toGeps.empty()) continue;
                    GetElementPtrInst* fromGep = dyn_cast<GetElementPtrInst>(LdPValue);
                    //GetElementPtrInst* toGep = dyn_cast<GetElementPtrInst>(StPValue);

                    Type *fromGepTy = fromGep->getPointerOperand()->getType()->getPointerElementType();
		            if(fromGepTy->isStructTy() && fromGep->hasAllConstantIndices() && fromGep->getNumIndices() == 2) {
                        auto fromoffsetVal = fromGep->getOperand(2);
                        auto fromoffsetInt = dyn_cast<ConstantInt>(fromoffsetVal);
                        int fromoffsetinst = fromoffsetInt->getZExtValue();
                        string fromtost = fromGep->getSourceElementType()->getStructName().str() + std::to_string(fromoffsetinst);
                        if(ParamsParse.find(fromtost) != ParamsParse.end()) {
                            for(auto& togepi : toGeps) {
                                Type *toGepTy = togepi->getPointerOperand()->getType()->getPointerElementType();
                                if(toGepTy->isStructTy() && togepi->hasAllConstantIndices() && togepi->getNumIndices() == 2) {
                                    auto tooffsetVal = togepi->getOperand(2);
                                    auto tooffsetInt = dyn_cast<ConstantInt>(tooffsetVal);
                                    int tooffsetinst = tooffsetInt->getZExtValue();
                                    string totost = togepi->getSourceElementType()->getStructName().str() + std::to_string(tooffsetinst);
                                    std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> temp = ParamsParse[fromtost];
                                    for(auto& flagtoopt : temp) {
                                        std::pair<uint32_t, string> flagcc = flagtoopt.first;
                                        uint32_t flagc = flagcc.first;
                                        string cfgtype = flagcc.second;
                                        res[std::make_pair(totost, std::make_pair(flagc, cfgtype))].insert(std::make_pair(std::make_pair(fromtost, flagcc), std::make_pair(std::string(""), (uint64_t)0)));
                                    }
                                }
                            } 
                        }
                    }
                    break;
                }
                case llvm::Instruction::Trunc: {
                    break;
                }
                case llvm::Instruction::ICmp: {
                    //auto icmp = llvm::dyn_cast<llvm::ICmpInst>(&i);
                    break;
                }
                case llvm::Instruction::Br: {
                    
                    auto bi = llvm::dyn_cast<llvm::BranchInst>(&i);
                    if(bi->getNumSuccessors() != 2 || bi->isUnconditional()) {
                        //getcmpzero = false;
                        currStAndConst.clear();
                        break;
                    }
                    //Value* condv = bi->getCondition();
                    Instruction* BICondI = dyn_cast<Instruction>(bi->getCondition());
                    set<Instruction*> pendinsts;
                    if(BICondI) {
                        pendinsts.insert(BICondI);
                    }
                    if(BICondI && dyn_cast<CallInst>(BICondI)) {
                        pendinsts.clear();
                        CallInst* BICondCall = dyn_cast<CallInst>(BICondI);
                        pendinsts = TryGetMountOptInIfCall(BICondCall);
                    }
                    for(Instruction* pendinst : pendinsts) {
                        BICondI = pendinst;
                        if(BICondI && dyn_cast<TruncInst>(BICondI)) {
                            //getcmpzero = false;
                            currStAndConst.clear();
                            bool tisno;
                            auto sb0t = bi->getSuccessor(0);
                            auto sb1t = bi->getSuccessor(1);
                            int sb0tidx = getBasicBlockIndex(sb0t);
                            int sb1tidx = getBasicBlockIndex(sb1t);
                            if (sb0tidx < sb1tidx) {
                                tisno = false;
                            } else {
                                tisno = true;
                            }
                            string b0name = "";
                            string b1name = "";
                            if(sb0t->hasName()) b0name = sb0t->getName().str();
                            if(sb1t->hasName()) b1name = sb1t->getName().str();
                            if(b0name.find(".then") != std::string::npos || b0name.find(".true") != std::string::npos || b1name.find(".false") != std::string::npos) {
                                tisno = false;
                            } else if (b0name.find(".false") != std::string::npos || b1name.find(".true") != std::string::npos || b1name.find(".then") != std::string::npos)
                            {
                                tisno = true;
                            }
                            auto trunci = dyn_cast<TruncInst>(BICondI);
                            currStAndConst = getStFromTrunc(trunci, ParamsParse, tisno);
                            if(currStAndConst.size() == 0) {
                                continue;
                            } else {
                                //outs() << "get matched truncinst in " << currentF->getName() << ": " << *trunci << "\n";
                            }
                        } else if(BICondI && dyn_cast<ICmpInst>(BICondI)) {
                            //getcmpzero = false;
                            currStAndConst.clear();
                            ICmpInst* icmp = dyn_cast<ICmpInst>(BICondI);
                            currStAndConst = getStFromIcmp(icmp, ParamsParse);
                            if(currStAndConst.size() == 0) {
                                continue;
                            }
                            //if(getcmpzero == false) break;
                        } else {
                            currStAndConst.clear();
                            continue;
                        }
                        bool isno;
                        BasicBlock* sb = nullptr;
                        //outs() << "get BranchInst in " << currentF->getName() << ": " << *bi << "\n";
                        auto sb0 = bi->getSuccessor(0);
                        auto sb1 = bi->getSuccessor(1);
                        int sb0idx = getBasicBlockIndex(sb0);
                        int sb1idx = getBasicBlockIndex(sb1);
                        if (sb0idx < sb1idx) {
                            isno = false;
                            sb = sb0;
                        } else {
                            isno = true;
                            sb = sb1;
                        }
                        string b0name = "";
                        string b1name = "";
                        if(sb0->hasName()) b0name = sb0->getName().str();
                        if(sb1->hasName()) b1name = sb1->getName().str();
                        if(b0name.find(".then") != std::string::npos || b0name.find(".true") != std::string::npos || b1name.find(".false") != std::string::npos) {
                            isno = false;
                            sb = sb0;
                        } else if (b0name.find(".false") != std::string::npos || b1name.find(".true") != std::string::npos || b1name.find(".then") != std::string::npos)
                        {
                            sb = sb1;
                            isno = true;
                        }
                        //getcmpzero = false;
                        
                        /*if (llvm::isPotentiallyReachable(sb0, sb1, nullptr, DT)) {
                            sb = sb0;
                        } else {
                            sb = sb1;
                        }*/
                        //uint32_t flagcollect = 0xffffffff;
                        bool getflag = false;
                        all_bb.erase(sb);
                        for(auto &i : *sb)
                        {
                            uint32_t flagcollect = 0xffffffff;
                            string cfgtype = "";
                            if(auto sti = dyn_cast<llvm::StoreInst>(&i)) {
                                Value *storevalue = sti->getValueOperand();
                                if(auto andor = dyn_cast<llvm::Instruction>(storevalue))
                                {
                                    //TODO: 先不处理and的情况，之后再加上；其它部分使用onelayer时，可能也没写对于and做clear的情况要怎么使用，需要补上
                                    //if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                    if(andor->getOpcode() == Instruction::And || andor->getOpcode() == Instruction::Or)
                                    {
                                        BinaryOperator* binOp = dyn_cast<BinaryOperator>(andor);
                                        for(int i = 0; i < binOp->getNumOperands(); i++)
                                        {
                                            ConstantInt* constantInt = dyn_cast<ConstantInt>(binOp->getOperand(i));
                                            if(constantInt == nullptr)
                                            continue;
                                            // tmp += " " + to_string(constantInt->getZExtValue());
                                            if(andor->getOpcode() == Instruction::And) 
                                            {
                                                cfgtype = "clear";
                                                flagcollect &= ~(constantInt->getZExtValue());
                                            }
                                            else if (andor->getOpcode() == Instruction::Or)
                                            {
                                                cfgtype = "set";
                                                flagcollect &= constantInt->getZExtValue();
                                            }
                                                         
                                            getflag = true;
                                        }
                                    }
                                }
                                else if(auto storeconst = dyn_cast<ConstantInt>(storevalue)) {
                                    uint32_t storeint = storeconst->getZExtValue();
                                    Value* storePoint = sti->getPointerOperand();
                                    bool isret = false;
                                    if(storePoint->hasName() && storePoint->getName().str() == "retval") {
                                        isret = true;
                                    }
                                    if(storeint == 1) {
                                        if(isret) {
                                            cfgtype = "functionrettrue";
                                            flagcollect = 0xfffffff1;
                                            for(auto& stcon: currStAndConst) {
                                                auto& innerP = stcon.first;
                                                string configtype = innerP.second.second;
                                                if(isno) {
                                                    if(configtype == "set" || configtype == "enumset" || configtype == "bitfieldset" || configtype == "assigntrue") continue;
                                                } else {
                                                    if(configtype == "clear" || configtype == "enumclear" || configtype == "bitfieldclear" || configtype == "assignfalse") continue;
                                                }
                                                res[std::make_pair(currentF->getName().str() + ":function", std::make_pair(flagcollect, cfgtype))].insert(stcon);
                                            }
                                        }
                                        else {
                                            cfgtype = "assigntrue";
                                            flagcollect = 0xfffffff1;
                                            getflag = true;
                                        }
                                    } 
                                    else if(storeint == 0) {
                                        if(isret) {
                                            cfgtype = "functionretfalse";
                                            flagcollect = 0xfffffff0;
                                            for(auto& stcon: currStAndConst) {
                                                auto& innerP = stcon.first;
                                                string configtype = innerP.second.second;
                                                if(isno) {
                                                    if(configtype == "set" || configtype == "enumset" || configtype == "bitfieldset" || configtype == "assigntrue") continue;
                                                } else {
                                                    if(configtype == "clear" || configtype == "enumclear" || configtype == "bitfieldclear" || configtype == "assignfalse") continue;
                                                }
                                                res[std::make_pair(currentF->getName().str() + ":function", std::make_pair(flagcollect, cfgtype))].insert(stcon);
                                            }
                                        } else {
                                            cfgtype = "assignfalse";
                                            flagcollect = 0xfffffff0;
                                            getflag = true;
                                        }
                                    }
                                }
                                if(getflag)
                                {
                                    Value* flagtarget = sti->getPointerOperand();
                                    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(flagtarget);
                                    if(!GEP) {
                                        getflag = false;
                                        continue;
    
                                    }
                                    Type *flagPTy = GEP->getPointerOperand()->getType();
                                    Type *flagTy = flagPTy->getPointerElementType();
                                    if (flagTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2)
                                    {
                                        auto offsetVal = GEP->getOperand(2);
                                        auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                        int offsetinst = offsetInt->getZExtValue();
                                        string flagtost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                        for(auto& stcon: currStAndConst) {
                                            auto& innerP = stcon.first;
                                            string configtype = innerP.second.second;
                                            if(isno) {
                                                if(configtype == "set" || configtype == "enumset" || configtype == "bitfieldset" || configtype == "assigntrue") continue;
                                            } else {
                                                if(configtype == "clear" || configtype == "enumclear" || configtype == "bitfieldclear" || configtype == "assignfalse") continue;
                                            }
                                            res[std::make_pair(flagtost, std::make_pair(flagcollect, cfgtype))].insert(stcon);
                                        }
                                    }
                                    getflag = false;
                                }
                            } else if(auto calli = dyn_cast<llvm::CallInst>(&i)) {
                                auto setorclearFunc=calli->getCalledFunction();
                                if(setorclearFunc && (setorclearFunc->getName().str() == "set_bit" || setorclearFunc->getName().str() == "clear_bit")) {
                                    //outs() << "get call set_bit or clear_bit in " << currentF->getName() << ": " << *calli << "\n";
                                    ConstantInt* constantInt = dyn_cast<ConstantInt>(calli->getOperand(0));
                                    if(constantInt != nullptr) {
                                        unsigned int bitmaskoff = constantInt->getZExtValue();
                                        flagcollect &= (1UL << bitmaskoff);
                                        GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(calli->getOperand(1));
                                        if(gepi) {
                                            Type *flagPTy = gepi->getPointerOperand()->getType();
                                            Type *flagTy = flagPTy->getPointerElementType();
                                            if (flagTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2)
                                            {
                                                auto offsetVal = gepi->getOperand(2);
                                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                int offsetinst = offsetInt->getZExtValue();
                                                string flagtost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                for(auto& stcon: currStAndConst) {
                                                    auto& innerP = stcon.first;
                                                    string configtype = innerP.second.second;
                                                    if(isno) {
                                                        if(configtype == "set" || configtype == "enumset" || configtype == "bitfieldset" || configtype == "assigntrue") continue;
                                                    } else {
                                                        if(configtype == "clear" || configtype == "enumclear" || configtype == "bitfieldclear" || configtype == "assignfalse") continue;
                                                    }
                                                    if(setorclearFunc->getName().str() == "set_bit") {
                                                        cfgtype = "set";
                                                    } else {
                                                        cfgtype = "clear";
                                                    }
                                                    res[std::make_pair(flagtost, std::make_pair(flagcollect, cfgtype))].insert(stcon);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        
                        /*for ([[maybe_unused]] auto p : predecessors(sb)) {
                          num++;
                        }
                        if (num == 1) {
                          std::set<llvm::BasicBlock *> temp;
                          temp.insert(sb);
                          get_dom_bb(sb, &temp);
                          for (auto temp_b : temp) {
                            if (all_bb.find(temp_b) != all_bb.end()) {
                              all_bb.erase(temp_b);
                            }
                          }
                        }*/
                    }
                    break;
                }
            }
        }
    }
    return res;
}


std::map<std::string, std::set<string>> FilesystemExtractorPass::collectFunctionTableAlloc(Function* InodeInitF, std::map<std::pair<int, std::string>, std::map<int, std::string>> &sigfsparamsenum, std::map<int, string> &sigfsparamsflag, std::map<int, std::pair<std::string, int>> &sigfsparamsint, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> &sigfs2options, std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> &sigfs2options2onelayer) 
{
    outs() << "start analyze old param parse func " << InodeInitF->getName() << ": " << "\n";
    std::map<std::string, std::set<string>> res;
    std::set<llvm::BasicBlock *> all_bb;
    llvm::DominatorTree *DT = new llvm::DominatorTree(*InodeInitF);
    for (auto &bb : *InodeInitF) {
        all_bb.insert(&bb);
    }

    string srcfilename = InodeInitF->getParent()->getSourceFileName();

    while (!all_bb.empty())
    {
        auto bb = *all_bb.begin();
        all_bb.erase(bb);
        for (auto &i : *bb)
        {
            switch (i.getOpcode())
            {
                case llvm::Instruction::Switch: {
                    //outs() << InodeInitF->getName() <<" switch: " << i << "\n";
                    auto si = llvm::dyn_cast<llvm::SwitchInst>(&i);
                    if(!SwitchCondIsFileType(srcfilename, si)) continue;
                    //outs() << "find switch file type in " << InodeInitF->getName() << ": " << *si << "\n";
                    for (auto cis = si->case_begin(), cie = si->case_end(); cis != cie; cis++)
                    {
                        auto cmd_val = cis->getCaseValue();
                        auto sb = cis->getCaseSuccessor();
                        all_bb.erase(sb);
                        //std::set<llvm::BasicBlock *> visited_in_cmd;
                        auto cmd_value = cmd_val->getValue().getZExtValue();
                        if(FileTypeConstToString.find(cmd_value) != FileTypeConstToString.end())
                        {
                            for(auto &ii : *sb)
                            {
                                Instruction *I = &ii;
                                if(I->getOpcode() == Instruction::GetElementPtr)
                                {
                                    GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(I);
                                    if(!gepInst->getSourceElementType()->isStructTy())
                                    {
                                        continue;
                                    }
                                    if(gepInst->getSourceElementType()->getStructName() == "struct.inode" || gepInst->getSourceElementType()->getStructName() == "struct.address_space")
                                    {
                                        Type* gepPointerType = nullptr;
                                        Instruction *gepNext = getNextInstruction(I);
                                        Instruction *nearStore = I;
                                        if(!gepInst->getResultElementType()->isPointerTy())
                                        {
                                            if(!gepNext || !dyn_cast<BitCastInst>(gepNext)) {
                                                continue;
                                            } else {
                                                if(gepNext->getOperand(0) != gepInst) {
                                                    continue;
                                                }
                                                nearStore = gepNext;
                                            }
                                        }
                                        if(!gepInst->getResultElementType()->isPointerTy()) {
                                            if(gepNext && dyn_cast<BitCastInst>(gepNext)) {
                                                BitCastInst* bci = dyn_cast<BitCastInst>(gepNext);
                                                gepPointerType = bci->getDestTy();
                                                while (gepPointerType->isPointerTy()) {
                                                    gepPointerType = gepPointerType->getPointerElementType();
                                                }
                                                if (!gepPointerType->isStructTy()) {
                                                        gepPointerType = nullptr;
                                                }
                                            }
                                        }
                                        else {
                                            gepPointerType = gepInst->getResultElementType()->getPointerElementType();
                                            if(!gepPointerType->isStructTy())
                                            {
                                                gepPointerType = nullptr;
                                            }
                                        }
                                        if(!gepPointerType) continue;
                                        string gepResultType = gepPointerType->getStructName().str();
                                        if(gepResultType == "struct.file_operations" || gepResultType == "struct.inode_operations" || gepResultType == "struct.address_space_operations")
                                        {
                                            for(User* user:nearStore->users())
                                            {
                                                if(StoreInst* storeInst = dyn_cast<StoreInst>(user))
                                                {
                                                    Value* op = storeInst->getValueOperand();
                                                    GlobalVariable* globalVar = dyn_cast<GlobalVariable>(op);
                                                    if(globalVar == nullptr)
                                                    {
                                                        if(BitCastOperator* bitcastOp = dyn_cast<BitCastOperator>(op))
                                                        {
                                                            globalVar = dyn_cast<GlobalVariable>(bitcastOp->getOperand(0));
                                                        }
                                                    }
                                                    if(globalVar != nullptr)
                                                    {
                                                        if(!globalVar->hasInitializer())
                                                        {
                                                            globalVar = getGlobalVaraible(globalVar->getName());
                                                        }
                                                    }
                                                    if(globalVar != nullptr)
                                                    {
                                                        res[globalVar->getName().str()].insert("FileType:" + FileTypeConstToString[cmd_value]);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if(I->getOpcode() == Instruction::Br) {
                                    BranchInst* BI = llvm::dyn_cast<llvm::BranchInst>(I);
                                    if(BI->getNumSuccessors() != 2 || BI->isUnconditional()) continue;
                                    set<pair<string, string>> fsMountConstraintIf;
                                    auto brbb1 = BI->getSuccessor(0);
				                    auto brbb2 = BI->getSuccessor(1);

                                    bool isno;
				                    int brbb1idx = getBasicBlockIndex(brbb1);
                                    int brbb2idx = getBasicBlockIndex(brbb2);
                                    if (brbb1idx < brbb2idx) {
                                        isno = false;
                                    } else {
                                        isno = true;
                                    }
                                    string b1name = "";
                                    string b2name = "";
                                    if(brbb1->hasName()) b1name = brbb1->getName().str();
                                    if(brbb2->hasName()) b2name = brbb2->getName().str();
                                    if(b1name.find(".then") != std::string::npos || b1name.find(".true") != std::string::npos || b2name.find(".false") != std::string::npos) {
                                        isno = false;
                                    } 
                                    else if (b1name.find(".false") != std::string::npos || b2name.find(".true") != std::string::npos || b2name.find(".then") != std::string::npos)
                                    {
                                        isno = true;
                                    }
                                    Instruction* BICondI = dyn_cast<Instruction>(BI->getCondition());
                                    set<Instruction*> pendinsts;
                                    if(BICondI) {
                                        pendinsts.insert(BICondI);
                                    }
                                    if(BICondI && dyn_cast<CallInst>(BICondI)) {
                                        pendinsts.clear();
                                        CallInst* BICondCall = dyn_cast<CallInst>(BICondI);
                                        pendinsts = TryGetMountOptInIfCall(BICondCall);
                                        if(pendinsts.empty()) {
                                            continue;
                                        }
                                    }
                                    for(Instruction* pendinst : pendinsts) {
                                        fsMountConstraintIf.clear();
                                        BICondI = pendinst;
                                        if(ICmpInst* ICmp = dyn_cast<ICmpInst>(BICondI)) {
                                            if((ICmp->getPredicate()==llvm::CmpInst::ICMP_NE) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_EQ)) {
                                                if((dyn_cast<Instruction>(ICmp->getOperand(0)) && dyn_cast<ConstantInt>(ICmp->getOperand(1))) || (dyn_cast<Instruction>(ICmp->getOperand(1)) && dyn_cast<ConstantInt>(ICmp->getOperand(0)))) {
                                                    Instruction* ICmpi = dyn_cast<Instruction>(ICmp->getOperand(0));
                                                    ConstantInt* ICmpc = dyn_cast<ConstantInt>(ICmp->getOperand(1));
                                                    if(!ICmpi) {
                                                        Instruction* ICmpi = dyn_cast<Instruction>(ICmp->getOperand(1));
                                                        ConstantInt* ICmpc = dyn_cast<ConstantInt>(ICmp->getOperand(0));
                                                    }
                                                    int cmpintvalue = -1; 
                                                    cmpintvalue = ICmpc->getZExtValue();
                                                    bool MaybeBitField = false;
                                                    int BitFieldOff = 0;
                                                    if(cmpintvalue != 0) continue;
                                                    set<Instruction*> pendinsts2;
                                                    pendinsts2.insert(ICmpi);
                                                    if(ICmpi->getOpcode() == llvm::Instruction::Call) {
                                                        pendinsts2.clear();
                                                        CallInst* ifCall = dyn_cast<CallInst>(ICmpi);
                                                        pendinsts2 = TryGetMountOptInIfCall(ifCall);
                                                        if(pendinsts2.empty()) continue;
                                                    }
                                                    for(Instruction* pendinst2 : pendinsts2) {
                                                        MaybeBitField = false;
                                                        BitFieldOff = 0;
                                                        ICmpi = pendinst2;
                                                        if(ICmpi->getOpcode() == llvm::Instruction::ZExt) {
                                                            ICmpi = dyn_cast<Instruction>(ICmpi->getOperand(0));
                                                            MaybeBitField = true;
                                                        }
                                                        if(ICmpi->getOpcode() == llvm::Instruction::And) {
                                                            auto *andop1 = ICmpi->getOperand(0);
                                                            auto *andop2 = ICmpi->getOperand(1);
                                                            Instruction* andi = nullptr;
                                                            LoadInst* ldi = nullptr;
                                                            GetElementPtrInst* gepi = nullptr;
                                                            uint32_t andv = 0xffffffff;
                                                            if(dyn_cast<ConstantInt>(andop1) && !dyn_cast<ConstantInt>(andop2)) {
                                                                andi = dyn_cast<Instruction>(andop2);
                                                                auto andInt = dyn_cast<ConstantInt>(andop1);
                                                                andv = andInt->getZExtValue();
                                                            } else if(dyn_cast<ConstantInt>(andop2) && !dyn_cast<ConstantInt>(andop1)) {
                                                                andi = dyn_cast<Instruction>(andop1);
                                                                auto andInt = dyn_cast<ConstantInt>(andop2);
                                                                andv = andInt->getZExtValue();
                                                            }
                                                            if(andv == 0xffffffff) continue;
                                                            if(!andi) continue;
                                                            if(andi->getOpcode() == llvm::Instruction::LShr) {
                                                                ConstantInt* BitFieldConst = dyn_cast<ConstantInt>(andi->getOperand(1));
                                                                if(!BitFieldConst) continue;
                                                                BitFieldOff = BitFieldConst->getZExtValue();
                                                                MaybeBitField = true;
                                                                andi = dyn_cast<Instruction>(andi->getOperand(0));
                                                            }
                                                            if(dyn_cast<LoadInst>(andi)) {
                                                                ldi = dyn_cast<LoadInst>(andi);
                                                                llvm::Value* ldpo = ldi->getPointerOperand();
                                                                Instruction* ldpoi = dyn_cast<Instruction>(ldpo);
                                                                if(!ldpoi) continue;
                                                                if(ldpoi->getOpcode() == llvm::Instruction::BitCast) {
                                                                    gepi = dyn_cast<GetElementPtrInst>(ldpoi->getOperand(0));
                                                                    MaybeBitField = true;
                                                                } else {
                                                                    gepi = dyn_cast<GetElementPtrInst>(ldpo);
                                                                }
                                                                if(!gepi) continue;
                                                                Type *gepiPTy = gepi->getPointerOperand()->getType();
                                                                Type *gepiTy = gepiPTy->getPointerElementType();
                                                                if (gepiTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2) {
                                                                    auto offsetVal = gepi->getOperand(2);
                                                                    auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                                    int offsetinst = offsetInt->getZExtValue();
                                                                    string icmptost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                                    string icmptostbitfield = icmptost;
                                                                    if(MaybeBitField) {
                                                                        icmptostbitfield = icmptostbitfield + ":" + std::to_string(BitFieldOff);
                                                                    }
                                                                    OneLayerPairSet currStAndConsts;
                                                                    //修改： 一层直接赋值的assignenum和assignint还没写
                                                                    if(isno) {
                                                                        currStAndConsts.insert(std::make_pair(std::make_pair(icmptost, std::make_pair(andv, "clear")), std::make_pair(std::string(""), (uint64_t)0)));
                                                                        currStAndConsts.insert(std::make_pair(std::make_pair(icmptost, std::make_pair(andv, "enumclear")), std::make_pair(std::string(""), (uint64_t)0)));
                                                                        if(MaybeBitField) {
                                                                            currStAndConsts.insert(std::make_pair(std::make_pair(icmptostbitfield, std::make_pair((uint32_t)BitFieldOff, "bitfieldclear")), std::make_pair(std::string(""), (uint64_t)0)));
                                                                        }
                                                                    } else {
                                                                        currStAndConsts.insert(std::make_pair(std::make_pair(icmptost, std::make_pair(andv, "set")), std::make_pair(std::string(""), (uint64_t)0)));
                                                                        currStAndConsts.insert(std::make_pair(std::make_pair(icmptost, std::make_pair(andv, "enumset")), std::make_pair(std::string(""), (uint64_t)0)));
                                                                        if(MaybeBitField) {
                                                                            currStAndConsts.insert(std::make_pair(std::make_pair(icmptostbitfield, std::make_pair((uint32_t)BitFieldOff, "bitfieldset")), std::make_pair(std::string(""), (uint64_t)0)));
                                                                        }
                                                                    }
                            
                                                                    if(sigfs2options.find(icmptost) != sigfs2options.end() || sigfs2options.find(icmptostbitfield) != sigfs2options.end()) {
                                                                        std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[icmptost];
                                                                        if(constandfe.empty()) {
                                                                            constandfe = sigfs2options[icmptostbitfield];
                                                                        }
                                                                        for(auto& constfeandconf : constandfe) {
                                                                            std::pair<uint32_t, string> constfe = constfeandconf.first;
                                                                            if(isno) {
                                                                                
                                                                                if((constfe.first != andv && constfe.first != BitFieldOff) || (constfe.second != "clear" && constfe.second != "enumclear" && constfe.second != "bitfieldclear")) continue;
                                                                            } else {
                                                                                if((constfe.first != andv && constfe.first != BitFieldOff) || (constfe.second != "set" && constfe.second != "enumset" && constfe.second != "bitfieldset")) continue;
                                                                            }
                                                                            std::pair<int, int> flagorenumopt = constfeandconf.second;
                                                                            int flagorenum = flagorenumopt.second;
                                                                            if(flagorenum > -1) {
                                                                                // enum
                                                                                int optnum = flagorenumopt.first;
                                                                                int enumnum = flagorenumopt.second;
                                                                                for(auto& enumoptandconst : sigfsparamsenum) {
                                                                                    pair<int, string> enumopt = enumoptandconst.first;
                                                                                    if(enumopt.first != optnum) continue;
                                                                                    string enumoptstr = enumopt.second;
                                                                                    std::map<int, string> enumconst = enumoptandconst.second;
                                                                                    string enumstr = enumconst[enumnum];
                                                                                    fsMountConstraintIf.insert(std::make_pair(enumoptstr, "=" + enumstr));
                                                                                }
                                                                            } else {
                                                                                // flag or enum or int
															                    int optnum = flagorenumopt.first;
															                    int optstatus = flagorenumopt.second;
															                    string flagoptstr = sigfsparamsflag[optnum];
															                    auto it_int = sigfsparamsint.find(optnum);
															                    if(!flagoptstr.empty()) {
																                    if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																                    fsMountConstraintIf.insert(std::make_pair(flagoptstr, " "));
															                    }
															                    else if(it_int != sigfsparamsint.end()) {
																                    string intname = it_int->second.first;
																                    string op = "";
																                    if(isno) op = "!="; else op = "=";
																                    fsMountConstraintIf.insert(std::make_pair(intname, op + std::to_string(andv)));
																                    continue;
															                    }
															                    else {
																                    if(optstatus == -1) {
																	                    for(auto& enumopt2 : sigfsparamsenum) {
																		                    std::pair<int, string> enumoptnumandstr = enumopt2.first;
																		                    if(enumoptnumandstr.first != optnum) continue;
																		                    std::map<int, string> enumsvalueandstr = enumopt2.second;
																		                    if(enumsvalueandstr.find(andv) != enumsvalueandstr.end()) {
																			                    string enumvaluetostr = enumsvalueandstr[andv];
																			                    string op = "";
																			                    if (isno) op = "!="; else op = "=";
																			                    fsMountConstraintIf.insert(std::make_pair(enumoptnumandstr.second, op + enumvaluetostr));
                                                                                                break;
																		                    }
																	                    }
																                    }			
															                    }
                                                                            }
                                                                        }
                                                                    }
                                                                    else {
                                                                        for(auto& currStAndConst : currStAndConsts) {
                                                                            auto searchKey = currStAndConst.first;
                                                                            if(sigfs2options2onelayer.find(searchKey) != sigfs2options2onelayer.end()) {
                                                                                OneLayerPairSet fsopts2one = sigfs2options2onelayer[searchKey];
                                                                                for(auto& OptStConstconf : fsopts2one) {
                                                                                    auto& innerP = OptStConstconf.first;
                                                                                    pair<uint32_t, string> ConstConf = innerP.second;
                                                                                    string optSt = innerP.first;
                                                                                    uint32_t setOptConst = ConstConf.first;
                                                                                    string setOptStr = ConstConf.second;
                                                                                    std::pair<std::string, uint64_t> cmpopandv = OptStConstconf.second;
                                                                                    if(setOptConst == 0xffffffff && setOptStr != "assignenum" && setOptStr != "assignint") continue;
                                                                                    std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[optSt];
                                                                                    for(auto& constfeandconf : constandfe) {
                                                                                        std::pair<uint32_t, string> constfe = constfeandconf.first;
                                                                                        if(constfe.first != setOptConst || constfe.second != setOptStr) continue;
                                                                                        std::pair<int, int> flagorenumopt = constfeandconf.second;
                                                                                        int flagorenum = flagorenumopt.second;
                                                                                        if(flagorenum > -1) {
                                                                                            // enum
                                                                                            int optnum = flagorenumopt.first;
                                                                                            int enumnum = flagorenumopt.second;
                                                                                            for(auto& enumoptandconst : sigfsparamsenum) {
                                                                                                pair<int, string> enumopt = enumoptandconst.first;
                                                                                                if(enumopt.first != optnum) continue;
                                                                                                string enumoptstr = enumopt.second;
                                                                                                std::map<int, string> enumconst = enumoptandconst.second;
                                                                                                string enumstr = enumconst[enumnum];
                                                                                                fsMountConstraintIf.insert(std::make_pair(enumoptstr, "=" + enumstr));
                                                                                            }
                                                                                        } else {
                                                                                            // flag, int, or enum
																		                    int optnum = flagorenumopt.first;
																		                    int optstatus = flagorenumopt.second;
																		                    // check int params first
																		                    auto it_int = sigfsparamsint.find(optnum);
																		                    if(it_int != sigfsparamsint.end()) {
																			                    string intname = it_int->second.first;
																			                    string op = "";
																			                    if (cmpopandv.first != "") {
																				                    if(isno) op = comparisonOpposites[cmpopandv.first]; else op = cmpopandv.first;
																				                    fsMountConstraintIf.insert(std::make_pair(intname, op + std::to_string(cmpopandv.second)));
																			                    } else {
																				                    if(isno) op = "!="; else op = "=";
																				                    fsMountConstraintIf.insert(std::make_pair(intname, op + std::to_string(andv)));
																			                    }
																			                    continue;
																		                    }
																		                    string flagoptstr = sigfsparamsflag[optnum];
																		                    if(!flagoptstr.empty()) {
																			                    if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																			                    fsMountConstraintIf.insert(std::make_pair(flagoptstr, " "));
																		                    } else {
																			                    if(optstatus == -1) {
																				                    string op = "";
																				                    for(auto& enumopt2 : sigfsparamsenum) {
																					                    std::pair<int, string> enumoptnumandstr = enumopt2.first;
																					                    if(enumoptnumandstr.first != optnum) continue;
																					                    std::map<int, string> enumsvalueandstr = enumopt2.second;
																					                    if (cmpopandv.first != "") {
																						                    for (auto& enumvs : enumsvalueandstr) {
																							                    if (enumvs.first == cmpopandv.second) {
																								                    if(isno) op = comparisonOpposites[cmpopandv.first]; else op = cmpopandv.first;
																								                    fsMountConstraintIf.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
																							                    }
																						                    }
																					                    } else {
																						                    for (auto& enumvs : enumsvalueandstr) {
																							                    if (enumvs.first == andv) {
																								                    if (isno) op = "!="; else op = "=";
																								                    fsMountConstraintIf.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
																							                    }
																						                    }
																					                    }
																					                    break;
																				                    }
																			                    }
																		                    }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    } 
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        else if(TruncInst* Trunci = dyn_cast<TruncInst>(BICondI)) {
                                            // 1. 获取源操作数 (%31)
                                            Value *sourceValue = Trunci->getOperand(0);
                                
                                            // 3. 获取目标类型 (i1)
                                            Type *destType = Trunci->getDestTy();
                        
                                            uint32_t flagv = 0xfffffff1;
                                            if(isno) flagv = 0xfffffff0;
                        
                                            bool MaybeBitField = false;
                                            int BitFieldOff = 0;
                                                    
                                            // 4. 判断目标类型是否是 i1
                                            if (IntegerType *intType = dyn_cast<IntegerType>(destType)) {
                                                if (intType->getBitWidth() == 1) {
                                                    Value* MaybeLdi = sourceValue;
                                                    Instruction* TruncSrci = dyn_cast<Instruction>(MaybeLdi);
                                                    if(TruncSrci && TruncSrci->getOpcode() == llvm::Instruction::And) {
                                                        MaybeBitField = true;
                                                        MaybeLdi = TruncSrci->getOperand(0);
                                                        Instruction* andi = dyn_cast<Instruction>(MaybeLdi);
                                                        if(andi && andi->getOpcode() == llvm::Instruction::LShr) {
                                                            ConstantInt* BitLShrConstInt = dyn_cast<ConstantInt>(andi->getOperand(1));
                                                            if(BitLShrConstInt) {
                                                                MaybeLdi = andi->getOperand(0);
                                                                BitFieldOff = BitLShrConstInt->getZExtValue();
                                                            } 
                                                        }
                                                    }
                                                    if(LoadInst* ldi=dyn_cast<LoadInst>(MaybeLdi)) {
                                                        Value* ldiv = ldi->getPointerOperand();
                                                        Instruction* ldpoi = dyn_cast<Instruction>(ldiv);
                                                        if(ldpoi && ldpoi->getOpcode() == llvm::Instruction::BitCast) {
                                                            ldiv = ldpoi->getOperand(0);
                                                            MaybeBitField = true;
                                                        }
                                                        if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(ldiv)) {
                                                            Type *GepTy = GEP->getPointerOperand()->getType()->getPointerElementType();
                                                            if(GepTy->isStructTy() && GEP->hasAllConstantIndices() && GEP->getNumIndices() == 2) {
                                                                auto offsetVal = GEP->getOperand(2);
                                                                auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                                                                int offsetinst = offsetInt->getZExtValue();
                                                                string itrunctost = GEP->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
                                                                if(MaybeBitField) {
                                                                    itrunctost = itrunctost + ":" + std::to_string(BitFieldOff);
                                                                }
                                                                std::pair<std::pair<std::string, std::pair<uint32_t, std::string>>, std::pair<std::string, uint64_t>> currStAndConst;
                                                                if(isno) {
                                                                    if(MaybeBitField) {
                                                                        currStAndConst = std::make_pair(std::make_pair(itrunctost, std::make_pair((uint32_t)BitFieldOff, "bitfieldclear")), std::make_pair(std::string(""), (uint64_t)0));
                                                                    } else {
                                                                        currStAndConst = std::make_pair(std::make_pair(itrunctost, std::make_pair(flagv, "assignfalse")), std::make_pair(std::string(""), (uint64_t)0));
                                                                    }
                                                                } else {
                                                                    if(MaybeBitField) {
                                                                        currStAndConst = std::make_pair(std::make_pair(itrunctost, std::make_pair((uint32_t)BitFieldOff, "bitfieldset")), std::make_pair(std::string(""), (uint64_t)0));
                                                                    } else {
                                                                        currStAndConst = std::make_pair(std::make_pair(itrunctost, std::make_pair(flagv, "assigntrue")), std::make_pair(std::string(""), (uint64_t)0));
                                                                    }
                                                                }
                                                                
                                                                if(sigfs2options.find(itrunctost) != sigfs2options.end()) {
                                                                    std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[itrunctost];
                                                                    for(auto& constfeandconf : constandfe) {
                                                                        std::pair<uint32_t, string> constfe = constfeandconf.first;
                                                                        if(isno) {
                                                                            if(MaybeBitField) {
                                                                                if(constfe.first != BitFieldOff || constfe.second != "bitfieldclear") continue;
                                                                            } else {
                                                                                if(constfe.first != flagv || constfe.second != "assignfalse") continue;
                                                                            }
                                                                        } else {
                                                                            if(MaybeBitField) {
                                                                                if(constfe.first != BitFieldOff || constfe.second != "bitfieldset") continue;
                                                                            } else {
                                                                                if(constfe.first != flagv || constfe.second != "assigntrue") continue;
                                                                            }
                                                                        }
                                                                        std::pair<int, int> flagorenumopt = constfeandconf.second;
                                                                        int flagorenum = flagorenumopt.second;
                                                                        if(flagorenum > -1) {
                                                                            // enum
                                                                            int optnum = flagorenumopt.first;
                                                                            int enumnum = flagorenumopt.second;
                                                                            for(auto& enumoptandconst : sigfsparamsenum) {
                                                                                pair<int, string> enumopt = enumoptandconst.first;
                                                                                if(enumopt.first != optnum) continue;
                                                                                string enumoptstr = enumopt.second;
                                                                                std::map<int, string> enumconst = enumoptandconst.second;
                                                                                string enumstr = enumconst[enumnum];
                                                                                fsMountConstraintIf.insert(std::make_pair(enumoptstr, "=" + enumstr));
                                                                            }
                                                                        } else {
                                                                            // flag or enum
														                    int optnum = flagorenumopt.first;
														                    int optstatus = flagorenumopt.second;
														                    string flagoptstr = sigfsparamsflag[optnum];
														                    if(!flagoptstr.empty()) {
															                    if(optstatus == -2) flagoptstr = "no" + flagoptstr;
															                    fsMountConstraintIf.insert(std::make_pair(flagoptstr, " "));
														                    }
														                    else {
															                    if(optstatus == -1) {
																                    for(auto& enumopt2 : sigfsparamsenum) {
																	                    std::pair<int, string> enumoptnumandstr = enumopt2.first;
																	                    if(enumoptnumandstr.first != optnum) continue;
																	                    std::map<int, string> enumsvalueandstr = enumopt2.second;
																	                    if(enumsvalueandstr.find(flagv) != enumsvalueandstr.end()) {
																		                    string enumvaluetostr = enumsvalueandstr[flagv];
																		                    if (isno) {
																			                    fsMountConstraintIf.insert(std::make_pair(enumoptnumandstr.second, "!=" + enumvaluetostr));
																		                    }
																		                    else {
																			                    fsMountConstraintIf.insert(std::make_pair(enumoptnumandstr.second, "=" + enumvaluetostr));
																		                    }
																	                    }
																                    }
															                    }
														                    }
                                                                        }
                                                                    }
                                                                }
                                                                else {
                                                                    auto searchKey = currStAndConst.first;
                                                                    if(sigfs2options2onelayer.find(searchKey) != sigfs2options2onelayer.end()) {
                                                                        OneLayerPairSet fsopts2one = sigfs2options2onelayer[searchKey];
                                                                        for(auto& OptStConstconf : fsopts2one) {
                                                                            auto& innerP = OptStConstconf.first;
                                                                            pair<uint32_t, string> ConstConf = innerP.second;
                                                                            if(ConstConf.first == 0xffffffff && ConstConf.second != "assignenum" && ConstConf.second != "assignint") continue;
                                                                            string optSt = innerP.first;
                                                                            uint32_t setOptConst = ConstConf.first;
                                                                            string setOptStr = ConstConf.second;
                                                                            std::pair<std::string, uint64_t> cmpopandv = OptStConstconf.second;
                                                                            std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[optSt];
                                                                            for(auto& constfeandconf : constandfe) {
                                                                                std::pair<uint32_t, string> constfe = constfeandconf.first;
                                                                                if(constfe.first != setOptConst || constfe.second != setOptStr) continue;
                                                                                std::pair<int, int> flagorenumopt = constfeandconf.second;
                                                                                int flagorenum = flagorenumopt.second;
                                                                                if(flagorenum > -1) {
                                                                                    // enum
                                                                                    int optnum = flagorenumopt.first;
                                                                                    int enumnum = flagorenumopt.second;
                                                                                    for(auto& enumoptandconst : sigfsparamsenum) {
                                                                                        pair<int, string> enumopt = enumoptandconst.first;
                                                                                        if(enumopt.first != optnum) continue;
                                                                                        string enumoptstr = enumopt.second;
                                                                                        std::map<int, string> enumconst = enumoptandconst.second;
                                                                                        string enumstr = enumconst[enumnum];
                                                                                        fsMountConstraintIf.insert(std::make_pair(enumoptstr, "=" + enumstr));
                                                                                    }
                                                                                } else {
                                                                                    // flag, int, or enum
															                        int optnum = flagorenumopt.first;
															                        int optstatus = flagorenumopt.second;
															                        // check int params first
															                        auto it_int = sigfsparamsint.find(optnum);
															                        if(it_int != sigfsparamsint.end()) {
																                        string intname = it_int->second.first;
																                        string op = "";
																                        if (cmpopandv.first != "") {
																	                        if(isno) op = comparisonOpposites[cmpopandv.first]; else op = cmpopandv.first;
																	                        fsMountConstraintIf.insert(std::make_pair(intname, op + std::to_string(cmpopandv.second)));
																                        }
																                        continue;
															                        }
															                        string flagoptstr = sigfsparamsflag[optnum];
															                        if(!flagoptstr.empty()) {
																                        if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																                        fsMountConstraintIf.insert(std::make_pair(flagoptstr, " "));
															                        } else {
																                        if(optstatus == -1) {
																	                        string op = "";
																	                        for(auto& enumopt2 : sigfsparamsenum) {
																		                        std::pair<int, string> enumoptnumandstr = enumopt2.first;
																		                        if(enumoptnumandstr.first != optnum) continue;
																		                        std::map<int, string> enumsvalueandstr = enumopt2.second;
																		                        if (cmpopandv.first != "") {
																			                        for (auto& enumvs : enumsvalueandstr) {
																				                        if (enumvs.first == cmpopandv.second) {
																					                        if(isno) op = comparisonOpposites[cmpopandv.first]; else op = cmpopandv.first;
																					                        fsMountConstraintIf.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
																				                        }
																			                        }
																		                        }
																		                        break;
																	                        }
																                        }
															                        }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        if(fsMountConstraintIf.size() == 0) continue;
                                        for(auto &iii : *brbb1)
                                        {
                                            Instruction *II = &iii;
                                            if(II->getOpcode() == Instruction::GetElementPtr)
                                            {
                                                GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(II);
                                                if(!gepInst->getSourceElementType()->isStructTy())
                                                {
                                                    continue;
                                                }
                                                if(gepInst->getSourceElementType()->getStructName() == "struct.inode" || gepInst->getSourceElementType()->getStructName() == "struct.address_space")
                                                {
                                                    Type* gepPointerType = nullptr;
                                                    Instruction *gepNext = getNextInstruction(II);
                                                    Instruction *nearStore = II;
                                                    if(!gepInst->getResultElementType()->isPointerTy())
                                                    {
                                                        if(!gepNext || !dyn_cast<BitCastInst>(gepNext)) {
                                                            continue;
                                                        } else {
                                                            if(gepNext->getOperand(0) != gepInst) {
                                                                continue;
                                                            }
                                                            nearStore = gepNext;
                                                        }
                                                    }
                                                    if(!gepInst->getResultElementType()->isPointerTy()) {
                                                        if(gepNext && dyn_cast<BitCastInst>(gepNext)) {
                                                            BitCastInst* bci = dyn_cast<BitCastInst>(gepNext);
                                                            gepPointerType = bci->getDestTy();
                                                            while (gepPointerType->isPointerTy()) {
                                                                gepPointerType = gepPointerType->getPointerElementType();
                                                            }
                                                            if (!gepPointerType->isStructTy()) {
                                                                    gepPointerType = nullptr;
                                                            }
                                                        }
                                                    }
                                                    else {
                                                        gepPointerType = gepInst->getResultElementType()->getPointerElementType();
                                                        if(!gepPointerType->isStructTy())
                                                        {
                                                            gepPointerType = nullptr;
                                                        }
                                                    }
                                                    if(!gepPointerType) continue;
                                                    string gepResultType = gepPointerType->getStructName().str();
                                                    if(gepResultType == "struct.file_operations" || gepResultType == "struct.inode_operations" || gepResultType == "struct.address_space_operations")
                                                    {
                                                        for(User* user:nearStore->users())
                                                        {
                                                            if(StoreInst* storeInst = dyn_cast<StoreInst>(user))
                                                            {
                                                                Value* op = storeInst->getValueOperand();
                                                                GlobalVariable* globalVar = dyn_cast<GlobalVariable>(op);
                                                                if(globalVar == nullptr)
                                                                {
                                                                    if(BitCastOperator* bitcastOp = dyn_cast<BitCastOperator>(op))
                                                                    {
                                                                        globalVar = dyn_cast<GlobalVariable>(bitcastOp->getOperand(0));
                                                                    }
                                                                }
                                                                if(globalVar != nullptr)
                                                                {
                                                                    if(!globalVar->hasInitializer())
                                                                    {
                                                                        globalVar = getGlobalVaraible(globalVar->getName());
                                                                    }
                                                                }
                                                                if(globalVar != nullptr)
                                                                {
                                                                    for(auto& mntcons: fsMountConstraintIf) {
                                                                        string key = mntcons.first;
                                                                        string val = mntcons.second;
                                                                        if(val != " ") key = key + val;
                                                                        res[globalVar->getName().str()].insert("MountOpt:" + key);
                                                                        //修改：现在它里面也可能有!=或者其它符号了，要看下对它的使用需不需要改
                                                                    } 
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
                case llvm::Instruction::Br: {
                    auto bri = llvm::dyn_cast<llvm::BranchInst>(&i);
                    set<string> BrCondIsFileType = BranchCondIsFileType(srcfilename, bri);
                    if(BrCondIsFileType.size() == 0) continue;
                    BasicBlock* iftrueblk = bri->getSuccessor(0);
                    for(auto &i : *iftrueblk)
                    {
                        Instruction *I = &i;
                        if(I->getOpcode() == Instruction::GetElementPtr)
                        {
                            GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(I);
                            if(!gepInst->getSourceElementType()->isStructTy())
                            {
                                continue;
                            }
                            if(gepInst->getSourceElementType()->getStructName() == "struct.inode" || gepInst->getSourceElementType()->getStructName() == "struct.address_space")
                            {
                                Type* gepPointerType = nullptr;
                                Instruction *gepNext = getNextInstruction(I);
                                Instruction *nearStore = I;
                                if(!gepInst->getResultElementType()->isPointerTy())
                                {
                                    if(!gepNext || !dyn_cast<BitCastInst>(gepNext)) {
                                        continue;
                                    } else {
                                        if(gepNext->getOperand(0) != gepInst) {
                                            continue;
                                        }
                                        nearStore = gepNext;
                                    }
                                }
                                if(!gepInst->getResultElementType()->isPointerTy()) {
                                    if(gepNext && dyn_cast<BitCastInst>(gepNext)) {
                                        BitCastInst* bci = dyn_cast<BitCastInst>(gepNext);
                                        gepPointerType = bci->getDestTy();
                                        while (gepPointerType->isPointerTy()) {
                                            gepPointerType = gepPointerType->getPointerElementType();
                                        }
                                        if (!gepPointerType->isStructTy()) {
                                                gepPointerType = nullptr;
                                        }
                                    }
                                }
                                else {
                                    gepPointerType = gepInst->getResultElementType()->getPointerElementType();
                                    if(!gepPointerType->isStructTy())
                                    {
                                        gepPointerType = nullptr;
                                    }
                                }
                                if(!gepPointerType) continue;
                                string gepResultType = gepPointerType->getStructName().str();
                                if(gepResultType == "struct.file_operations" || gepResultType == "struct.inode_operations" || gepResultType == "struct.address_space_operations")
                                {
                                    for(User* user:nearStore->users())
                                    {
                                        if(StoreInst* storeInst = dyn_cast<StoreInst>(user))
                                        {
                                            Value* op = storeInst->getValueOperand();
                                            GlobalVariable* globalVar = dyn_cast<GlobalVariable>(op);
                                            if(globalVar == nullptr)
                                            {
                                                if(BitCastOperator* bitcastOp = dyn_cast<BitCastOperator>(op))
                                                {
                                                    globalVar = dyn_cast<GlobalVariable>(bitcastOp->getOperand(0));
                                                }
                                            }
                                            if(globalVar != nullptr)
                                            {
                                                if(!globalVar->hasInitializer())
                                                {
                                                    globalVar = getGlobalVaraible(globalVar->getName());
                                                }
                                            }
                                            if(globalVar != nullptr)
                                            {
                                                for(auto& ft : BrCondIsFileType) {
                                                    res[globalVar->getName().str()].insert("FileType:" + ft);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
    return res;
}

vector<GlobalVariable*> getOperStruct(Module* M, const char* StrucName)
{
    vector<GlobalVariable*> res;
    for(auto gv = M->global_begin(); gv != M->global_end(); gv++)
    {
        GlobalVariable* globalVar = &(*gv); 
        if (globalVar == nullptr) {
            continue;
        }
        if (globalVar->getValueType()->isStructTy())
        {
            if (!globalVar->isConstant() || !globalVar->hasInitializer()) {
                continue;
            }
            if(globalVar->getName().endswith(StrucName))
            {
                res.push_back(globalVar);
            }
            else if(globalVar->getValueType()->getStructName().str() == string("struct.")+StrucName)
            {
                res.push_back(globalVar);
            }
        }
    }
    return res;
}

void getCallTrace(Function* targetFunction, vector<CallTraceInfo> &callTraces) {
	// input: target function
	// output: call trace: from syscall to target function
	// return a <Function*, Inst*> pair vector for each syscall,
	// the last pair is <Function*, nullptr>
	// the other pair is <Function*, call inst of next function>
	queue<pair<Function*, int>> q;
	map<Function*, set<pair<Function*, CallInst*>>> callerHistory; // A -> set of <B, (call B) in A>
	unordered_set<Function*> entryList;
	map<Function*, int> visit;

	string targetFunctionName = targetFunction->getName().str();

	q.push(make_pair(targetFunction, 0));
	visit[targetFunction] = 1;

	int maxCallTrace = 2;
	int maxIndirectCallNum = 2;

	while (!q.empty()) {
		Function *F = q.front().first;
		int original_currentIndirectCallNum = q.front().second;
		q.pop();

		size_t fh = funcHash(F);
		Function* unifiedFunc= GlobalCtx.UnifiedFuncMap[fh];
		for (auto callInst: GlobalCtx.Callers[unifiedFunc]) {
			Function *callerFunc = callInst->getFunction();
			int currentIndirectCallNum = original_currentIndirectCallNum;

			if (entryList.count(callerFunc) != 0) {
				if (visit[callerFunc] >= maxCallTrace) continue;
			} else {

				if (visit.count(callerFunc) != 0) {
					continue;
				}
			}

			if (callInst->isIndirectCall()) {
				currentIndirectCallNum += 1;
				if (currentIndirectCallNum >= maxIndirectCallNum) continue;
			}

			visit[callerFunc] += 1;

			callerHistory[callerFunc].insert(make_pair(F, callInst));

			string FuncName = callerFunc->getName().str();
			if (FuncName.size() > 0) {
				if (isSyscall(callerFunc)) {
					entryList.insert(callerFunc);
					continue;
				}
			}
			q.push(make_pair(callerFunc, currentIndirectCallNum));
		}
	}

	for (Function* entry: entryList) {
		Function *F = entry;


		// callerHistory  node: A -> set of <B, (call B) in A>
		queue<pair<Function*, Instruction*>> nodeQueue; // node: <B, call B in A>
		queue<vector<pair<Function*, Instruction*>>> pathQueue; // node: <A, call B in A>

		for (auto item: callerHistory[F]) {
			Function *nextFunc = item.first;
			CallInst *callInst = item.second;
			if (callInst) {
				Instruction *inst = dyn_cast<Instruction>(callInst);
				vector<pair<Function*, Instruction*>> tmp;
				tmp.push_back(make_pair(F, inst));
				pathQueue.push(tmp);
				nodeQueue.push(make_pair(nextFunc, inst));
			} else {
				vector<pair<Function*, Instruction*>> tmp;
				tmp.push_back(make_pair(F, nullptr));
				pathQueue.push(tmp);
				nodeQueue.push(make_pair(nextFunc, nullptr));
			}
		}

		while (!nodeQueue.empty()) {
			pair<Function*, Instruction*> node = nodeQueue.front();
			vector<pair<Function*, Instruction*>> path = pathQueue.front();
			nodeQueue.pop();
			pathQueue.pop();

			Function *F = node.first;

// A -> set of <B, (call B) in A>
			if (callerHistory.count(F) == 0) {
				path.push_back(make_pair(F, nullptr));
				CallTraceInfo callTraceInfo;
				callTraceInfo.callTrace = path;
				
				int depth = path.size();
				int icallNum = 0;
				for (auto item: path) {
					if (item.second == nullptr) { continue; }
					if (CallInst *callInst = dyn_cast<CallInst>(item.second)) {
						if (callInst->isIndirectCall()) {
							icallNum += 1;
						}
					}
				}
				callTraceInfo.depth = depth;
				callTraceInfo.icallNum = icallNum;
				callTraceInfo.isSyscallEntry = isSyscall(path[0].first);
				callTraces.push_back(callTraceInfo);
				

			} else {
				for (auto item: callerHistory[F]) {
					Function *nextFunc = item.first;
					if (item.second) {
						Instruction *inst = dyn_cast<Instruction>(item.second);
						nodeQueue.push(make_pair(nextFunc, inst));
						path.push_back(make_pair(F, inst));
						pathQueue.push(path);
					} else {
						nodeQueue.push(make_pair(nextFunc, nullptr));
						path.push_back(make_pair(F, nullptr));
						pathQueue.push(path);
					}
				}
			}
		}
	}
    std::sort(callTraces.begin(), callTraces.end(), [](CallTraceInfo a, CallTraceInfo b) {
		if (a.depth != b.depth) {
			return a.depth < b.depth;
		} else {
			return a.icallNum < b.icallNum;
		}
	});
}

vector<pair<string, Function*>> FilesystemExtractorPass::getHandlerFromFileOperations(GlobalVariable* globalVar, string fsname)
{
    vector<pair<string, Function*>> res = vector<pair<string, Function*>>();
    ConstantStruct* constStruct = dyn_cast<ConstantStruct>(globalVar->getInitializer());
    if (!constStruct && Ctx->GlobalStructMap.count(globalVar->getName().str())) {
        constStruct = dyn_cast<ConstantStruct>(Ctx->GlobalStructMap[globalVar->getName().str()]);
    } 
    if (!constStruct) return res;
    Constant* handlerLlseek = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["llseek"]);
    Constant* handlerRead = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["read"]);
    Constant* handlerWrite = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["write"]);
    //Constant* handlerIopoll = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["iopoll"]);
    Constant* handlerIoctl = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["unlocked_ioctl"]);
    //Constant* handlerCompatIoctl = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["compat_ioctl"]);
    Constant* handlerOpen = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["open"]);
    Constant* handlerMmap = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["mmap"]);
    Constant* handlerFlush = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["flush"]);
    Constant* handlerRelease = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["release"]);
    Constant* handlerSpliceRead = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["splice_read"]);
    Constant* handlerSpliceWrite = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["splice_write"]);
    Constant* handlerLock = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["lock"]);
    Constant* handlerCKflag = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["check_flags"]);
    Constant* handlerFlock = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["flock"]);
    if (handlerFlock && isa<Function>(handlerFlock))
    {
        Function* flockFunc = dyn_cast<Function>(handlerFlock);
        if(flockFunc != nullptr)
        {
            if(flockFunc->getInstructionCount() == 0)
            {
                flockFunc = getFunctionFromModules(flockFunc->getName());
            }
        }
        if(flockFunc != nullptr)
        {
            res.push_back(make_pair("flock", flockFunc));
            GlobalCtx.FunctionArgMap[flockFunc->getName().str()] = {1, 2, 0};
            if(fsname != "" && flockFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][flockFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerCKflag && isa<Function>(handlerCKflag))
    {
        Function* ckflagFunc = dyn_cast<Function>(handlerCKflag);
        if(ckflagFunc != nullptr)
        {
            if(ckflagFunc->getInstructionCount() == 0)
            {
                ckflagFunc = getFunctionFromModules(ckflagFunc->getName());
            }
        }
        if(ckflagFunc != nullptr)
        {
            res.push_back(make_pair("fcntl", ckflagFunc));
            GlobalCtx.FunctionArgMap[ckflagFunc->getName().str()] = {4};
            if(fsname != "" && ckflagFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][ckflagFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerLock && isa<Function>(handlerLock))
    {
        Function* lockFunc = dyn_cast<Function>(handlerLock);
        if(lockFunc != nullptr)
        {
            if(lockFunc->getInstructionCount() == 0)
            {
                lockFunc = getFunctionFromModules(lockFunc->getName());
            }
        }
        if(lockFunc != nullptr)
        {
            res.push_back(make_pair("fcntl", lockFunc));
            GlobalCtx.FunctionArgMap[lockFunc->getName().str()] = {1, 2, 0};
            if(fsname != "" && lockFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][lockFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerLlseek && isa<Function>(handlerLlseek))
    {
        Function* llseekFunc = dyn_cast<Function>(handlerLlseek);
        if(llseekFunc != nullptr)
        {
            if(llseekFunc->getInstructionCount() == 0)
            {
                llseekFunc = getFunctionFromModules(llseekFunc->getName());
            }
        }
        if(llseekFunc != nullptr)
        {
            res.push_back(make_pair("llseek", llseekFunc));
            GlobalCtx.FunctionArgMap[llseekFunc->getName().str()] = {1, 6, 16};
            if(fsname != "" && llseekFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][llseekFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerRead && isa<Function>(handlerRead))
    {
        Function* readFunc = dyn_cast<Function>(handlerRead);
        if(readFunc != nullptr)
        {
            if(readFunc->getInstructionCount() == 0)
            {
                readFunc = getFunctionFromModules(readFunc->getName());
            }
        }
        if(readFunc != nullptr)
        {
            res.push_back(make_pair("read", readFunc));
            GlobalCtx.FunctionArgMap[readFunc->getName().str()] = {1, 2, 4, 0};
            if(fsname != "" && readFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][readFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    else {
        Constant* handlerReadIter = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["read_iter"]);
        if(handlerReadIter && isa<Function>(handlerReadIter)) {
            Function* readiterFunc = dyn_cast<Function>(handlerReadIter);
            if(readiterFunc != nullptr)
            {
                if(readiterFunc->getInstructionCount() == 0) {
                    readiterFunc = getFunctionFromModules(readiterFunc->getName());
                }
            }
            if(readiterFunc != nullptr)
            {
                res.push_back(make_pair("read", readiterFunc));
                GlobalCtx.FunctionArgMap[readiterFunc->getName().str()] = {0, 0};
                if(fsname != "" && readiterFunc->hasName() && globalVar->hasName()) {
                    Ctx->Fs2EntryFunc2FuncTable[fsname][readiterFunc->getName().str()].insert(globalVar->getName().str());
                }
            }
        }
    }
    if (handlerWrite && isa<Function>(handlerWrite))
    {
        Function* writeFunc = dyn_cast<Function>(handlerWrite);
        if(writeFunc != nullptr)
        {
            if(writeFunc->getInstructionCount() == 0)
            {
                writeFunc = getFunctionFromModules(writeFunc->getName());
            }
        }
        if(writeFunc != nullptr)
        {
            res.push_back(make_pair("write", writeFunc));
            GlobalCtx.FunctionArgMap[writeFunc->getName().str()] = {1, 2, 4, 0};
            if(fsname != "" && writeFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][writeFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    else
    {
        handlerWrite = constStruct->getOperand(Ctx->StructFieldIdx["file_operations"]["write_iter"]);
        if(handlerWrite && isa<Function>(handlerWrite))
        {
            Function* writeFunc = dyn_cast<Function>(handlerWrite);
            if(writeFunc != nullptr && writeFunc->getInstructionCount() == 0)
            {
                writeFunc = getFunctionFromModules(writeFunc->getName());
            }
            if(writeFunc != nullptr)
            {
                res.push_back(make_pair("write", writeFunc));
                GlobalCtx.FunctionArgMap[writeFunc->getName().str()] = {0, 0};
                if(fsname != "" && writeFunc->hasName() && globalVar->hasName()) {
                    Ctx->Fs2EntryFunc2FuncTable[fsname][writeFunc->getName().str()].insert(globalVar->getName().str());
                }
            }
        }
    }
    /*if (handlerIopoll && isa<Function>(handlerIopoll))
    {
        Function* iopollFunc = dyn_cast<Function>(handlerIopoll);
        if(iopollFunc != nullptr)
        {
            if(iopollFunc->getInstructionCount() == 0)
            {
                iopollFunc = getFunctionFromModules(iopollFunc->getName());
            }
        }
        if(iopollFunc != nullptr)
        {
            res.push_back(make_pair("io_uring_enter", iopollFunc));
            GlobalCtx.FunctionArgMap[iopollFunc->getName().str()] = {0, 0};
            if(fsname != "" && iopollFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][iopollFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }*/
    if (handlerIoctl && isa<Function>(handlerIoctl))
    {
        Function* ioctlFunc = dyn_cast<Function>(handlerIoctl);
        if(ioctlFunc != nullptr)
        {
            if(ioctlFunc->getInstructionCount() == 0)
            {
                ioctlFunc = getFunctionFromModules(ioctlFunc->getName());
            }
        }
        if(ioctlFunc != nullptr)
        {
            res.push_back(make_pair("ioctl", ioctlFunc));
            if(ioctlFunc->getName() == "autofs_root_ioctl")
            {
                outs() << "get autofs_root_ioctl" << "\n";
            }
            GlobalCtx.FunctionArgMap[ioctlFunc->getName().str()] = {1, 2, 4};
            if(fsname != "" && ioctlFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][ioctlFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    /*if (handlerCompatIoctl && isa<Function>(handlerCompatIoctl))
    {
        Function* ioctlFunc = dyn_cast<Function>(handlerCompatIoctl);
        if(ioctlFunc != nullptr)
        {
            if(ioctlFunc->getInstructionCount() == 0)
            {
                ioctlFunc = getFunctionFromModules(ioctlFunc->getName());
            }
        }
        if(ioctlFunc != nullptr)
        {
            res.push_back(make_pair("ioctl", ioctlFunc));
            if(ioctlFunc->getName() == "autofs_root_ioctl")
            {
                outs() << "get autofs_root_ioctl" << "\n";
            }
            GlobalCtx.FunctionArgMap[ioctlFunc->getName().str()] = {1, 2, 4};
        }
    }*/
    if (handlerOpen && isa<Function>(handlerOpen))
    {
        Function* openFunc = dyn_cast<Function>(handlerOpen);
        if(openFunc != nullptr)
        {
            if(openFunc->getInstructionCount() == 0)
            {
                openFunc = getFunctionFromModules(openFunc->getName());
            }
        }
        if(openFunc != nullptr)
        {
            res.push_back(make_pair("open", openFunc));
            GlobalCtx.FunctionArgMap[openFunc->getName().str()] = {0, 1};
            if(fsname != "" && openFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][openFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerMmap && isa<Function>(handlerMmap))
    {
        Function* mmapFunc = dyn_cast<Function>(handlerMmap);
        if(mmapFunc != nullptr)
        {
            if(mmapFunc->getInstructionCount() == 0)
            {
                mmapFunc = getFunctionFromModules(mmapFunc->getName());
            }
        }
        if(mmapFunc != nullptr)
        {
            res.push_back(make_pair("mmap", mmapFunc));
            GlobalCtx.FunctionArgMap[mmapFunc->getName().str()] = {1, 2};
            if(fsname != "" && mmapFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][mmapFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerFlush && isa<Function>(handlerFlush))
    {
        Function* flushFunc = dyn_cast<Function>(handlerFlush);
        if(flushFunc != nullptr)
        {
            if(flushFunc->getInstructionCount() == 0)
            {
                flushFunc = getFunctionFromModules(flushFunc->getName());
            }
        }
        if(flushFunc != nullptr)
        {
            res.push_back(make_pair("close", flushFunc));
            GlobalCtx.FunctionArgMap[flushFunc->getName().str()] = {1, 0};
            if(fsname != "" && flushFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][flushFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerRelease && isa<Function>(handlerRelease))
    {
        Function* releaseFunc = dyn_cast<Function>(handlerRelease);
        if(releaseFunc != nullptr)
        {
            if(releaseFunc->getInstructionCount() == 0)
            {
                releaseFunc = getFunctionFromModules(releaseFunc->getName());
            }
        }
        if(releaseFunc != nullptr)
        {
            res.push_back(make_pair("close", releaseFunc));
            GlobalCtx.FunctionArgMap[releaseFunc->getName().str()] = {0, 1};
            if(fsname != "" && releaseFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][releaseFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerSpliceRead && isa<Function>(handlerSpliceRead))
    {
        Function* splicereadFunc = dyn_cast<Function>(handlerSpliceRead);
        if(splicereadFunc != nullptr)
        {
            if(splicereadFunc->getInstructionCount() == 0)
            {
                splicereadFunc = getFunctionFromModules(splicereadFunc->getName());
            }
        }
        if(splicereadFunc != nullptr)
        {
            res.push_back(make_pair("splice", splicereadFunc));
            GlobalCtx.FunctionArgMap[splicereadFunc->getName().str()] = {1, 2, 0, 16, 32};
            if(fsname != "" && splicereadFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][splicereadFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerSpliceWrite && isa<Function>(handlerSpliceWrite))
    {
        Function* splicewriteFunc = dyn_cast<Function>(handlerSpliceWrite);
        if(splicewriteFunc != nullptr)
        {
            if(splicewriteFunc->getInstructionCount() == 0)
            {
                splicewriteFunc = getFunctionFromModules(splicewriteFunc->getName());
            }
        }
        if(splicewriteFunc != nullptr)
        {
            res.push_back(make_pair("splice", splicewriteFunc));
            GlobalCtx.FunctionArgMap[splicewriteFunc->getName().str()] = {0, 4, 8, 16, 32};
            if(fsname != "" && splicewriteFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][splicewriteFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    return res;
}

map<string, vector<string>> xattrHandlerSyscallMap = {
    // {"get", {"getxattr", "lgetxattr", "fgetxattr"}}, 
    // {"set", {"setxattr", "lsetxattr", "fsetxattr"}},
    {"get", {"getxattr",}}, 
    {"set", {"setxattr",}},
};

vector<pair<string, Function*>> FilesystemExtractorPass::getHandlerFromASOperations(GlobalVariable* globalVar, string fsname)
{
    vector<pair<string, Function*>> res = vector<pair<string, Function*>>();
    ConstantStruct* constStruct = dyn_cast<ConstantStruct>(globalVar->getInitializer());
    if (!constStruct && Ctx->GlobalStructMap.count(globalVar->getName().str())) {
        constStruct = dyn_cast<ConstantStruct>(Ctx->GlobalStructMap[globalVar->getName().str()]);
    } 
    if (!constStruct) return res;
    auto &asStructMap = Ctx->StructFieldIdx["address_space_operations"];

    for (auto readFuncName: {"readpage", "readpages", "read_folio", "readahead", "is_partially_uptodate", "direct_IO"}) {
        Constant* handler = constStruct->getOperand(asStructMap[readFuncName]);
        if (!handler || !isa<Function>(handler)) {
            continue;
        }
        Function* readFunc = dyn_cast<Function>(handler);
        if(readFunc != nullptr && readFunc->getInstructionCount() == 0) {
            readFunc = getFunctionFromModules(readFunc->getName());
        }
        if(readFunc != nullptr) {
            res.push_back(make_pair("read", readFunc));
            if(fsname != "" && readFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][readFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }

    for(auto writeFuncName: {"write_begin", "write_end", "dirty_folio", "prepare_write", "commit_write", "set_page_dirty", "direct_IO"}) {
        Constant* handler = constStruct->getOperand(asStructMap[writeFuncName]);
        if (!handler || !isa<Function>(handler)) {
            continue;
        }
        Function* writeFunc = dyn_cast<Function>(handler);
        if(writeFunc != nullptr && writeFunc->getInstructionCount() == 0) {
            writeFunc = getFunctionFromModules(writeFunc->getName());
        }
        if(writeFunc != nullptr) {
            res.push_back(make_pair("write", writeFunc));
            if(fsname != "" && writeFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][writeFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }

    return res;
}

vector<pair<string, Function*>> FilesystemExtractorPass::getHandlerFromINodeOperations(GlobalVariable* globalVar, string fsname)
{
    vector<pair<string, Function*>> res = vector<pair<string, Function*>>();
    ConstantStruct* constStruct = dyn_cast<ConstantStruct>(globalVar->getInitializer());
    if (!constStruct && Ctx->GlobalStructMap.count(globalVar->getName().str())) {
        constStruct = dyn_cast<ConstantStruct>(Ctx->GlobalStructMap[globalVar->getName().str()]);
    } 
    if (!constStruct) return res;
    Constant* handlerCreate = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["create"]);
    Constant* handlerLink = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["link"]);
    Constant* handlerUnlink = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["unlink"]);
    Constant* handlerSymlink = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["symlink"]);
    Constant* handlerMkdir = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["mkdir"]);
    Constant* handlerRmdir = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["rmdir"]);
    Constant* handlerMknod = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["mknod"]);
    Constant* handlerRename = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["rename"]);
    //Constant* handlerGetlink = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["get_link"]);
    Constant* handlerReadlink = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["readlink"]);
    //Constant* handlerSetattr = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["setattr"]);
    //Constant* handlerGetattr = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["getattr"]);
    Constant* handlerListxattr = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["listxattr"]);
    //Constant* handlerTmpfile = constStruct->getOperand(Ctx->StructFieldIdx["inode_operations"]["tmpfile"]);
    if (handlerCreate && isa<Function>(handlerCreate))
    {
        Function* createFunc = dyn_cast<Function>(handlerCreate);
        if(createFunc != nullptr)
        {
            if(createFunc->getInstructionCount() == 0)
            {
                createFunc = getFunctionFromModules(createFunc->getName());
            }
        }
        if(createFunc != nullptr)
        {
            res.push_back(make_pair("open", createFunc));
            GlobalCtx.FunctionArgMap[createFunc->getName().str()] = {0, 0, 0, 4, 2};
            if(fsname != "" && createFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][createFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerLink && isa<Function>(handlerLink))
    {
        Function* linkFunc = dyn_cast<Function>(handlerLink);
        if(linkFunc != nullptr)
        {
            if(linkFunc->getInstructionCount() == 0)
            {
                linkFunc = getFunctionFromModules(linkFunc->getName());
            }
        }
        if(linkFunc != nullptr)
        {
            res.push_back(make_pair("link", linkFunc));
            GlobalCtx.FunctionArgMap[linkFunc->getName().str()] = {0, 0, 0};
            if(fsname != "" && linkFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][linkFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerUnlink && isa<Function>(handlerUnlink))
    {
        Function* unlinkFunc = dyn_cast<Function>(handlerUnlink);
        if(unlinkFunc != nullptr)
        {
            if(unlinkFunc->getInstructionCount() == 0)
            {
                unlinkFunc = getFunctionFromModules(unlinkFunc->getName());
            }
        }
        if(unlinkFunc != nullptr)
        {
            res.push_back(make_pair("unlink", unlinkFunc));
            GlobalCtx.FunctionArgMap[unlinkFunc->getName().str()] = {0, 0};
            if(fsname != "" && unlinkFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][unlinkFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerSymlink && isa<Function>(handlerSymlink))
    {
        Function* symlinkFunc = dyn_cast<Function>(handlerSymlink);
        if(symlinkFunc != nullptr)
        {
            if(symlinkFunc->getInstructionCount() == 0)
            {
                symlinkFunc = getFunctionFromModules(symlinkFunc->getName());
            }
        }
        if(symlinkFunc != nullptr)
        {
            res.push_back(make_pair("symlink", symlinkFunc));
            GlobalCtx.FunctionArgMap[symlinkFunc->getName().str()] = {0, 0, 0, 1};
            if(fsname != "" && symlinkFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][symlinkFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerMkdir && isa<Function>(handlerMkdir))
    {
        Function* mkdirFunc = dyn_cast<Function>(handlerMkdir);
        if(mkdirFunc != nullptr)
        {
            if(mkdirFunc->getInstructionCount() == 0)
            {
                mkdirFunc = getFunctionFromModules(mkdirFunc->getName());
            }
        }
        if(mkdirFunc != nullptr)
        {
            res.push_back(make_pair("mkdir", mkdirFunc));
            GlobalCtx.FunctionArgMap[mkdirFunc->getName().str()] = {0, 0, 0, 2};
            if(fsname != "" && mkdirFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][mkdirFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerRmdir && isa<Function>(handlerRmdir))
    {
        Function* rmdirFunc = dyn_cast<Function>(handlerRmdir);
        if(rmdirFunc != nullptr)
        {
            if(rmdirFunc->getInstructionCount() == 0)
            {
                rmdirFunc = getFunctionFromModules(rmdirFunc->getName());
            }
        }
        if(rmdirFunc != nullptr)
        {
            res.push_back(make_pair("rmdir", rmdirFunc));
            GlobalCtx.FunctionArgMap[rmdirFunc->getName().str()] = {0, 0};
            if(fsname != "" && rmdirFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][rmdirFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerMknod && isa<Function>(handlerMknod))
    {
        Function* mknodFunc = dyn_cast<Function>(handlerMknod);
        if(mknodFunc != nullptr)
        {
            if(mknodFunc->getInstructionCount() == 0)
            {
                mknodFunc = getFunctionFromModules(mknodFunc->getName());
            }
        }
        if(mknodFunc != nullptr)
        {
            res.push_back(make_pair("mknod", mknodFunc));
            GlobalCtx.FunctionArgMap[mknodFunc->getName().str()] = {0, 0, 0, 1, 2};
            if(fsname != "" && mknodFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][mknodFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerRename && isa<Function>(handlerRename))
    {
        Function* renameFunc = dyn_cast<Function>(handlerRename);
        if(renameFunc != nullptr)
        {
            if(renameFunc->getInstructionCount() == 0)
            {
                renameFunc = getFunctionFromModules(renameFunc->getName());
            }
        }
        if(renameFunc != nullptr)
        {
            res.push_back(make_pair("rename", renameFunc));
            GlobalCtx.FunctionArgMap[renameFunc->getName().str()] = {0, 0, 0, 0, 0, 0};
            if(fsname != "" && renameFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][renameFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerReadlink && isa<Function>(handlerReadlink))
    {
        Function* readlinkFunc = dyn_cast<Function>(handlerReadlink);
        if(readlinkFunc != nullptr)
        {
            if(readlinkFunc->getInstructionCount() == 0)
            {
                readlinkFunc = getFunctionFromModules(readlinkFunc->getName());
            }
        }
        if(readlinkFunc != nullptr)
        {
            res.push_back(make_pair("readlink", readlinkFunc));
            GlobalCtx.FunctionArgMap[readlinkFunc->getName().str()] = {0, 2, 4};
            if(fsname != "" && readlinkFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][readlinkFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    if (handlerListxattr && isa<Function>(handlerListxattr))
    {
        Function* listxattrFunc = dyn_cast<Function>(handlerListxattr);
        if(listxattrFunc != nullptr)
        {
            if(listxattrFunc->getInstructionCount() == 0)
            {
                listxattrFunc = getFunctionFromModules(listxattrFunc->getName());
            }
        }
        if(listxattrFunc != nullptr)
        {
            res.push_back(make_pair("listxattr", listxattrFunc));
            GlobalCtx.FunctionArgMap[listxattrFunc->getName().str()] = {0, 0, 4};
            if(fsname != "" && listxattrFunc->hasName() && globalVar->hasName()) {
                Ctx->Fs2EntryFunc2FuncTable[fsname][listxattrFunc->getName().str()].insert(globalVar->getName().str());
            }
        }
    }
    return res;
}

void FilesystemExtractorPass::ProcessRegisterFilesystem(CallInst* callInst, set<GlobalVariable*>& fsctxoper)
{
    FilesystemInfoItem* filesystemInfoItem = new FilesystemInfoItem();
    filesystemInfoItem->ItemType = FILESYSTEM;
    Value* arg = callInst->getOperand(0);
    if(GlobalVariable* globalVar = dyn_cast<GlobalVariable>(arg))
    {
        outs() << "[*] global variable: " << *arg << "\n";
        outs() << "[*] type: " << *globalVar->getType() << "\n";
        if(globalVar->getValueType()->isStructTy())
        {
            if(globalVar->hasInitializer())
            {
                HandleFsTypeStruct(globalVar, filesystemInfoItem, fsctxoper);
            }
            else
            {
                outs() << "[-] global variable declaration: " << *arg << "\n";
                GlobalVariable* globalVar = getGlobalVaraible(arg->getName());
                if(globalVar != nullptr)
                {
                    outs() << "[+] get global variable: " << *globalVar << "\n";
                    HandleFsTypeStruct(globalVar, filesystemInfoItem, fsctxoper);
                }
            }
        }

    }
    else if(ConstantExpr* constantExpr = dyn_cast<ConstantExpr>(arg))
    {
        outs() << "[+] constant cast: " << *arg << "\n";
        if(constantExpr->isCast())
        {
            if(GlobalVariable* globalVar = dyn_cast<GlobalVariable>(constantExpr->getOperand(0)))
            {
                if(globalVar->hasInitializer())
                {
                    HandleFsTypeStruct(globalVar, filesystemInfoItem, fsctxoper);
                }
                else
                {
                    outs() << "[-] global variable declaration: " << *arg << "\n";
                    globalVar = getGlobalVaraible(arg->getName());
                    if(globalVar != nullptr)
                    {
                        outs() << "[+] get global variable: " << *globalVar << "\n";
                        HandleFsTypeStruct(globalVar, filesystemInfoItem, fsctxoper);
                    }
                }
            }

        }
    }
    else
    {
        outs() << "[-] local variable: " << *arg << "\n";
        outs() << "[-] variable name: " << arg->getName() << "\n";
        outs() << "[-] in function: " << callInst->getFunction()->getName() << "\n";
    }

    SpecialFSItem* SpecialFileSystemInfoItem=NULL;
    for(auto p:filesystemInfoItem->SyscallHandler){
            
        if(p.first!="mount")
            continue;
        Function* mntFunc=p.second;
        outs() << "SpecialFSdebug: " << p.first << "|" << p.second->getName() << "\n";
        for (inst_iterator i = inst_begin(mntFunc), e = inst_end(mntFunc); 
            i != e; ++i) {
            if (CallInst *CI = dyn_cast<CallInst>(&*i)) {

                auto getCalledF=CI->getCalledFunction();
                if (getCalledF && getCalledF->getName()=="simple_fill_super" && CI->getNumOperands()==4){
                    
                    if(ConstantExpr* files_desc=dyn_cast<ConstantExpr>(CI->getOperand(2))){
                        outs() << "simple_fill_super2: " << *files_desc << "\n";
                        if(GetElementPtrInst* GEP=dyn_cast<GetElementPtrInst>(files_desc->getAsInstruction())){
                            if(GlobalVariable* GBV=dyn_cast<GlobalVariable>(GEP->getPointerOperand())){
                                if(GBV->hasInitializer()){
                                    const Constant *currConst = GBV->getInitializer();
                                    const ConstantArray *currArray = dyn_cast<ConstantArray>(currConst);
                                    for(int i=0;i<currArray->getNumOperands();i++){
                                        Value* currentV=currArray->getOperand(i);
                                        if(isa<ConstantAggregateZero>(currentV)){
                                            continue;
                                        }
                                        ConstantStruct* tree_descr=dyn_cast<ConstantStruct>(currentV);



                                        string subdevname = "";
                                        Value* NameStr=tree_descr->getOperand(0);
                                        raw_string_ostream ss(subdevname);
                                        if(auto temp=dyn_cast<ConstantExpr>(NameStr)){
                                            outs() << "tree_descr0: " << *temp << "\n";
                                            auto GEP=dyn_cast<GetElementPtrInst>(temp->getAsInstruction());
                                            if(GlobalVariable* GVStr=dyn_cast<GlobalVariable>(GEP->getPointerOperand())){
                                                if(GVStr->hasInitializer()){
                                                    NameStr=GVStr->getInitializer();
                                                }
                                                
                                            }
                                            
                                        }
                                        if(!SpecialFileSystemInfoItem){
                                            SpecialFileSystemInfoItem=new SpecialFSItem(filesystemInfoItem);
                                            delete filesystemInfoItem;
                                        }                                        
                                        
                                        if(ConstantDataArray* currDArray=dyn_cast<ConstantDataArray>(NameStr)){
                                            ss << currDArray->getAsCString();
                                            GlobalVariable* the_ops=dyn_cast<GlobalVariable>(tree_descr->getOperand(1));
                                            if(!the_ops) {
                                                auto *bitcastExpr = dyn_cast<ConstantExpr>(tree_descr->getOperand(1));
                                                if (bitcastExpr->getOpcode() == Instruction::BitCast) {
                                                    Value *operand = bitcastExpr->getOperand(0);
                                                    
                                                    if (GlobalVariable *targetGV = dyn_cast<GlobalVariable>(operand)) {
                                                        the_ops = targetGV;
                                                    }
                                                }
                                            }
                                            outs() << "tree_descr1: " << *the_ops << "\n";
                                            if (the_ops->hasInitializer()){
                                                vector<pair<string, Function*>> res = getHandlerFromFileOperations(the_ops, SpecialFileSystemInfoItem->name);
                                                for (auto p: res){
                                                    Function* f=p.second;
                                                    SpecialFileSystemInfoItem->Func2Dev[f]=subdevname;
                                                }
                                            }
                                        }
                                        
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if (SpecialFileSystemInfoItem)
        filesystemInfoItem=SpecialFileSystemInfoItem;

       
    
    Ctx->SubsystemInfo.push_back(filesystemInfoItem);
}


vector<Module*> FilesystemExtractorPass::getRelatedModule(Module* M)
{
    vector<Module*> res;
    string srcFileName = M->getSourceFileName();
    if(count(srcFileName.begin(), srcFileName.end(), '/') == 1)
    {
        res.push_back(M);
        return res;
    }
    else if(count(srcFileName.begin(), srcFileName.end(), '/') > 1)
    {
        string prefix = srcFileName.substr(0, srcFileName.rfind("/"));
        for(pair<Module*, StringRef> item : Ctx->Modules)
        {
            Module* m = item.first;
            if(m->getSourceFileName().find(prefix) == 0)
            {
                res.push_back(m);
            }
        }
    }
    return res;
    
}

bool FilesystemExtractorPass::doInitialization(Module* M)
{
    return false;
}

bool FilesystemExtractorPass::doModulePass(Module* M)
{
    bool corner = false;
    for(Module::iterator mi = M->begin(); mi != M->end(); mi++)
    {
        set<GlobalVariable*> cfsctxopers;
        Function* F = &*mi;
        // corner case
        if (F->hasName() && F->getName().str() == "vfs_kern_mount" && corner == false) 
        {
            for (User* user: F->users()) 
            {
                if (CallInst* callInst = dyn_cast<CallInst>(user)) 
                {
                    corner = true;
                    ProcessRegisterFilesystem(callInst, cfsctxopers);
                }
            }
        }
        if(F->hasName() && F->getName().str() == "register_filesystem")
        {
            for(User* user : F->users())
            {
                if(CallInst* callInst = dyn_cast<CallInst>(user))
                {
                    ProcessRegisterFilesystem(callInst, cfsctxopers);
                    vector<Module*> relatedModule = getRelatedModule(M);
                    for(Module* m: relatedModule)
                    {
                        outs() << "related modules\n";
                        outs() << m->getSourceFileName() << "\n";
                    }
                    FilesystemInfoItem* filesystemInfoItem = static_cast<FilesystemInfoItem*>(Ctx->SubsystemInfo[Ctx->SubsystemInfo.size() - 1]);
                    vector<GlobalVariable*> shouldRemove;
                    for(GlobalVariable* gv: filesystemInfoItem->fileOperations)
                    {
                        bool flag = false;
                        for(Module* m : relatedModule)
                        {
                            if(m->getGlobalVariable(gv->getName()) != nullptr)
                            {
                                outs() << "global variable name: " << gv->getName() << "\n";
                                if(m->getGlobalVariable(gv->getName()) == gv)
                                {
                                    flag = true;
                                    break;
                                }
                            }       
                        }
                        if(flag)
                            continue;
                        shouldRemove.push_back(gv);
                    }
                    for(GlobalVariable* gv : shouldRemove)
                    {
                        filesystemInfoItem->fileOperations.erase(find(filesystemInfoItem->fileOperations.begin(), filesystemInfoItem->fileOperations.end(), gv));
                    }
                    if(filesystemInfoItem->name != "debugfs")
                    {
                        for(Module* m: relatedModule)
                        {       
                            vector<GlobalVariable*> fileOperations = getOperStruct(m, "file_operations");
                            for(GlobalVariable* gv : fileOperations)
                            {
                                outs() << "file operations name: " << gv->getName() << "\n";
                                outs() << "file operations type: " << gv->getValueType()->getStructName() << "\n";
                                if(find(filesystemInfoItem->fileOperations.begin(), filesystemInfoItem->fileOperations.end(), gv) != filesystemInfoItem->fileOperations.end())
                                    continue;
                                filesystemInfoItem->fileOperations.push_back(gv);
                            }
                        } 
                        set<GlobalVariable*> asOperStructs;
                        for (Module* m: relatedModule) {       
                            vector<GlobalVariable*> asOperations = getOperStruct(m, "address_space_operations");
                            for(GlobalVariable* gv : asOperations) {
                                asOperStructs.insert(gv);
                            }
                        }
                        for (GlobalVariable* gv: asOperStructs) {
                            auto res = getHandlerFromASOperations(gv, filesystemInfoItem->name);
                            bool flag = false;
                            for(pair<string, Function*> item: res) {
                                for(pair<string, Function*> i:filesystemInfoItem->SyscallHandler)
                                {
                                    if(item.first == i.first && item.second->getName() == i.second->getName())
                                    {
                                        flag = true;
                                        break;
                                    }
                                }
                                if(flag)
                                    continue;
                                filesystemInfoItem->SyscallHandler.push_back(item);
                            }
                        }
                        set<GlobalVariable*> inodeOperStructs;
                        for (Module* m: relatedModule) {       
                            vector<GlobalVariable*> inodeOperations = getOperStruct(m, "inode_operations");
                            for(GlobalVariable* gv : inodeOperations) {
                                inodeOperStructs.insert(gv);
                            }
                        }
                        for (GlobalVariable* gv: inodeOperStructs) {
                            auto res = getHandlerFromINodeOperations(gv, filesystemInfoItem->name);
                            bool flag = false;
                            for(pair<string, Function*> item: res) {
                                for(pair<string, Function*> i:filesystemInfoItem->SyscallHandler)
                                {
                                    if(item.first == i.first && item.second->getName() == i.second->getName())
                                    {
                                        flag = true;
                                        break;
                                    }
                                }
                                if(flag)
                                    continue;
                                filesystemInfoItem->SyscallHandler.push_back(item);
                            }
                        }
                        if(!cfsctxopers.empty()) {
                            for(auto& cfsco : cfsctxopers) {
                                GlobalVariable* cfsctxoper = cfsco;
                                ConstantStruct* constStructfsCtxOper = dyn_cast<ConstantStruct>(cfsctxoper->getInitializer());
                                if (!constStructfsCtxOper && Ctx->GlobalStructMap.count(cfsctxoper->getName().str())) {
                                    constStructfsCtxOper = dyn_cast<ConstantStruct>(Ctx->GlobalStructMap[cfsctxoper->getName().str()]);
                                } 
                                if (!constStructfsCtxOper) continue;
                                Constant* parseParams = constStructfsCtxOper->getOperand(Ctx->StructFieldIdx["fs_context_operations"]["parse_param"]);
                                if (parseParams && !parseParams->isNullValue() && isa<Function>(parseParams))
                                {
                                    Function* parseParamsFunc = dyn_cast<Function>(parseParams);
                                    if(parseParamsFunc != nullptr)
                                    {
                                        if(filesystemInfoItem->name == "msdos" || filesystemInfoItem->name == "vfat") {
                                            llvm::StringRef fatparse = "fat_parse_param";
                                            parseParamsFunc = getFunctionFromModules(fatparse);
                                        }
                                        if(parseParamsFunc->getInstructionCount() == 0)
                                        {
                                            parseParamsFunc = getFunctionFromModules(parseParamsFunc->getName());
                                        }
                                    }
                                
                                    if(parseParamsFunc != nullptr)
                                    {
                                        outs() << "start collect in " << parseParamsFunc->getName() << ": " << "\n";
                                        set<string> correctParamsNames = getFsParamsNames(parseParamsFunc);
                                        set<GlobalVariable*> fsParamsArrays;
                                        for (Module* m: relatedModule) { 
                                            vector<GlobalVariable*> fsparams = getFsParams(m, correctParamsNames);
                                            for(GlobalVariable* fsparam : fsparams) {
                                                fsParamsArrays.insert(fsparam);
                                            }
                                        }
                                        std::map<int, std::pair<std::string, int>> flagcollectres;
                                        std::map<std::pair<int, std::string>, std::map<int, std::string>> enumcollectres;
                                        std::map<int, std::pair<std::string, int>> intcollectres;
                                        for(GlobalVariable* fsp : fsParamsArrays) {
                                            std::map<int, std::pair<std::string, int>> tmpintcollectres;
                                            std::map<int, std::pair<std::string, int>> tmpflagcollectres = getFlagsinParams(fsp, tmpintcollectres);
                                            std::map<std::pair<int, std::string>, std::map<int, std::string>> tmpenumcollectres = getEnumsinParams(fsp);
                                            for(auto &mflag : tmpflagcollectres) {
                                                int tmpopt = mflag.first;
                                                std::pair<std::string, int> tmpstrflag = mflag.second;
                                                if(flagcollectres.find(tmpopt) == flagcollectres.end()) {
                                                    flagcollectres[tmpopt] = tmpstrflag;
                                                }
                                            }
                                            for(auto &menum : tmpenumcollectres) {
                                                std::pair<int, string> tmpopt = menum.first;
                                                std::map<int, std::string> tmpenum = menum.second;
                                                if(enumcollectres.find(tmpopt) == enumcollectres.end()) {
                                                    enumcollectres[tmpopt] = tmpenum;
                                                }
                                            }
                                            for(auto &mint : tmpintcollectres) {
                                                if(intcollectres.find(mint.first) == intcollectres.end()) {
                                                    intcollectres[mint.first] = mint.second;
                                                }
                                            }
                                        }
                                        for(auto &mflag : flagcollectres) {
                                            int flagoptnum = mflag.first;
                                            std::pair<std::string, int> flagnamenobool = mflag.second;
                                            string flagoptname = flagnamenobool.first;
                                            Ctx->fsparamsflag[filesystemInfoItem->name][flagoptnum] = flagoptname;
                                        }
                                        for(auto &mint : intcollectres) {
                                            Ctx->fsparamsint[filesystemInfoItem->name][mint.first] = mint.second;
                                        }
                                        Ctx->fsparamsenum[filesystemInfoItem->name] = enumcollectres;
                                        std::set<string> relatedSt;
                                        std::set<string> paramsparsefuncs;
                                        paramsparsefuncs.insert(parseParamsFunc->getName().str());
                                        if(filesystemInfoItem->name.find("fuse") == 0 || filesystemInfoItem->name == "virtiofs") {
                                            paramsparsefuncs.insert("fuse_parse_param");
                                            paramsparsefuncs.insert("virtio_fs_parse_param");
                                        }
                                        //记录一下这个东西代表什么，string就是结构体类型名称和字段序号构成的字符串，uint32_t就是用于设置flag的常量值，跟它在一起的字符串只会是"set"或"clear"或"enumset"或"enumclear"或"assign*"，两个int，第一个int是该选项本身的枚举值，第二个int，当uint32_t对该enum选项可以解析出值时，该值为在enum数组中的对应值，否则为-1，对普通flag选项，也为-1，对noflag，为-2，对yesflag，为-3，对老版本的基于match_token的解析，对于它的flag，记为-4，对assignint，记为-5
                                        std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> collectParamsParseRes;
                                        if(filesystemInfoItem->name == "ext4") {
                                            collectParamsParseRes = collectExt4ParamParse(parseParamsFunc->getParent(), relatedSt);
                                        } else {
                                            collectParamsParseRes = collectParamsParse(parseParamsFunc, enumcollectres, flagcollectres, intcollectres, relatedSt);
                                        }
                                        
                                        relatedSt.insert("struct.fs_context");
                                        outs() << "find related struct in " << parseParamsFunc->getName() << ": " << "\n";
                                        for(const string& ststr : relatedSt) {
                                            outs() << ststr << "\n";
                                        }
                                        outs() << "find related struct end" << "\n";
                                        for(auto& stparams: collectParamsParseRes) {
                                            string st = stparams.first;
                                            std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> paramsparses = stparams.second;
                                            for(std::pair<std::pair<uint32_t, string>, std::pair<int, int>> paramp : paramsparses) {
                                                Ctx->fs2options[filesystemInfoItem->name][st].insert(paramp);
                                            }
                                        }
                                        //Ctx->fs2options[filesystemInfoItem->name] = collectParamsParseRes;
                                        if(!collectParamsParseRes.empty()) {
                                            Constant* parseParamsold = constStructfsCtxOper->getOperand(Ctx->StructFieldIdx["fs_context_operations"]["parse_monolithic"]);
                                            if (parseParamsold && !parseParamsold->isNullValue() && isa<Function>(parseParamsold)) {
                                                Function* parseParamsoldFunc = dyn_cast<Function>(parseParamsold);
                                                if(parseParamsoldFunc != nullptr)
                                                {
                                                    if(parseParamsoldFunc->getInstructionCount() == 0)
                                                    {
                                                        parseParamsoldFunc = getFunctionFromModules(parseParamsoldFunc->getName());
                                                    }
                                                }
                                                if(parseParamsoldFunc != nullptr) {
                                                    paramsparsefuncs.insert(parseParamsoldFunc->getName().str());
                                                    if(filesystemInfoItem->name == "nfs" || filesystemInfoItem->name == "nfs4") {
                                                        paramsparsefuncs.insert("nfs23_parse_monolithic");
                                                        paramsparsefuncs.insert("nfs4_parse_monolithic");
                                                    }
                                                    //findAllParseParamsOld(parseParamsoldFunc, paramsparsefuncs);
                                                }
                                            }
                                            for (Module* m: relatedModule) {
                                                for (Function &cf : *m) {
                                                    bool hasSt = false;
                                                    Function* cfp = &cf;
                                                    for (Function::arg_iterator FI = cfp->arg_begin(), FE = cfp->arg_end(); FI != FE; ++FI) {
                                                        Type *DefinedTy = FI->getType();
                                                        while (DefinedTy->isPointerTy()) {
                                                            DefinedTy = DefinedTy->getPointerElementType();
                                                            if (DefinedTy->isStructTy()) {
                                                                string argstr = DefinedTy->getStructName().str();
                                                                if(relatedSt.find(argstr) != relatedSt.end()) {
                                                                    hasSt = true;
                                                                    break;
                                                                }
                                                            }
                                                        }
                                                    }
                                                    if(!hasSt) continue;
                                                    if(cfp->hasName() && paramsparsefuncs.find(cfp->getName().str()) != paramsparsefuncs.end()) continue;
                                            
                                                    outs() << "find matched type function: " << cfp->getName().str() << "\n";
                                                    
                                                    std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> collectOneLayer = collectOneLayerParamsProp(cfp, collectParamsParseRes);
                                                    if(collectOneLayer.size() != 0) {
                                                        for(auto col : collectOneLayer) {
                                                            pair<string, pair<uint32_t, string>> coption = col.first;
                                                            OneLayerPairSet onelayer = col.second;
                                                            for(auto onelayerfe : onelayer) {
                                                                Ctx->fs2options2onelayer[filesystemInfoItem->name][coption].insert(onelayerfe);
                                                            }
                                                        
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        // L2: extract mount option dependencies for this FS
                                         MountOptDependencyExtractor l2ext(Ctx);
                                        l2ext.extract(filesystemInfoItem->name, parseParamsFunc, relatedSt,
                                            Ctx->fs2options[filesystemInfoItem->name], Ctx->fs2options2onelayer[filesystemInfoItem->name],
                                            flagcollectres, intcollectres, enumcollectres);
                            
                                    }
                                }
                            }
                            cfsctxopers.clear();
                        }
                        else if(!Ctx->Fs2OldParseMountOptionsFuncs[filesystemInfoItem->name].empty()) {
                            set<pair<Function*, CallInst*>> OldParseFuncs = Ctx->Fs2OldParseMountOptionsFuncs[filesystemInfoItem->name];
                            for(auto &OldParseFAndC : OldParseFuncs) {
                                Function* OldParseF = OldParseFAndC.first;
                                CallInst* CallToOldParseF = OldParseFAndC.second;
                                set<string> correctParamsNames = getOldFsParamsNames(OldParseF);
                                set<GlobalVariable*> fsParamsArrays;
                                for (Module* m: relatedModule) { 
                                    vector<GlobalVariable*> fsparams = getFsOldParams(m, correctParamsNames);
                                    for(GlobalVariable* fsparam : fsparams) {
                                        fsParamsArrays.insert(fsparam);
                                    }
                                }
                                std::map<int, std::string> flagcollectres;
                                std::map<int, std::pair<std::string, int>> intcollectres;
                                std::map<int, std::string> enumcollectres;
                                for(GlobalVariable* fsp : fsParamsArrays) {
                                    std::map<int, std::pair<std::string, int>> tmpintcollectres;
                                    //std::map<std::pair<int, std::string>, std::map<int, std::string>> tmpenumcollectres;
                                    std::map<int, std::string> tmpflagcollectres = getPotentialFlagsinOldParams(fsp, tmpintcollectres, enumcollectres);
                                    for(auto &mflag : tmpflagcollectres) {
                                        int tmpopt = mflag.first;
                                        std::string tmpstrflag = mflag.second;
                                        if(flagcollectres.find(tmpopt) == flagcollectres.end()) {
                                            flagcollectres[tmpopt] = tmpstrflag;
                                        }
                                    }
                                    for(auto &mint : tmpintcollectres) {
                                        if(intcollectres.find(mint.first) == intcollectres.end()) {
                                            intcollectres[mint.first] = mint.second;
                                        }
                                    }
                                    /*for(auto &menum : tmpenumcollectres) {
                                        if(enumcollectres.find(menum.first) == enumcollectres.end()) {
                                            enumcollectres[menum.first] = menum.second;
                                        }
                                    }*/
                                }
                                for(auto &mflag : flagcollectres) {
                                    int flagoptnum = mflag.first;
                                    std::string flagoptname = mflag.second;
                                    Ctx->fsparamsflag[filesystemInfoItem->name][flagoptnum] = flagoptname;
                                }
                                for(auto &mint : intcollectres) {
                                    Ctx->fsparamsint[filesystemInfoItem->name][mint.first] = mint.second;
                                }
                                std::set<string> relatedSt;
                                std::set<string> paramsparsefuncs;
                                paramsparsefuncs.insert(OldParseF->getName().str());
                                //记录一下这个东西代表什么，string就是结构体类型名称和字段序号构成的字符串，uint32_t就是用于设置flag的常量值，跟它在一起的字符串只会是"set"或"clear"或"enumset"或"enumclear"或"assign*"，两个int，第一个int是该选项本身的枚举值，第二个int，当uint32_t对该enum选项可以解析出值时，该值为在enum数组中的对应值，否则为-1，对普通flag选项，也为-1，对noflag，为-2，对yesflag，为-3，对老版本的基于match_token的解析，对于它的flag，记为-4，对assignint，记为-5
                                std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> collectParamsParseRes;
                                if(filesystemInfoItem->name == "ext4") {
                                    collectParamsParseRes = collectExt4ParamParse(OldParseF->getParent(), relatedSt);
                                } else {
                                    std::map<int, std::map<int, std::string>> enumCollect;
                                    collectParamsParseRes = collectOldParamsParse(OldParseF, CallToOldParseF, flagcollectres, intcollectres, enumcollectres, relatedSt, enumCollect);
                                    if (!enumCollect.empty()) {
                                        for (auto& ec : enumCollect) {
                                            int enumOpt = ec.first;
                                            std::map<int, std::string> enumValueandKey = ec.second;
                                            if(enumcollectres.find(enumOpt) != enumcollectres.end()) {
                                                Ctx->fsparamsenum[filesystemInfoItem->name][std::make_pair(enumOpt, enumcollectres[enumOpt])] = enumValueandKey;
                                            }
                                        }
                                    }
                                }
                                //relatedSt.insert("struct.fs_context");
                                //outs() << "find related struct in " << parseParamsFunc->getName() << ": " << "\n";
                                //for(const string& ststr : relatedSt) {
                                    //outs() << ststr << "\n";
                                //}
                                //outs() << "find related struct end" << "\n";
                                for(auto& stparams: collectParamsParseRes) {
                                    string st = stparams.first;
                                    std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> paramsparses = stparams.second;
                                    for(std::pair<std::pair<uint32_t, string>, std::pair<int, int>> paramp : paramsparses) {
                                        Ctx->fs2options[filesystemInfoItem->name][st].insert(paramp);
                                    }
                                }
                                //Ctx->fs2options[filesystemInfoItem->name] = collectParamsParseRes;
                                if(!collectParamsParseRes.empty()) {
                                    for (Module* m: relatedModule) {
                                        for (Function &cf : *m) {
                                            Function* cfp = &cf;
                                            /*bool hasSt = false;
                                            for (Function::arg_iterator FI = cfp->arg_begin(), FE = cfp->arg_end(); FI != FE; ++FI) {
                                                Type *DefinedTy = FI->getType();
                                                while (DefinedTy->isPointerTy()) {
                                                    DefinedTy = DefinedTy->getPointerElementType();
                                                    if (DefinedTy->isStructTy()) {
                                                        string argstr = DefinedTy->getStructName().str();
                                                        if(relatedSt.find(argstr) != relatedSt.end()) {
                                                            hasSt = true;
                                                            break;
                                                        }
                                                    }
                                                }
                                            }
                                            if(!hasSt) continue;*/
                                            if(cfp->hasName() && paramsparsefuncs.find(cfp->getName().str()) != paramsparsefuncs.end()) continue;
                                            if(cfp->getInstructionCount() == 0) continue;

                                            std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> collectOneLayer = collectOneLayerParamsProp(cfp, collectParamsParseRes);
                                            if(collectOneLayer.size() != 0) {
                                                for(auto col : collectOneLayer) {
                                                    pair<string, pair<uint32_t, string>> coption = col.first;
                                                    OneLayerPairSet onelayer = col.second;
                                                    for(auto onelayerfe : onelayer) {
                                                        Ctx->fs2options2onelayer[filesystemInfoItem->name][coption].insert(onelayerfe);
                                                    }    
                                                }
                                            }
                                        }
                                    }
                                }
                                // L2: extract mount option dependencies for this FS (old-style API)
                                std::map<int, std::pair<std::string, int>> l2flagParams;
                                for (auto& f : flagcollectres) l2flagParams[f.first] = {f.second, 0};
                                //std::map<std::pair<int, std::string>, std::map<int, std::string>> l2enumParams;
                                 MountOptDependencyExtractor l2ext(Ctx);
                                l2ext.extract(filesystemInfoItem->name, OldParseF, relatedSt,
                                    Ctx->fs2options[filesystemInfoItem->name], Ctx->fs2options2onelayer[filesystemInfoItem->name],
                                    l2flagParams, intcollectres, Ctx->fsparamsenum[filesystemInfoItem->name]);
                            } 
                        }
                    }

                    set<Function*> InodeInitfuncs = Ctx->Fs2InodeInitFuncs[filesystemInfoItem->name];
                    if(!InodeInitfuncs.empty()) {
                        for(auto& initf : InodeInitfuncs) {
                            std::map<std::string, std::set<string>> ftalloc = collectFunctionTableAlloc(initf, Ctx->fsparamsenum[filesystemInfoItem->name], Ctx->fsparamsflag[filesystemInfoItem->name], Ctx->fsparamsint[filesystemInfoItem->name], Ctx->fs2options[filesystemInfoItem->name], Ctx->fs2options2onelayer[filesystemInfoItem->name]);
                            for(auto& ft: ftalloc) {
                                string ftname = ft.first;
                                set<string> ftconds = ft.second;
                                for(auto& ftc : ftconds) {
                                    Ctx->fs2functiontablealloc[filesystemInfoItem->name][ftname].insert(ftc);
                                }
                            }
                        }
                    }
                    

                    for(GlobalVariable* globalVar:filesystemInfoItem->fileOperations)
                    {
                        vector<pair<string, Function*>> res = getHandlerFromFileOperations(globalVar, filesystemInfoItem->name);
                        for(pair<string, Function*> item: res)
                        {
                            bool flag = false;
                            for(pair<string, Function*> i:filesystemInfoItem->SyscallHandler)
                            {
                                if(item.first == i.first && item.second->getName() == i.second->getName())
                                {
                                    flag = true;
                                    break;
                                }
                            }
                            if(flag)
                                continue;
                            filesystemInfoItem->SyscallHandler.push_back(item);
                        }
                    }
                }
            }
            
        }
    }

    auto xattrHandlers = getOperStruct(M, "xattr_handler");
    auto xattrHandlerStruc = Ctx->StructFieldIdx["xattr_handler"];
    for (auto handler : xattrHandlers) {
        vector<pair<string, Function*>> res = vector<pair<string, Function*>>();
        ConstantStruct* constStruct = dyn_cast<ConstantStruct>(handler->getInitializer());
        if (!constStruct) {
            outs() << "what???? should have " << handler->getName().str() << " in module: " << M->getName() << '\n' ;
            continue;
        }
        Constant* handlerGet = constStruct->getOperand(xattrHandlerStruc["get"]);
        Constant* handlerSet = constStruct->getOperand(xattrHandlerStruc["set"]);

        for (auto iterIdx: {0, 1}) {
            auto fieldName = "name"; 
            if (iterIdx == 1) {
                fieldName = "prefix";
            }
            Constant* strConst = constStruct->getOperand(xattrHandlerStruc[fieldName]);
            if (!strConst) {
                outs() << "no field: " << fieldName << '\n';
                continue;
            }
            string strVal = "";
            auto t2 = dyn_cast<ConstantExpr>(strConst);
            if (!t2) {
                continue;
            }
            auto t3 = t2->getAsInstruction(); 
            if (!t3) {
                continue;
            }
            auto t4 = dyn_cast<GetElementPtrInst>(t3);
            if (!t4) {
                continue;
            }
            auto t5 = t4->getPointerOperand();
            if (!t5) {
                continue;
            }
            auto t6 = dyn_cast<GlobalVariable>(t5);
            if (t6 && t6->hasInitializer()) {                                  
                auto t8 = dyn_cast<ConstantDataArray>(t6->getInitializer()); 
                if (t8) {
                    strVal = t8->getAsCString().str();
                }
            } else {   
                continue;
            }
            if (iterIdx == 1) {
                strVal += "*";
            }
            vector<pair<string, Function*>> SyscallHandler; 
            for (auto &handlerItem: xattrHandlerSyscallMap) {
                Constant* handlerPtr = constStruct->getOperand(xattrHandlerStruc[handlerItem.first]);
                if (!handlerPtr || !isa<Function>(handlerPtr)) {
                    continue;
                }
                Function* handlerFunc = dyn_cast<Function>(handlerPtr);
                if (handlerFunc != nullptr && handlerFunc->getInstructionCount() == 0) {
                    handlerFunc = getFunctionFromModules(handlerFunc->getName());
                }
                if (handlerFunc == nullptr) {
                    continue; 
                }
                for (auto syscall: handlerItem.second) {
                    SyscallHandler.push_back(make_pair(syscall, handlerFunc));
                }
            } 
            if (SyscallHandler.size() > 0) {
                FilesystemInfoItem* filesystemInfoItem = new FilesystemInfoItem();
                filesystemInfoItem->ItemType = FILESYSTEM;
                filesystemInfoItem->name = strVal;
                filesystemInfoItem->SyscallHandler = SyscallHandler;
                filesystemInfoItem->filesystemTypeStruct = nullptr;
                Ctx->SubsystemInfo.push_back(filesystemInfoItem);
            }
        }
    }
    return false;
}

bool FilesystemExtractorPass::doFinalization(Module* M)
{
    return false;
}

SpecialFSItem::SpecialFSItem(){}

SpecialFSItem::SpecialFSItem(FilesystemInfoItem* InfoItem){
    /* from infoitem */
    this->ItemType = InfoItem->ItemType;
    this->name = InfoItem->name;
    /* from FilesystemInfoItem */
    this->filesystemTypeStruct=InfoItem->filesystemTypeStruct;
    this->fileOperations=InfoItem->fileOperations;
    this->SyscallHandler=InfoItem->SyscallHandler;
}



string FilesystemInfoItem::generateDeviceSignature(Function*){
    return name;
}



string SpecialFSItem::generateDeviceSignature(Function* func){
    if (Func2Dev.count(func) && Func2Dev[func]!=""){
        return name+" "+Func2Dev[func];
    }
    else
        return name;
}

