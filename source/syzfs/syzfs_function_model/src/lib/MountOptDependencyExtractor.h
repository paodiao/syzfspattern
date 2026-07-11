#ifndef MOUNT_OPT_DEPENDENCY_EXTRACTOR_H
#define MOUNT_OPT_DEPENDENCY_EXTRACTOR_H

#include "Analyzer.h"

class MountOptDependencyExtractor {
private:
    GlobalContext *Ctx;

    // Extract self-dependencies from checker functions' ICmp→Branch→error_BB patterns
    void extractSelfDeps(
        const std::set<Function*>& funcs,
        const std::map<int, std::pair<std::string, int>>& flagParams,
        const std::map<int, std::pair<std::string, int>>& intParams,
        std::map<std::pair<int, std::string>, std::map<int, std::string>>& enumParams,
        std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& fs2options,
        FsDeps& deps);

    // Extract cross-option dependencies from ICmp conditions linking different fs2options entries
    void extractCrossDeps(
        const std::set<Function*>& funcs,
        const std::set<std::string>& relatedSt,
        std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& fs2options,
        std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet>& fs2options2onelayer,
        FsDeps& deps);

    // Extract silent dependencies: Branch(ICmp A) → BB with Store(And/Or on B)
    void extractSilentDeps(
        const std::set<Function*>& funcs,
        std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& fs2options,
        FsDeps& deps);

    // Trace a value (Load/ICmp operands) back to an fs2options entry
    std::string traceToFs2Options(
        Value* V,
        std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& fs2options);

    // Parse ICmp predicate to comparable string
    static std::string predToStr(CmpInst::Predicate p);

    // Merge hardcoded cross-function dependencies
    void mergeHardcodedDeps(const std::string& fsname, FsDeps& deps);

public:
    MountOptDependencyExtractor(GlobalContext *Ctx_) : Ctx(Ctx_) {}

    // Main entry: extract all dependencies for a filesystem
    void extract(
        const std::string& fsname,
        Function* parseParamsFunc,
        const std::set<std::string>& relatedSt,
        std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& fs2options,
        std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet>& fs2options2onelayer,
        const std::map<int, std::pair<std::string, int>>& flagParams,
        const std::map<int, std::pair<std::string, int>>& intParams,
        std::map<std::pair<int, std::string>, std::map<int, std::string>>& enumParams);
};

#endif
