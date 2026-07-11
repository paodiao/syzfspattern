#ifndef ANALYZER_GLOBAL_H
#define ANALYZER_GLOBAL_H

#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include "llvm/Support/CommandLine.h"
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <utility>
#include <tuple>

#include "Common.h"
// 
// typedefs
//
typedef std::pair<Instruction *, BasicBlock *> CFGEdge;
typedef vector< pair<llvm::Module*, llvm::StringRef> > ModuleList;
// Mapping module to its file name.
typedef unordered_map<llvm::Module*, llvm::StringRef> ModuleNameMap;
// The set of all functions.
typedef llvm::SmallPtrSet<llvm::Function*, 8> FuncSet;
// Mapping from function name to function.
typedef unordered_map<string, llvm::Function*> NameFuncMap;
typedef llvm::SmallPtrSet<llvm::CallInst*, 8> CallInstSet;
typedef DenseMap<Function*, CallInstSet> CallerMap;
typedef DenseMap<CallInst *, FuncSet> CalleeMap;
// Pointer analysis types.
typedef DenseMap<Value *, SmallPtrSet<Value *, 16>> PointerAnalysisMap;
typedef unordered_map<Function *, PointerAnalysisMap> FuncPointerAnalysisMap;
typedef unordered_map<Function *, AAResults *> FuncAAResultsMap;

//ErrorPaths analysis types.
typedef std::map<CFGEdge, int> EdgeErrMap;


typedef map<Type*, string> TypeNameMap;

struct CallTraceInfo {
	vector<pair<Function*, Instruction*>> callTrace;
	int depth;
	int icallNum;
	bool isSyscallEntry;
};

class RefFieldInfo {
public:
    StringRef field_type;
    string field_name;
    CallInst* callsite;
    Function* callFunc;
    Value* refobj;
//    OpType opType;

public:
    RefFieldInfo() = default;

};

typedef map<string,set<RefFieldInfo *>> RefcountFieldInfoMap; // [struct_name, <field_name, field_type, callsiye>]
typedef map<pair<string,string>, map<StringRef, size_t>> RefcountOpTimesMap;
//[(struct_name, field_name), [func_name, op_times]]
typedef std::set<std::pair<std::pair<std::string, std::pair<uint32_t, std::string>>, std::pair<std::string, uint64_t>>> OneLayerPairSet;

#define DEVICE 1
#define FILESYSTEM 2
#define NETWORK 3

class InfoItem {
	public:
	string name;
	int ItemType;
};

// L2: mount option dependency structures
struct MountOptSelfConstraint {
    int opt_token;
    string opt_name;
    string dep_type;          // "range", "discrete", "power_of_2", "hw_check", "default"
    uint64_t min_val;
    uint64_t max_val;
    set<uint64_t> valid_values;
    uint64_t def_val;
};

struct MountOptCrossDep {
    int opt_A;
    int opt_B;
    string opt_A_name;        // string name (for hardcoded deps where token is unknown)
    string opt_B_name;
    string relation;
    string src_file;
    int src_line;
};

struct FsDeps {
    vector<MountOptSelfConstraint> self;
    vector<MountOptCrossDep> cross;
};

class CMDConst;
class Signature;
struct GlobalContext {

	GlobalContext() {
		// Initialize statistucs.
		NumSecurityChecks = 0;
		NumCondStatements = 0;
	}

	unsigned NumSecurityChecks;
	unsigned NumCondStatements;
	// Map global types to type_name
	TypeNameMap GlobalTypes;

	// Map global function name to function.
	NameFuncMap GlobalFuncs;

	// Functions whose addresses are taken.
	FuncSet AddressTakenFuncs;

	// Map a callsite to all potential callee functions.
	CalleeMap Callees;

	// Map a function to all potential caller instructions.
	CallerMap Callers;

	// Map a function to all call instructions.
	CallerMap CallInsts;

	// Collected information about specific subsystems (fs, device driver, etc).
	vector<InfoItem*> SubsystemInfo;

	// Map the function args with the syscall args
	// bitwise value, 0b1 -> arg 1, 0b10 -> arg 2, 0b100 -> arg 3
	map<Function*, vector<int>> FunctionSyscallArgMap;

	// Map operation struct -> function list
	DenseMap<GlobalVariable*, FuncSet> HandlersInOperationStruct;
	
	// Map handler function -> syscall types
	std::map<Function*, string> HandlerFunctionsType;

	std::map<std::string, std::vector<Function*>> SyscallHandlerCandidates;

	// Save the structure name and index of the field
	std::map<std::string, std::map<std::string, int>> StructFieldIdx;

	// Indirect call instructions.
	std::vector<CallInst *> IndirectCallInsts;

	// Unified functions -- no redundant inline functions
	DenseMap<size_t, Function *> UnifiedFuncMap;
	set<Function *> UnifiedFuncSet;

	// Map function signature to functions
	DenseMap<size_t, FuncSet> sigFuncsMap;

	// Modules.
	ModuleList Modules;
	ModuleNameMap ModuleMaps;
	set<string> InvolvedModules;

	// SecurityChecksPass
	// Functions handling errors
	set<string> ErrorHandleFuncs;
	map<string, tuple<int8_t, int8_t, int8_t>> CopyFuncs;
	DenseMap<Function *, EdgeErrMap> ErrorPathSets;

	// Identified sanity checks
	DenseMap<Function *, set<SecurityCheck>> SecurityCheckSets;
	DenseMap<Function *, set<Value *>> CheckInstSets;

	// Functions labelled
	set<string> GroundTruthFuncs;

	// Allocate function
	set<string> AllocFuncs;

	// Pointer analysis results.
	FuncPointerAnalysisMap FuncPAResults;
	FuncAAResultsMap FuncAAResults;

	// global struct map
	map<string, Value*> GlobalStructMap;

	map<string, pair<int8_t, int8_t>> DataFetchFuncs;


	map<StringRef,StructType*>StructTypeMap;
	set<StructType*>StructTypeSet;
	map<StringRef,set<StringRef>> embeddedMap;

	map<Function*, map<unsigned, vector<CMDConst*>>> FoundFunctionCache;
	vector<Signature*> AllSignatures;

	map<string, vector<int>> FunctionArgMap;

	string CaseSrcDir;

	map<string, std::set<Function*>> Fs2InodeInitFuncs;
	map<string, std::set<std::pair<Function*, CallInst*>>> Fs2OldParseMountOptionsFuncs;
	map<string, std::map<string, set<string>>> Fs2EntryFunc2FuncTable;
	map<string, std::map<std::pair<int, std::string>, std::map<int, std::string>>> fsparamsenum;
	map<string, std::map<int, string>> fsparamsflag;
	map<string, std::map<int, std::pair<std::string, int>>> fsparamsint;
	map<string, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>> fs2options;
	// One-layer propagation storage with cmp_info for assignint/assignenum
	// outer key: pair<storage_key, pair<flag_const, cfgtype>>  — NO cmp_info
	// inner element: pair<pair<storage_key, pair<flag_const, cfgtype>>, pair<cmp_op, cmp_val>>
	// typedef std::pair<std::pair<std::string, std::pair<uint32_t, std::string>>, std::pair<std::string, uint64_t>> OneLayerVal;
	map<string, std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet>> fs2options2onelayer;
	map<string, std::map<std::string, std::set<string>>> fs2functiontablealloc;
	map<string, FsDeps> fs2deps;
};

extern GlobalContext GlobalCtx;

class IterativeModulePass {
protected:
	GlobalContext *Ctx;
	const char * ID;
public:
	IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
		: Ctx(Ctx_), ID(ID_) { }

	// Run on each module before iterative pass.
	virtual bool doInitialization(llvm::Module *M)
		{ return true; }

	// Run on each module after iterative pass.
	virtual bool doFinalization(llvm::Module *M)
		{ return true; }

	// Iterative pass.
	virtual bool doModulePass(llvm::Module *M)
		{ return false; }

	virtual void run(ModuleList &modules);
};

#endif
