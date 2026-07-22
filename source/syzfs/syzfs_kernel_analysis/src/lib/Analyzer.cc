//===-- Analyzer.cc - the kernel-analysis framework--------------===//
//
// This file implements the analysis framework. It calls the pass for
// building call-graph and the pass for finding security checks.
//
// ===-----------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/JSON.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/PostDominators.h"
//#include "llvm/Analysis/ControlDependence.h"
#include <llvm/IR/InstIterator.h>



#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>
#include <filesystem>
#include <boost/algorithm/string/predicate.hpp>

#include "Analyzer.h"
#include "CallGraph.h"
#include "Constraint.h"
#include "Config.h"

#include "TypeInitializer.h"
#include "ControlDependenceGraph.h"

#include "Distance.h"
#include <time.h>
#include <llvm/IR/Dominators.h>

using namespace llvm;

// Command line parameters.
// cl::list<string> InputFilenames(
//     cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<string> TargetPointFile(
	"target-points", cl::desc("File that contain target point information (idx src_file:line)")
);

cl::opt<string> TargetPoint(
	"target-point", cl::desc("src file:line")
);

cl::opt<string> distanceOutput(
	"distance-output", cl::desc("block distance ouput dir")
);

cl::opt<string> MultiPositionPoints(
	"multi-pos-points", cl::desc("declare target function if has multiple function position")
);

cl::opt<int> TargetIndex(
	"target-index", cl::desc("target xidx"),  cl::init(-1)
		);

cl::opt<string> KernelInterfaceFile(
	"kernel-interface-file", cl::desc("kernel interface file (syztg result) path"), cl::init("")
);

cl::opt<string> FsparamsFlagFile(
	"fsparams-flag-file", cl::desc("fsparams flag file path"), cl::init("")
);

cl::opt<string> FsparamsEnumFile(
	"fsparams-enum-file", cl::desc("fsparams enum file path"), cl::init("")
);

cl::opt<string> Fs2OptionsFile(
	"fs2options-file", cl::desc("fs2options file path"), cl::init("")
);

cl::opt<string> Fs2Options2OnelayerFile(
	"fs2options2onelayer-file", cl::desc("fs2options2onelayer file path"), cl::init("")
);

cl::opt<string> FsparamsIntFile(
	"fsints-file", cl::desc("fsparams int file path"), cl::init("")
);

cl::opt<string> SuperblockMappingDir(
	"superblock-mapping-dir", cl::desc("directory containing superblock_mapping_*.json files"), cl::init("")
);

cl::opt<string> kernelBCDir(
	cl::Positional, cl::OneOrMore, cl::desc("kernel bitcode dir")
);

cl::opt<unsigned> VerboseLevel(
		"verbose-level", cl::desc("Print information at which verbose level"),
		cl::init(0));

cl::opt<string> SourceLocation(
				"source-location", cl::desc("Input the target source code location"),
				cl::init("linux"));

cl::opt<bool> SecurityChecks(
		"sc",
		cl::desc("Identify sanity checks"),
		cl::NotHidden, cl::init(false));

cl::opt<bool> MissingChecks(
		"mc",
		cl::desc("Identify missing-check bugs"),
		cl::NotHidden, cl::init(false));

// GlobalContext GlobalCtx;
GlobalContext GlobalCtx = GlobalContext();
map<string,pair<string,string>> SpecialConstraintMap;
#include <iostream>
#include <map>
#include <string>

std::map<std::string, std::string> comparisonOpposites = {
    {"<", ">="},
    {"<=", ">"},
    {">", "<="},
    {">=", "<"},
    {"=", "!="},
    {"!=", "="}
};


void IterativeModulePass::run(ModuleList &modules) {

	ModuleList::iterator i, e;
	OP << "[" << ID << "] Initializing " << modules.size() << " modules ";
	bool again = true;
	while (again) {
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			again |= doInitialization(i->first);
			OP << ".";
		}
	}
	OP << "\n";

	unsigned iter = 0, changed = 1;
	while (changed) {
		++iter;
		changed = 0;
		unsigned counter_modules = 0;
		unsigned total_modules = modules.size();
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			OP << "[" << ID << " / " << iter << "] ";
			OP << "[" << ++counter_modules << " / " << total_modules << "] ";
			OP << "[" << i->second << "]\n";

			bool ret = doModulePass(i->first);
			if (ret) {
				++changed;
				OP << "\t [CHANGED]\n";
			} else
				OP << "\n";
		}
		OP << "[" << ID << "] Updated in " << changed << " modules.\n";
	}

	OP << "[" << ID << "] Postprocessing ...\n";
	again = true;
	while (again) {
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			// TODO: Dump the results.
			again |= doFinalization(i->first);
		}
	}

//  OP << "[" << ID << "] Done!\n\n";
}

void ProcessResults(GlobalContext *GCtx) {
}

void PrintResults(GlobalContext *GCtx) {
	OP<<"############## Result Statistics ##############\n";
	OP<<"# Number of sanity checks: \t\t\t"<<GCtx->NumSecurityChecks<<"\n";
	OP<<"# Number of conditional statements: \t\t"<<GCtx->NumCondStatements<<"\n";
}

int getBasicBlockIndex(BasicBlock* BB)
{
    Function* F = BB->getParent();
    int i = -1;
    for(auto iter = F->begin(); iter != F->end(); iter++)
    {
        i++;
        BasicBlock* bb = &*iter;
        if(bb == BB)
        {
            break;
        }
    }
    return i;
}

bool isSyscall(Function* F) {
	string FuncName = static_cast<string>(F->getName());
	if (FuncName.size() > 0) {
		if (startsWith(FuncName, "__do_sys_") || startsWith(FuncName, "__se_sys_")) {
			return true;
		}
		if (startsWith(FuncName, "__x64_sys_")) {
			return true;
		}
	}
	return false;
}

string getSyscallName(Function* F) {
	string FuncName = static_cast<string>(F->getName());
	if (FuncName.size() > 0) {
		if (startsWith(FuncName, "__do_sys_") || startsWith(FuncName, "__se_sys_")) {
			return FuncName.substr(9);
		}
		if (startsWith(FuncName, "__x64_sys_")) {
			return FuncName.substr(10);
		}
	}
	return "";
}

void getCallTrace(BasicBlock* targetBlock, vector<CallTraceInfo> &callTraces) {
	// input: target block
	// output: call trace: from syscall to target block
	// return a <Function*, Inst*> pair vector for each syscall,
	// the last pair is <Function*, the first inst in the target block>
	// the other pair is <Function*, call inst of next function>
	queue<pair<Function*, int>> q;
	map<Function*, set<pair<Function*, CallInst*>>> callerHistory; // A -> set of <B, (call B) in A>
	unordered_set<Function*> entryList;
	map<Function*, int> visit;

	Function* targetFunction = targetBlock->getParent();
	string targetFunctionName = targetFunction->getName().str();


	q.push(make_pair(targetFunction, 0));
	visit[targetFunction] = 1;

	int maxCallTrace = 2;
	int maxIndirectCallNum = 2;

	map<Function*, unordered_set<Function*>> preNodeSet;

	while (!q.empty()) {
		Function *F = q.front().first;
		int original_currentIndirectCallNum = q.front().second;
		q.pop();

		for (auto callerFunc: GlobalCtx.MissingCallerMap[F]) {
			if (visit.count(callerFunc) != 0) continue;
			visit[callerFunc] += 1;
			callerHistory[callerFunc].insert(make_pair(F, nullptr));
			q.push(make_pair(callerFunc, original_currentIndirectCallNum));
		}
		size_t fh = funcHash(F);
		Function* unifiedFunc= GlobalCtx.UnifiedFuncMap[fh];
		for (auto callInst: GlobalCtx.Callers[unifiedFunc]) {
			Function *callerFunc = callInst->getFunction();
			int currentIndirectCallNum = original_currentIndirectCallNum;
			if (GlobalCtx.FPCallerMap.count(F) != 0 && GlobalCtx.FPCallerMap[F].count(callerFunc) != 0) {
				continue;
			}

			if (entryList.count(callerFunc) != 0) {
				if (visit[callerFunc] >= maxCallTrace) continue;
			} else {

				if (visit.count(callerFunc) != 0) {
					continue;
					// if (visit[callerFunc] >= maxCallTrace) continue;
					// if (preNodeSet.count(callerFunc) != 0 && preNodeSet[callerFunc].count(F) != 0) continue;
				}
			}

			if (callInst->isIndirectCall()) {
				currentIndirectCallNum += 1;
				if (currentIndirectCallNum > maxIndirectCallNum) continue;
			}

			visit[callerFunc] += 1;

			callerHistory[callerFunc].insert(make_pair(F, callInst));

			string FuncName = callerFunc->getName().str();
			if (FuncName.size() > 0) {
				if (GlobalCtx.kernelSig2syscallVariant.count(FuncName) != 0) {
					entryList.insert(callerFunc);
					continue;
				}
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
				path.push_back(make_pair(F, &*targetBlock->begin()));
				CallTraceInfo callTraceInfo;
				callTraceInfo.callTrace = path;
				if (GlobalCtx.kernelSig2syscallVariant.count(targetFunctionName) != 0){
					callTraceInfo.depth = 1;
					callTraceInfo.icallNum = 0;
					callTraceInfo.isSyscallEntry = isSyscall(targetFunction);
					callTraces.push_back(callTraceInfo);
					return;
				}
				else {
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
				}

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
}


bool findConstInSwitch(vector<pair<Function*, Instruction*>> &callTrace, string &importFunc, uint64_t &constNum, string &constStrName) {
	// return true if successfully find the target const option
	// else return false
	// constNum: case concrete number
	// srcFileName and lineNum are helpful to find case string name, and used to filter "const number -> multiple syscall variant"

	int callTraceNum = callTrace.size();
	if (callTraceNum == 0) return false;
	for (int i = callTraceNum-1; i >=0; --i) {
		Function *F = callTrace[i].first;
		Instruction *I = callTrace[i].second;
		if (I == nullptr) continue;
		string funcName = static_cast<string>(F->getName());
		// iter pred to find switch
		BasicBlock *BB = I->getParent();

		queue<pair<BasicBlock*, BasicBlock*>> q;
		set<BasicBlock*> visit;
		visit.insert(BB);

		for (BasicBlock *predBB: predecessors(BB)) {
			q.push(make_pair(predBB, BB));
			visit.insert(predBB);
		}
		while (!q.empty()) {
			BasicBlock *B = q.front().first;
			BasicBlock *nextB = q.front().second;
			q.pop();
			// find switch
			for (auto it = B->begin(); it != B->end(); ++it) {
				Instruction *inst = &*it;
				if (SwitchInst *SI = dyn_cast<SwitchInst>(inst)) {
					if (SI->getNumOperands() == 0) continue;

					for (auto c: SI->cases()) {
						int lineNum = -1;
						string srcFileName;
						if (c.getCaseSuccessor() != nextB) continue;
						// try to get the line number of "case xxx:"

						// if nextB like following:
						//  call void @__sanitizer_cov_trace_pc() #10, !dbg !12804
						//  br label %883, !dbg !12804
						// the line number is incorrect, so we need to find the correct line number using the next block of nextB
						bool specialCase = false;
						if (nextB->getInstList().size() == 2) {
							Instruction* I = &nextB->getInstList().front();
							if (CallInst* CI = dyn_cast<CallInst>(I)) {
								Function* calledF = CI->getCalledFunction();
								if (calledF && calledF->getName().str() == "__sanitizer_cov_trace_pc") {
									specialCase = true;
								}
							}
						}
						if (specialCase)
							nextB = nextB->getSingleSuccessor();


						for (auto nextBiter=nextB->begin(); nextBiter != nextB->end(); nextBiter++) {
							Instruction *nextBinst = &*nextBiter;
							if (DILocation *Loc = nextBinst->getDebugLoc()) {
								if (Loc->getLine() == 0) {
									if (Loc->getInlinedAt()) {
										lineNum = Loc->getInlinedAt()->getLine();
										break;
									} else {
										continue;
									}
								} else {
									lineNum = Loc->getLine();
									break;
								}
							}
						}
						importFunc = funcName;
						srcFileName =  F->getParent()->getSourceFileName();
						constNum = c.getCaseValue()->getZExtValue();
						lineNum -= 1;

						// loop 2 times to deal with conner case like following:
						// case xxx:
						// {

						for (int j = 0; j < 2; j++) {
							if (srcFileName != "" && lineNum > 0) {
								ifstream file(srcFileName);
								gotoLine(file, lineNum);
								string line;
								getline(file, line);
								strip(line);
								int idx = line.find(":");
								// TODO: 一连串case的情况，可以匹配多个case
								// TODO: case33 case下一行是一个括号
								if (startsWith(line, "case ") && idx != string::npos) {
									string caseStr = line.substr(5, idx-5);
									if (caseStr == "") continue;
									if (caseStr[0] >= '0' && caseStr[0] <= '9') continue;
									// find succ
									constStrName = caseStr;
									file.close();
									return true;
								}
								file.close();
							}
							lineNum -= 1;
						}
					}
				}
			}
			// iter bb
			for (BasicBlock *predBB: predecessors(B)) {
				if (visit.count(predBB) != 0) continue;
				visit.insert(predBB);
				q.push(make_pair(predBB, B));
			}
		}
	}
	return false;
}

void collectAllPredBlock(BasicBlock *bb, set<BasicBlock*> &predBlockSet) {
	predBlockSet.insert(bb);
	for (BasicBlock *pred: predecessors(bb)) {
		if (predBlockSet.count(pred) == 0) {
			collectAllPredBlock(pred, predBlockSet);
		}
	}
}

void collectAllPredBlock(BasicBlock *bb, vector<BasicBlock*> &predBlockVector) {
	predBlockVector.push_back(bb);
	for (BasicBlock *pred: predecessors(bb)) {
		if (std::find(predBlockVector.begin(),predBlockVector.end(),pred) == predBlockVector.end()) {
			collectAllPredBlock(pred, predBlockVector);
		}
	}
}


void dumpValueAsOperand(Value* v){
	v->printAsOperand(OP);
	OP << "\n";
}

string GetConstName(Function* F,Instruction* Target){

	string line,constname;
	getSourceCodeLine(Target,line);

	string srcFileName =  F->getParent()->getSourceFileName();

	int lineNum=-1;
	if (DILocation *Loc = Target->getDebugLoc()) {
		if (Loc->getLine() == 0) {
			if (Loc->getInlinedAt()) {
				lineNum = Loc->getInlinedAt()->getLine();
				return "";
			} else {
				return "";
			}
		} else {
			lineNum = Loc->getLine();
		}
	}
	if(lineNum==-1){
		DEBUG("Fail to get linenum!!!\n");
	}
	line = getSourceLine(srcFileName,lineNum);
	if (line!="") {

		// TODO: REGEX
		int leftpos = line.find("[");
		int rightpos = line.find("]",leftpos);
		constname = line.substr(leftpos+1,rightpos-leftpos-1);

		for(auto c:constname) {
			// into->attr[idx] where idx is a variable
			if (islower(c)) {
				constname = "";
				break;
			}
		}
	}
	return constname;
}
void findConstFromIf(vector<pair<Function*, Instruction*>> &callTrace, set<pair<uint64_t,string>> &constSet){
	int callTraceNum = callTrace.size();
	if (callTraceNum == 0) return;
	constSet.clear();
	for (int i = callTraceNum-1; i >=0; --i) {
		Function *F = callTrace[i].first;
		Instruction *I = callTrace[i].second;
		if (I == nullptr) continue;
		string funcName = static_cast<string>(F->getName());
		// iter pred to find switch
		BasicBlock *BB = I->getParent();
		set<BasicBlock*> visit;
		collectAllPredBlock(BB,visit);

		Value* ArrayRoot=NULL;
		for(auto BB:visit){
			for (BasicBlock::iterator I = BB->begin(),
									 IE = BB->end(); I != IE; ++I) {
				if (LoadInst *LI = dyn_cast<LoadInst>(&*I)) {
					auto oriType = LI->getType();
					int id=0;
					while (oriType->isPointerTy()) {
						oriType = oriType->getPointerElementType();
						id++;
					}
					if (!oriType->isStructTy() || oriType->getStructName() != "struct.nlattr" || id!=2)
						continue;
					ArrayRoot=LI;

					break;

				}
			}
			if(ArrayRoot)
				break;
		}
//  what if the argument itself is nlattr**?
		if (!ArrayRoot){
			for(auto& arg: F->args()){
				auto argType = arg.getType();
				int id=0;
				while (argType->isPointerTy()) {
					argType = argType->getPointerElementType();
					id++;
				}
				if (!argType->isStructTy() || argType->getStructName() != "struct.nlattr" || id!=2)
					continue;
				ArrayRoot=&arg;
			}
		}
		if(!ArrayRoot)
			continue;

		// For if (!attr[B]) callsite;
		// Find direct precondition block
		BasicBlock* CurrentBlock=I->getParent();
		BasicBlock* pred = CurrentBlock->getUniquePredecessor();

		if(pred){
			if(BranchInst* BI= dyn_cast<BranchInst>(pred->getTerminator())){
				int takenIdx = BI->getSuccessor(1)==CurrentBlock;
				if(ICmpInst* ICmp= dyn_cast<ICmpInst>(BI->getCondition())){
					if(isa<ConstantPointerNull>(ICmp->getOperand(1))){
						if(((ICmp->getPredicate()==llvm::CmpInst::ICMP_NE) && !takenIdx) || ((ICmp->getPredicate()==llvm::CmpInst::ICMP_EQ) && takenIdx)){
						 if(Instruction* target= dyn_cast<Instruction>(ICmp->getOperand(0))){
							 if(LoadInst* LI= dyn_cast<LoadInst>(target)){
								 if(GetElementPtrInst* Gep= dyn_cast<GetElementPtrInst>(LI->getPointerOperand())){
									 if(Gep->getNumOperands()==2 && Gep->getOperand(0)==ArrayRoot){
										 ConstantInt* offset= dyn_cast<ConstantInt>(Gep->getOperand(1));
										 string constname=GetConstName(F,BI);
										 if(constname!=""){
											 constSet.insert(make_pair(offset->getZExtValue(),constname));

											 INFO("Successfully get constname from precondition:" << constname << "\n");
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



		// collect all block return error
		set<ReturnInst*> retset;
		findReturnInFunc(F,retset);
		if(retset.empty())
			continue;
		ReturnInst* RI=*retset.begin();
		Value* RV=RI->getReturnValue();
		set<BasicBlock *> ReturnErrorBlocks;
		if(RV) {
			int phi_layer = 2;

			if (PHINode *PHIRV = dyn_cast<PHINode>(RV)) {
				queue<pair<PHINode *, int>> q;
				q.push(make_pair(PHIRV, 0));
				set<PHINode *> visitedPHI;
				set<pair<BasicBlock *, BasicBlock *>> ReturnErrorEdges;
				set<BasicBlock *> visitedBBs;
				queue<BasicBlock *> toPropagate;
				while (!q.empty()) {
					PHINode *PHI = q.front().first;
					int currentlayer = q.front().second;
					q.pop();
					visitedPHI.insert(PHI);
					visitedBBs.insert(PHI->getParent());
					for (int i = 0; i < PHI->getNumIncomingValues(); i++) {
						Value *IncomingV = PHI->getIncomingValue(i);
						if (ConstantInt *ConstInt = dyn_cast<ConstantInt>(IncomingV)) {
							int intval = ConstInt->getSExtValue();
							if (intval < 0 && intval > -4096) {
								BasicBlock *IncomingBB = PHI->getIncomingBlock(i);
								ReturnErrorEdges.insert(make_pair(PHI->getIncomingBlock(i), PHI->getParent()));
								toPropagate.push(IncomingBB);
								visitedBBs.insert(IncomingBB);
							}
						} else if (PHINode *NPHI = dyn_cast<PHINode>(IncomingV)) {
							if (currentlayer + 1 < phi_layer && visitedPHI.find(NPHI) == visitedPHI.end()) {
								q.push(make_pair(NPHI, currentlayer + 1));
							}
						}
					}
				}

				while (!toPropagate.empty()) {
					BasicBlock *currBB = toPropagate.front();
					toPropagate.pop();
					ReturnErrorBlocks.insert(currBB);
					for (auto pred: predecessors(currBB)) {
						if(ReturnErrorBlocks.find(pred)!=ReturnErrorBlocks.end())
							continue;
						bool AllErr = true;
						for (auto succ: successors(pred)) {
							if (succ != currBB && ReturnErrorEdges.find(make_pair(pred, succ)) == ReturnErrorEdges.end()) {
								AllErr = false;
								break;
							}
						}
						if (AllErr) {
							ReturnErrorEdges.insert(make_pair(pred, currBB));
							toPropagate.push(pred);
						}
					}
				}
			} else
				continue;
		}
		else{
			// TODO: return void
			;
		}

		DominatorTree DT = DominatorTree();
		DT.recalculate(*F);

		for (auto usr: ArrayRoot->users()) {
			if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(usr)) {
				if(visit.count(GEP->getParent())==0)
					continue;
				if(GEP->getNumOperands()<2 || !isa<ConstantInt>(GEP->getOperand(1)))
					continue;
				for(auto gepusr: GEP->users()) {
					if(!isa<LoadInst>(gepusr))
						continue;
					if(visit.count(GEP->getParent())==0)
						continue;
					for(auto liuser: gepusr->users()){
						if(ICmpInst* icmp= dyn_cast<ICmpInst>(liuser)){
							if(icmp->getOperand(0) != gepusr)
								continue;
							for(auto icmpusr: icmp->users()){
								BranchInst* BI= dyn_cast<BranchInst>(icmpusr);
								if(!BI || BI->isUnconditional())
									continue;
								int takenIdx= -1;
								if(isa<ConstantPointerNull>(icmp->getOperand(1))){
									if(icmp->getPredicate()==CmpInst::ICMP_EQ)
										takenIdx=1;
								}
								else{
									if(icmp->getPredicate()==CmpInst::ICMP_NE)
										takenIdx=0;
								}
								if(takenIdx==-1)
									continue;

								// if(!attr[something])
								BasicBlock* nextblock=BI->getSuccessor(!takenIdx);
								bool reject=false;
								if(RV)
									reject = (ReturnErrorBlocks.find(nextblock)!=ReturnErrorBlocks.end());
								else{
									if(succ_size(nextblock)==1 && nextblock->size()<10 && nextblock->getSingleSuccessor()==RI->getParent()){
										// only easy return
										reject=true;
									}
								}
								if(!reject)
									continue;



								// nested if check
								bool nested=false;
								queue<BasicBlock*> worklistsucc,worklistpred;
								worklistsucc.push(BI->getSuccessor(takenIdx));
								set<BasicBlock*> visitedsuccbbs;
								while(!worklistsucc.empty()){
									BasicBlock *bb=worklistsucc.front();
									worklistsucc.pop();
									if(visitedsuccbbs.find(bb)!=visitedsuccbbs.end())
										continue;
									visitedsuccbbs.insert(bb);
									for(auto succ: successors(bb)){
										if(pred_size(succ)==1){
											worklistsucc.push(bb);
										}
										else if(bb==RI->getParent())
											continue;
										else if(pred_size(succ)>1){
											for(auto pred: predecessors(succ)){
												if(pred!=bb)
													worklistpred.push(pred);
											}

										}
									}
								}
								while(!worklistpred.empty()){
									BasicBlock *bb=worklistpred.front();

									worklistpred.pop();
									for(auto pred: predecessors(bb)){
										if(succ_size(pred)==1)
											worklistpred.push(bb);
										else if(succ_size(pred)>1){
											if(DT.dominates(pred,BI->getParent())){
												nested=true;
												break;
											}

										}
									}
								}

								if(nested)
									continue;

								string constname=GetConstName(F,BI);
								if(constname=="")
									continue;
								INFO("Successfully get constname:" << constname << "\n");
								ConstantInt* constval= dyn_cast<ConstantInt>(GEP->getOperand(1));
								constSet.insert(make_pair(constval->getZExtValue(),constname));
							}



						}
					}
				}
			}
		}


	}

}

Function* getFunctionFromModules(StringRef funcName)
{
   Function* func = nullptr; 
   for(pair<Module*, StringRef> item : GlobalCtx.Modules)
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

set<Instruction*> TryGetMountOptInIfCall(CallInst* ifCall) {
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

void TryMatchCallInIf(CallInst* ifCall, std::map<std::pair<int, std::string>, std::map<int, std::string>> &sigfsparamsenum, std::map<int, string> &sigfsparamsflag, 
	std::map<int, std::pair<std::string, int>> &sigfsparamsint,
	std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> &sigfs2options, std::map<std::pair<std::string, std::pair<uint32_t, string>>, OneLayerPairSet> &sigfs2options2onelayer,
	const vector<SuperblockMappingEntry> &sm,
    set<pair<string, string>> &pathConstraints, bool isno)
{
	//修改：似乎现在还会考虑大于和小于的情况？那isno这个设计也要做相应补充，即对于isno的情况也要反过来
	Function *callee = ifCall->getCalledFunction();
    if(callee == nullptr)
    {
        callee = dyn_cast<Function>(ifCall->getCalledOperand()->stripPointerCasts());
    }
    if(callee == nullptr) return;
    if(callee->isIntrinsic()) return;
    if(callee->getInstructionCount() == 0)
    {
        callee = getFunctionFromModules(callee->getName());
    }
    if(callee == nullptr) return;
    if(callee->getInstructionCount() == 0) return;
	if(!callee->hasName()) return;
	string funcname = callee->getName().str();
	// Patterns A-2: match callee funcname against sm kernel_func
	for (const auto &entry : sm) {
		if (entry.kernel_func.empty()) continue;
		if (entry.transform == "bitmask_check" || entry.transform == "direct" ||
			entry.transform == "log2_scale" || entry.transform == "conditional") {
			if (funcname.find(entry.kernel_func) != string::npos) {
				string prefix = "mkfs:";
				if (isno) prefix += "^";
				pathConstraints.insert({entry.confd_param, prefix});
			}
		}
	}
	std::pair<std::string, std::pair<uint32_t, string>> currStAndConst;
	if(endsWith(funcname, "test_bit")) {
		ConstantInt* constantInt = dyn_cast<ConstantInt>(ifCall->getOperand(0));
        if(constantInt != nullptr) {
            unsigned int bitmaskoff = constantInt->getZExtValue();
            unsigned int flagcollect = 0xffffffff;
			flagcollect &= (1UL << bitmaskoff);
            GetElementPtrInst* gepi = dyn_cast<GetElementPtrInst>(ifCall->getOperand(1));
            if(gepi) {
                Type *flagPTy = gepi->getPointerOperand()->getType();
                Type *flagTy = flagPTy->getPointerElementType();
                if (flagTy->isStructTy() && gepi->hasAllConstantIndices() && gepi->getNumIndices() == 2)
                {
                    auto offsetVal = gepi->getOperand(2);
                    auto offsetInt = dyn_cast<ConstantInt>(offsetVal);
                    int offsetinst = offsetInt->getZExtValue();
                    string flagtost = gepi->getSourceElementType()->getStructName().str() + std::to_string(offsetinst);
					currStAndConst = std::make_pair(flagtost, std::make_pair(flagcollect, isno ? "clear" : "set"));
					if(sigfs2options2onelayer.find(currStAndConst) == sigfs2options2onelayer.end()) {
						currStAndConst = std::make_pair(flagtost, std::make_pair(flagcollect, isno ? "enumclear" : "enumset"));
						if(sigfs2options2onelayer.find(currStAndConst) == sigfs2options2onelayer.end()) {
							currStAndConst = std::make_pair(flagtost, std::make_pair(0xffffffff, "assignenum"));
							if (sigfs2options2onelayer.find(currStAndConst) == sigfs2options2onelayer.end()) {
								currStAndConst = std::make_pair(flagtost, std::make_pair(0xffffffff, "assignint"));
								if (sigfs2options2onelayer.find(currStAndConst) == sigfs2options2onelayer.end()) {
									return;
								}
							}
						}
							
					}
					auto targetmounts = sigfs2options2onelayer[currStAndConst];
					for(auto& OptStConstconf : targetmounts) {
						string optSt = OptStConstconf.first.first;
						uint32_t setOptConst = OptStConstconf.first.second.first;
						string setOptStr = OptStConstconf.first.second.second;
						std::pair<std::string, uint64_t> cmpopandv = OptStConstconf.second;
						if(setOptConst == 0xffffffff && setOptStr != "assignenum" && setOptStr != "assignint") continue;
						std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[optSt];
						for(auto& constfeandconf : constandfe) {
							std::pair<uint32_t, string> constfe = constfeandconf.first;
							if(constfe.first != setOptConst || constfe.second != setOptStr) continue;
							if(constfe.second == "assignenum" || constfe.second == "assignint") {
								// sentinel flagconst 0xffffffff, skip const matching
							} else if(isno) {
								if(constfe.second != "clear" && constfe.second != "enumclear" && constfe.second != "bitfieldclear") continue;
							} else {
								if(constfe.second != "set" && constfe.second != "enumset" && constfe.second != "bitfieldset") continue;
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
									pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
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
										pathConstraints.insert(std::make_pair(intname, op + std::to_string(cmpopandv.second)));
									} else {
										if(isno) op = "!="; else op = "=";
										pathConstraints.insert(std::make_pair(intname, op + std::to_string(flagcollect)));
									}
									continue;
								}
								string flagoptstr = sigfsparamsflag[optnum];
								if(!flagoptstr.empty()) {
									if(optstatus == -2) flagoptstr = "no" + flagoptstr;
									pathConstraints.insert(std::make_pair(flagoptstr, " "));
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
														pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
													}
												}
											} else {
												for (auto& enumvs : enumsvalueandstr) {
													if (enumvs.first == flagcollect) {
														if (isno) op = "!="; else op = "=";
														pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
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
		return;
	}
	
	string flagtofunc = funcname + ":function";
	if(isno) {
		currStAndConst = std::make_pair(flagtofunc, std::make_pair(0xfffffff0, "functionretfalse"));
	} else {
		currStAndConst = std::make_pair(flagtofunc, std::make_pair(0xfffffff1, "functionrettrue"));
	}
	if(sigfs2options2onelayer.find(currStAndConst) == sigfs2options2onelayer.end()) return;
	auto targetmounts = sigfs2options2onelayer[currStAndConst];
	for(auto& OptStConstconf : targetmounts) {
		string optSt = OptStConstconf.first.first;
		uint32_t setOptConst = OptStConstconf.first.second.first;
		string setOptStr = OptStConstconf.first.second.second;
		std::pair<std::string, uint64_t> cmpopandv = OptStConstconf.second;
		if(setOptConst == 0xffffffff && setOptStr != "assignenum" && setOptStr != "assignint") continue;
		std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[optSt];
		for(auto& constfeandconf : constandfe) {
			std::pair<uint32_t, string> constfe = constfeandconf.first;
			if(constfe.first != setOptConst || constfe.second != setOptStr) continue;
			if(constfe.second == "assignenum" || constfe.second == "assignint") {
				// sentinel flagconst 0xffffffff, skip const matching
			} else if(isno) {
				if(constfe.second != "clear" && constfe.second != "enumclear" && constfe.second != "bitfieldclear") continue;
			} else {
				if(constfe.second != "set" && constfe.second != "enumset" && constfe.second != "bitfieldset") continue;
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
					pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
				}
			} else {
				// flag or enum, but do not consider enum now
				int optnum = flagorenumopt.first;
				int optstatus = flagorenumopt.second;
				// check int params first
				auto it_int = sigfsparamsint.find(optnum);
				if(it_int != sigfsparamsint.end()) {
					string intname = it_int->second.first;
					string op = "";
					if (cmpopandv.first != "") {
						if (isno) op = comparisonOpposites[cmpopandv.first]; else op = cmpopandv.first;
						pathConstraints.insert(std::make_pair(intname, op + std::to_string(cmpopandv.second)));
					}
				} else {
					string flagoptstr = sigfsparamsflag[optnum];
					if(!flagoptstr.empty()) {
						if(optstatus == -2) flagoptstr = "no" + flagoptstr;
						pathConstraints.insert(std::make_pair(flagoptstr, " "));
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
											pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
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

void findFsConstFromIf(vector<set<pair<string, string>>> &fsMountConstraintGroups, vector<pair<Function*, Instruction*>> &callTrace, 
					std::map<std::pair<int, std::string>, std::map<int, std::string>> &sigfsparamsenum, std::map<int, string> &sigfsparamsflag, 
					std::map<int, std::pair<std::string, int>> &sigfsparamsint,
					std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> &sigfs2options, std::map<std::pair<std::string, std::pair<uint32_t, string>>, OneLayerPairSet> &sigfs2options2onelayer,
					const map<pair<string, unsigned>, vector<const SuperblockMappingEntry*>> &field_to_params,
					const vector<SuperblockMappingEntry> &sm)
{
	int callTraceNum = callTrace.size();
	if (callTraceNum == 0) return;

	vector<vector<set<pair<string, string>>>> allFuncSets;
	//constSet.clear();
	for (int i = callTraceNum-1; i >=0; --i) {
		Function *F = callTrace[i].first;
		Instruction *I = callTrace[i].second;
		if (I == nullptr) continue;
		string funcName = static_cast<string>(F->getName());
		// iter pred to find if
		BasicBlock *tBB = I->getParent();
		set<BasicBlock*> visit;
		collectAllPredBlock(tBB,visit);
		DominatorTree DT = DominatorTree();
		DT.recalculate(*F);

		// 获取后支配树
  		PostDominatorTree PDT;
  		PDT.recalculate(*F);
  
  		// 获取控制依赖图
		ControlDependenceGraph CDG(*F, PDT);

		set<BranchInst*> targetDependency;
		// 找到所有控制目标基本块的条件分支
  		for (BasicBlock *dBB : CDG.getControllers(tBB)) {
    		if (BranchInst *br = dyn_cast<BranchInst>(dBB->getTerminator())) {
      			if (br->isConditional()) {
        			//Value *cond = br->getCondition();
        			targetDependency.insert(br);
      			}
    		}
  		}

		//Value* ArrayRoot=NULL;
		vector<set<pair<string, string>>> funcSets;
		for(auto pBB:visit) {
			set<pair<string, string>> pathConstraints;
			int cmpintvalue = -1;
			unsigned icmpPred = 0;
			if(BranchInst* BI= dyn_cast<BranchInst>(pBB->getTerminator())) {
				if(BI->getNumSuccessors() != 2 || BI->isUnconditional()) continue;
				auto brbb1 = BI->getSuccessor(0);
				auto brbb2 = BI->getSuccessor(1);
				if (visit.count(brbb1) !=0 && visit.count(brbb2) !=0) {
					if(targetDependency.find(BI) == targetDependency.end()) {
						continue;
					}
				}

				if(F->hasName()) {
					OP << "find target branch in func " << F->getName().str() << ": " << *BI << "\n";
				}
				
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

				if(!isno && visit.count(brbb1) == 0 && visit.count(brbb2) != 0) {
					isno = true;
				}

				if(isno && visit.count(brbb1) != 0 && visit.count(brbb2) == 0) {
					isno = false;
				}

				Instruction* BICondI = dyn_cast<Instruction>(BI->getCondition());
				set<Instruction*> pendinsts;
				if(BICondI) {
					pendinsts.insert(BICondI);
				}
                if(BICondI && dyn_cast<CallInst>(BICondI)) {
					pendinsts.clear();
                    CallInst* BICondCall = dyn_cast<CallInst>(BICondI);
					TryMatchCallInIf(BICondCall, sigfsparamsenum, sigfsparamsflag, sigfsparamsint, sigfs2options, sigfs2options2onelayer, sm, pathConstraints, isno);
                    pendinsts = TryGetMountOptInIfCall(BICondCall);
					if(pendinsts.empty()) {
						continue;
					}
                }
				for(Instruction* pendinst : pendinsts) {
					BICondI = pendinst;
					if(!BICondI) continue;
					if(ICmpInst* ICmp= dyn_cast<ICmpInst>(BICondI)) {
						if((ICmp->getPredicate()==llvm::CmpInst::ICMP_NE) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_EQ) ||
						   (ICmp->getPredicate()==llvm::CmpInst::ICMP_UGT) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_UGE) ||
						   (ICmp->getPredicate()==llvm::CmpInst::ICMP_ULT) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_ULE) ||
						   (ICmp->getPredicate()==llvm::CmpInst::ICMP_SGT) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_SGE) ||
						   (ICmp->getPredicate()==llvm::CmpInst::ICMP_SLT) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_SLE)) {
							if((dyn_cast<Instruction>(ICmp->getOperand(0)) && dyn_cast<ConstantInt>(ICmp->getOperand(1))) || (dyn_cast<Instruction>(ICmp->getOperand(1)) && dyn_cast<ConstantInt>(ICmp->getOperand(0)))) {
								Instruction* ICmpi = dyn_cast<Instruction>(ICmp->getOperand(0));
								ConstantInt* ICmpc = dyn_cast<ConstantInt>(ICmp->getOperand(1));
								icmpPred = ICmp->getPredicate();
								if(!ICmpi) {
									ICmpi = dyn_cast<Instruction>(ICmp->getOperand(1));
									ICmpc = dyn_cast<ConstantInt>(ICmp->getOperand(0));
								}
								cmpintvalue = ICmpc->getZExtValue();
								set<Instruction*> pendinsts2;
                                pendinsts2.insert(ICmpi);
								if(ICmpi->getOpcode() == llvm::Instruction::Call) {
									pendinsts2.clear();
									CallInst* ifCall = dyn_cast<CallInst>(ICmpi);
									TryMatchCallInIf(ifCall, sigfsparamsenum, sigfsparamsflag, sigfsparamsint, sigfs2options, sigfs2options2onelayer, sm, pathConstraints, isno);
									pendinsts2 = TryGetMountOptInIfCall(ifCall);
									if(pendinsts2.empty()) continue;
								}
								for(Instruction* pendinst2 : pendinsts2) {
									ICmpi = pendinst2;
									bool MaybeBitField = false;
									int BitFieldOff = 0;
									if(ICmpi->getOpcode() == llvm::Instruction::ZExt) {
										OP << "find bit field zext " <<*ICmpi << "\n";
										ICmpi = dyn_cast<Instruction>(ICmpi->getOperand(0));
										MaybeBitField = true;
									}
									if(ICmpi->getOpcode() == llvm::Instruction::And && ((ICmp->getPredicate()==llvm::CmpInst::ICMP_NE) || (ICmp->getPredicate()==llvm::CmpInst::ICMP_EQ))) {
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
											OP << "find bit field lshr " <<*andi << "\n";
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
												std::set<std::pair<string, std::pair<uint32_t, string>>> currStAndConsts;
												if(isno) {
													currStAndConsts.insert(std::make_pair(icmptost, std::make_pair(andv, "clear")));
													currStAndConsts.insert(std::make_pair(icmptost, std::make_pair(andv, "enumclear")));
													if(MaybeBitField) {
														OP << "find bit field clear " <<icmptostbitfield << "\n";
														currStAndConsts.insert(std::make_pair(icmptostbitfield, std::make_pair(BitFieldOff, "bitfieldclear")));
													}
												} else {
													currStAndConsts.insert(std::make_pair(icmptost, std::make_pair(andv, "set")));
													currStAndConsts.insert(std::make_pair(icmptost, std::make_pair(andv, "enumset")));
													if(MaybeBitField) {
														OP << "find bit field set " <<icmptostbitfield << "\n";
														currStAndConsts.insert(std::make_pair(icmptostbitfield, std::make_pair(BitFieldOff, "bitfieldset")));
													}
												}
	
												if(sigfs2options.find(icmptost) != sigfs2options.end() || sigfs2options.find(icmptostbitfield) != sigfs2options.end()) {
													std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[icmptost];
													if(constandfe.empty()) {
														constandfe = sigfs2options[icmptostbitfield];
													}
													for(auto& constfeandconf : constandfe) {
														std::pair<uint32_t, string> constfe = constfeandconf.first;
														//修改：还没把assignint放过来，不过可以先等等
														if(isno) {
															if((constfe.first != andv && constfe.first != BitFieldOff) || (constfe.second != "clear" && constfe.second != "enumclear" && constfe.second != "bitfieldclear" && constfe.second != "assignint" && constfe.second != "assignenum")) continue;
														} else {
															if((constfe.first != andv && constfe.first != BitFieldOff) || (constfe.second != "set" && constfe.second != "enumset" && constfe.second != "bitfieldset" && constfe.second != "assignint" && constfe.second != "assignenum")) continue;
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
																pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
															}
														} else {
															// flag or enum or int
															int optnum = flagorenumopt.first;
															int optstatus = flagorenumopt.second;
															string flagoptstr = sigfsparamsflag[optnum];
															auto it_int = sigfsparamsint.find(optnum);
															if(!flagoptstr.empty()) {
																if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																pathConstraints.insert(std::make_pair(flagoptstr, " "));
															}
															else if(it_int != sigfsparamsint.end()) {
																string intname = it_int->second.first;
																string op = "";
																if(isno) op = "!="; else op = "=";
																pathConstraints.insert(std::make_pair(intname, op + std::to_string(andv)));
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
																			pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvaluetostr));
																		}
																	}
																}			
															}
														} // end int check else
													}
												} else {
													bool tryMkfsOpt = true;
													for(auto& currStAndConst : currStAndConsts) {
														if(sigfs2options2onelayer.find(currStAndConst) != sigfs2options2onelayer.end()) {
															auto fsopts2one = sigfs2options2onelayer[currStAndConst];
															for(auto& OptStConstconf : fsopts2one) {
																string optSt = OptStConstconf.first.first;
																uint32_t setOptConst = OptStConstconf.first.second.first;
																string setOptStr = OptStConstconf.first.second.second;
																std::pair<std::string, uint64_t> cmpopandv = OptStConstconf.second;
																if(setOptConst == 0xffffffff && setOptStr != "assignenum" && setOptStr != "assignint") continue;
																std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[optSt];
																for(auto& constfeandconf : constandfe) {
																	std::pair<uint32_t, string> constfe = constfeandconf.first;
																	if(constfe.first != setOptConst || constfe.second != setOptStr) continue;
																	tryMkfsOpt = false;
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
																			pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
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
																				pathConstraints.insert(std::make_pair(intname, op + std::to_string(cmpopandv.second)));
																			} else {
																				if(isno) op = "!="; else op = "=";
																				pathConstraints.insert(std::make_pair(intname, op + std::to_string(andv)));
																			}
																			continue;
																		}
																		string flagoptstr = sigfsparamsflag[optnum];
																		if(!flagoptstr.empty()) {
																			if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																			pathConstraints.insert(std::make_pair(flagoptstr, " "));
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
																								pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
																							}
																						}
																					} else {
																						for (auto& enumvs : enumsvalueandstr) {
																							if (enumvs.first == andv) {
																								if (isno) op = "!="; else op = "=";
																								pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
																							}
																						}
																					}
																					break;
																				}
																			}
																		}
																	}
																} // end int check else
															}
														}
													} // end sigfs2options2onelayer else
													// Pattern B-2: bitmask match against sm
													if (andv != 0xffffffff && tryMkfsOpt) {
														for (const auto &entry : sm) {
															if (entry.bitmask_hex.empty()) continue;
															if (entry.transform != "bitmask_check") continue;
															if ((andv & (uint32_t)entry.bitmask_value) == 0) continue;
															string prefix = "mkfs:";
															if (isno) prefix += "^";
															pathConstraints.insert({entry.confd_param, prefix});
														}
													}
												}
											}
										}
									} else if (ICmpi->getOpcode() == llvm::Instruction::Load && !MaybeBitField) {
										LoadInst* ldi = nullptr;
										GetElementPtrInst* gepi = nullptr;
										ldi = dyn_cast<LoadInst>(ICmpi);
										llvm::Value* ldpo = ldi->getPointerOperand();
										Instruction* ldpoi = dyn_cast<Instruction>(ldpo);
										if(!ldpoi) continue;
										if(ldpoi->getOpcode() == llvm::Instruction::BitCast) {
											gepi = dyn_cast<GetElementPtrInst>(ldpoi->getOperand(0));
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
											std::set<std::pair<string, std::pair<uint32_t, string>>> currStAndConsts;
											currStAndConsts.insert(std::make_pair(icmptost, std::make_pair(0xffffffff, "assignint")));
											currStAndConsts.insert(std::make_pair(icmptost, std::make_pair(0xffffffff, "assignenum")));
	
											// Pattern E: GEP+offset → mkfs constraint via field_to_params
											{
												string structName = gepiTy->getStructName().str();
												auto it_fe = field_to_params.find({structName, (unsigned)offsetinst});
												if (it_fe != field_to_params.end()) {
													for (const auto *entry : it_fe->second) {
														string prefix = "mkfs:";
														if (entry->transform == "bitmask_check") {
															if (isno) prefix += "^";
															pathConstraints.insert({entry->confd_param, prefix});
														} else if (cmpintvalue >= 0) {
															string op;
															if (icmpPred == llvm::CmpInst::ICMP_EQ) { op = "="; if (isno) op = "!="; }
															else if (icmpPred == llvm::CmpInst::ICMP_NE) { op = "!="; if (isno) op = "="; }
															else if (icmpPred == llvm::CmpInst::ICMP_UGT || icmpPred == llvm::CmpInst::ICMP_SGT) { op = ">"; if (isno) op = "<="; }
															else if (icmpPred == llvm::CmpInst::ICMP_UGE || icmpPred == llvm::CmpInst::ICMP_SGE) { op = ">="; if (isno) op = "<"; }
															else if (icmpPred == llvm::CmpInst::ICMP_ULT || icmpPred == llvm::CmpInst::ICMP_SLT) { op = "<"; if (isno) op = ">="; }
															else if (icmpPred == llvm::CmpInst::ICMP_ULE || icmpPred == llvm::CmpInst::ICMP_SLE) { op = "<="; if (isno) op = ">"; }
															pathConstraints.insert({entry->confd_param, prefix + op + std::to_string(cmpintvalue)});
														} else {
															pathConstraints.insert({entry->confd_param, prefix});
														}
													}
												}
											}
	
											if(sigfs2options.find(icmptost) != sigfs2options.end()) {
												std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>> constandfe = sigfs2options[icmptost];
												for(auto& constfeandconf : constandfe) {
													std::pair<uint32_t, string> constfe = constfeandconf.first;
													if(constfe.second != "assignint" && constfe.second != "assignenum") continue;
													
													std::pair<int, int> flagorenumopt = constfeandconf.second;
													int flagorenum = flagorenumopt.second;
													if((flagorenum == -1 || flagorenum == -5) && cmpintvalue >= 0) {
														string op = "";
														if(icmpPred == llvm::CmpInst::ICMP_EQ) { op = "="; if(isno) op = "!="; }
														else if(icmpPred == llvm::CmpInst::ICMP_NE) { op = "!="; if(isno) op = "="; }
														else if(icmpPred == llvm::CmpInst::ICMP_UGT || icmpPred == llvm::CmpInst::ICMP_SGT) { op = ">"; if(isno) op = "<="; }
														else if(icmpPred == llvm::CmpInst::ICMP_UGE || icmpPred == llvm::CmpInst::ICMP_SGE) { op = ">="; if(isno) op = "<"; }
														else if(icmpPred == llvm::CmpInst::ICMP_ULT || icmpPred == llvm::CmpInst::ICMP_SLT) { op = "<"; if(isno) op = ">="; }
														else if(icmpPred == llvm::CmpInst::ICMP_ULE || icmpPred == llvm::CmpInst::ICMP_SLE) { op = "<="; if(isno) op = ">"; }
														if (constfe.second == "assignint") {
															int optnum = flagorenumopt.first;
															// check int params first
															auto it_int = sigfsparamsint.find(optnum);
															if(it_int != sigfsparamsint.end()) {
																string intname = it_int->second.first;
																pathConstraints.insert(std::make_pair(intname, op + std::to_string(cmpintvalue)));
															}
														} else if (constfe.second == "assignenum") {
															int optnum = flagorenumopt.first;
															std::pair<int, std::string> optenum = std::make_pair(-1, "");
															for(auto& enumoptandconst : sigfsparamsenum) {
																if (optnum == enumoptandconst.first.first) {
																	optenum = enumoptandconst.first;
																	break;
																}
															}
															if (optenum.first != -1) {
																std::map<int, std::string> enumopts = sigfsparamsenum[optenum];
																if (enumopts.count(cmpintvalue) > 0) {
																	string enumoptstr = optenum.second;
																	pathConstraints.insert(std::make_pair(enumoptstr, op + enumopts[cmpintvalue]));
																}
															}
														}
													}
												}
											} else {
												for(auto& currStAndConst : currStAndConsts) {
													if(sigfs2options2onelayer.find(currStAndConst) != sigfs2options2onelayer.end()) {
														auto fsopts2one = sigfs2options2onelayer[currStAndConst];
														for(auto& OptStConstconf : fsopts2one) {
															string optSt = OptStConstconf.first.first;
															uint32_t setOptConst = OptStConstconf.first.second.first;
															string setOptStr = OptStConstconf.first.second.second;
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
																		pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
																	}
																} else {
																	string op = "";
																	if(icmpPred == llvm::CmpInst::ICMP_EQ) { op = "="; if(isno) op = "!="; }
																	else if(icmpPred == llvm::CmpInst::ICMP_NE) { op = "!="; if(isno) op = "="; }
																	else if(icmpPred == llvm::CmpInst::ICMP_UGT || icmpPred == llvm::CmpInst::ICMP_SGT) { op = ">"; if(isno) op = "<="; }
																	else if(icmpPred == llvm::CmpInst::ICMP_UGE || icmpPred == llvm::CmpInst::ICMP_SGE) { op = ">="; if(isno) op = "<"; }
																	else if(icmpPred == llvm::CmpInst::ICMP_ULT || icmpPred == llvm::CmpInst::ICMP_SLT) { op = "<"; if(isno) op = ">="; }
																	else if(icmpPred == llvm::CmpInst::ICMP_ULE || icmpPred == llvm::CmpInst::ICMP_SLE) { op = "<="; if(isno) op = ">"; }
																	// flag, int, or enum
																	int optnum = flagorenumopt.first;
																	int optstatus = flagorenumopt.second;
																	// check int params first
																	auto it_int = sigfsparamsint.find(optnum);
																	if(it_int != sigfsparamsint.end()) {
																		string intname = it_int->second.first;
																		pathConstraints.insert(std::make_pair(intname, op + std::to_string(cmpintvalue)));
																		continue;
																	}
																	string flagoptstr = sigfsparamsflag[optnum];
																	if(!flagoptstr.empty()) {
																		if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																		pathConstraints.insert(std::make_pair(flagoptstr, " "));
																	} else {
																		if(optstatus == -1) {
																			string op = "";
																			for(auto& enumopt2 : sigfsparamsenum) {
																				std::pair<int, string> enumoptnumandstr = enumopt2.first;
																				if(enumoptnumandstr.first != optnum) continue;
																				std::map<int, string> enumsvalueandstr = enumopt2.second;
																				for (auto& enumvs : enumsvalueandstr) {
																					if (enumvs.first == cmpintvalue) {
																						pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
																					}
																				}
																				break;
																			}
																		}
																	}
																}
															} // end int check else
														}
													}
												} // end sigfs2options2onelayer else
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
											std::pair<string, std::pair<uint32_t, string>> currStAndConst;
											if(isno) {
												if(MaybeBitField) {
													currStAndConst = std::make_pair(itrunctost, std::make_pair(BitFieldOff, "bitfieldclear"));
												} else {
													currStAndConst = std::make_pair(itrunctost, std::make_pair(flagv, "assignfalse"));
												}
											} else {
												if(MaybeBitField) {
													currStAndConst = std::make_pair(itrunctost, std::make_pair(BitFieldOff, "bitfieldset"));
												} else {
													currStAndConst = std::make_pair(itrunctost, std::make_pair(flagv, "assigntrue"));
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
															pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
														}
													} else {
														// flag or enum
														int optnum = flagorenumopt.first;
														int optstatus = flagorenumopt.second;
														string flagoptstr = sigfsparamsflag[optnum];
														if(!flagoptstr.empty()) {
															if(optstatus == -2) flagoptstr = "no" + flagoptstr;
															pathConstraints.insert(std::make_pair(flagoptstr, " "));
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
																			pathConstraints.insert(std::make_pair(enumoptnumandstr.second, "!=" + enumvaluetostr));
																		}
																		else {
																			pathConstraints.insert(std::make_pair(enumoptnumandstr.second, "=" + enumvaluetostr));
																		}
																	}
																}
															}
														}
													}
												}
                        					}
											else if(sigfs2options2onelayer.find(currStAndConst) != sigfs2options2onelayer.end()) {
												auto fsopts2one = sigfs2options2onelayer[currStAndConst];
												for(auto& OptStConstconf : fsopts2one) {
													string optSt = OptStConstconf.first.first;
													uint32_t setOptConst = OptStConstconf.first.second.first;
													string setOptStr = OptStConstconf.first.second.second;
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
																pathConstraints.insert(std::make_pair(enumoptstr, '=' + enumstr));
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
																	pathConstraints.insert(std::make_pair(intname, op + std::to_string(cmpopandv.second)));
																}
																continue;
															}
															string flagoptstr = sigfsparamsflag[optnum];
															if(!flagoptstr.empty()) {
																if(optstatus == -2) flagoptstr = "no" + flagoptstr;
																pathConstraints.insert(std::make_pair(flagoptstr, " "));
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
																					pathConstraints.insert(std::make_pair(enumoptnumandstr.second, op + enumvs.second));
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
					if (!pathConstraints.empty())
						funcSets.push_back(pathConstraints);
				}
			}
		}
		// per-function: collect func-level constraint sets
		if (!funcSets.empty())
			allFuncSets.push_back(funcSets);
	}
	// Compute cartesian product of per-function constraint sets
	if (!allFuncSets.empty()) {
		vector<set<pair<string, string>>> currentGroups;
		for (auto &s : allFuncSets[0])
			currentGroups.push_back(s);
		for (size_t fi = 1; fi < allFuncSets.size(); fi++) {
			vector<set<pair<string, string>>> expanded;
			for (auto &existing : currentGroups) {
				for (auto &newSet : allFuncSets[fi]) {
					set<pair<string, string>> merged = existing;
					merged.insert(newSet.begin(), newSet.end());
					if (std::find(expanded.begin(), expanded.end(), merged) == expanded.end())
						expanded.push_back(merged);
				}
			}
			if (!expanded.empty())
				currentGroups = expanded;
		}
		for (auto &g : currentGroups)
			fsMountConstraintGroups.push_back(g);
	}
}


ConstraintInfo constraintExtraction(CallTraceInfo &callTraceInfo) {
	ConstraintInfo constraintInfo;
	auto callTrace = callTraceInfo.callTrace;
	uint64_t constNum = 0;
	string importFunc;
	int lineNum;
	string constStrName;
	bool flag = findConstInSwitch(callTrace, importFunc, constNum, constStrName);
	if (flag) {
		constraintInfo.switchConstSet.insert(make_pair(constNum, constStrName));
	}

	findConstFromIf(callTrace,constraintInfo.ifNotConstSet);

	for (auto &trace: callTrace) {
		string funcName = trace.first->getName().str();
		for (auto constInfo: GlobalCtx.HandlerConstraint[funcName]) {
			constraintInfo.handlerConstSet.insert(constInfo);
		}

		if(constraintInfo.relateModule=="" && GlobalCtx.Func2ConstFromFopsMap.count(funcName)!=0){
			constraintInfo.relateModule=GlobalCtx.Func2ConstFromFopsMap[funcName];
		}
	}

	for(auto cst: constraintInfo.switchConstSet){
		string cstName=cst.second;
		if(cstName.find("NETLBL_NLTYPE_")!=-1){
			string newcstName=cstName+"_NAME";
			if(SpecialConstraintMap.count(newcstName)!=-1){
				if(SpecialConstraintMap[newcstName].first=="string")
					constraintInfo.relateModule=SpecialConstraintMap[newcstName].second;
				else{
					constraintInfo.switchConstSet.insert(make_pair(atoi(SpecialConstraintMap[newcstName].second.c_str()), constStrName));
				}
			}
		}
	}
	return constraintInfo;
}

void initializeBasicBlock2IdxMap(Function* F){
	if(GlobalCtx.BasicBlockIndexMap.count(F)!=0){
		return;
	}
	GlobalCtx.BasicBlockIndexMap[F]=map<BasicBlock*,string>();
	int idx = -1;
	for (auto it = F->begin(), end = F->end(); it != end; it++) {
		idx += 1;
		BasicBlock *it2BB = &*it;
		GlobalCtx.BasicBlockIndexMap[F][it2BB]=to_string(idx);
	}
}

set<string> filesystem_set{"sysfs", "rootfs", "ramfs", "tmpfs", "devtmpfs", "debugfs", "securityfs", "sockfs", "pipefs", "anon_inodefs", "devpts", "ext3", "ext2", "ext4", "hugetlbfs", "vfat", "ecryptfs", "fuseblk", "fuse", "rpc_pipefs", "nfs", "nfs4", "nfsd", "binfmt_misc", "autofs", "xfs", "jfs", "msdos", "ntfs3", "ntfs", "minix", "hfs", "hfsplus", "qnx4", "ufs", "btrfs", "configfs", "ncpfs", "qnx6", "exofs", "befs", "vxfs", "gfs2", "gfs2meta", "fusectl", "bfs", "nsfs", "efs", "cifs", "efivarfs", "affs", "tracefs", "bdev", "ocfs2", "ocfs2_dlmfs", "hpfs", "proc", "afs", "reiserfs", "jffs2", "romfs", "aio", "sysv", "v7", "udf", "ceph", "pstore", "adfs", "9p", "hostfs", "squashfs", "cramfs", "iso9660", "coda", "nilfs2", "logfs", "overlay", "f2fs", "omfs", "ubifs", "openpromfs", "bpf", "cgroup", "cgroup2", "cpuset", "mqueue", "aufs", "selinuxfs", "dax", "erofs", "virtiofs", "exfat", "binder", "zonefs", "pvfs2", "incremental-fs", "esdfs"};

vector<TargetSignature> collectSignature(BasicBlock* targetBlock, int index, vector<set<pair<string, string>>>& fsMountCons) {
	vector<TargetSignature> targetSigList;
	vector<CallTraceInfo> callTraceInfoList;
	getCallTrace(targetBlock, callTraceInfoList);
	std::sort(callTraceInfoList.begin(), callTraceInfoList.end(), [](CallTraceInfo a, CallTraceInfo b) {
		if (a.depth != b.depth) {
			return a.depth < b.depth;
		} else {
			return a.icallNum < b.icallNum;
		}
	});

	const int maxCallTrace = 2;
	int idxSyscall = 0;
	int idxHandler = 0;
	bool firstEntrySyscall = true;
	bool firstEntryHandler = true;
	CallTraceInfo lastCallTraceSyscall;
	CallTraceInfo lastCallTraceEntry;

	Function *targetFunc = targetBlock->getParent();
	string fullPath = targetFunc->getParent()->getSourceFileName();
	vector<string> splitRes;
	string filesystem = "";
	std::map<std::pair<int, std::string>, std::map<int, std::string>> sigfsparamsenum;
	std::map<int, string> sigfsparamsflag;
	std::map<int, std::pair<std::string, int>> sigfsparamsint;
	std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> sigfs2options;
	std::map<std::pair<std::string, std::pair<uint32_t, string>>, OneLayerPairSet> sigfs2options2onelayer;
	const vector<SuperblockMappingEntry> *sm = nullptr;
	map<pair<string, unsigned>, vector<const SuperblockMappingEntry*>> field_to_params;
	
	set<pair<string, string>> testfsmountif;

	splitString(fullPath, splitRes, "/");
	for (auto subItem: splitRes) {
		if (filesystem_set.count(subItem) != 0) {
			filesystem = subItem;
		}
	}
	if(filesystem != "") {
		sigfsparamsenum = GlobalCtx.fsparamsenum[filesystem];
		sigfsparamsflag = GlobalCtx.fsparamsflag[filesystem];
		sigfsparamsint = GlobalCtx.fsparamsint[filesystem];
		sigfs2options =  GlobalCtx.fs2options[filesystem];
		sigfs2options2onelayer = GlobalCtx.fs2options2onelayer[filesystem];
		sm = &GlobalCtx.superblock_mappings[filesystem];
		for (const auto &entry : *sm) {
			if (!entry.embedded_struct_type.empty() && entry.embedded_field_offset >= 0) {
				field_to_params[{entry.embedded_struct_type, (unsigned)entry.embedded_field_offset}].push_back(&entry);
			}
		}
	}

	for (auto callTraceInfo: callTraceInfoList) {
		auto callTrace = callTraceInfo.callTrace;
		bool isSyscallEntry = callTraceInfo.isSyscallEntry;
		if (isSyscallEntry) {
			if (firstEntrySyscall) {
				firstEntrySyscall = false;
				lastCallTraceSyscall = callTraceInfo;
			} else {
				if (lastCallTraceSyscall.depth != callTraceInfo.depth || lastCallTraceSyscall.icallNum != callTraceInfo.icallNum) {
					idxSyscall += 1;
					lastCallTraceSyscall = callTraceInfo;
				}
			}
		} else {
			if (firstEntryHandler) {
				firstEntryHandler = false;
				lastCallTraceEntry = callTraceInfo;
			} else {
				if (lastCallTraceEntry.depth != callTraceInfo.depth || lastCallTraceEntry.icallNum != callTraceInfo.icallNum) {
					idxHandler += 1;
					lastCallTraceEntry = callTraceInfo;
				}
			}
		}

		if (idxSyscall+idxHandler >= maxCallTrace) break;

		TargetSignature sig;
		if (isSyscallEntry) {
			sig.rank = idxSyscall;
		} else {
			sig.rank = idxHandler;
		}

		INFO("------------------------------------\n")
		INFO("index: " << index << "\n");
		string syscallName = getSyscallName(callTrace[0].first);
		if (syscallName != "") {
			sig.commonSyscall = syscallName;
		}

		int cnt = 0;

		for (auto tracePoint: callTrace) {
			if (cnt == 0) {
				sig.handler = tracePoint.first->getName().str();
			}
			Function *functionPoint = tracePoint.first;
			sig.functionList.push_back(functionPoint->getName().str());
			Instruction *instPoint = tracePoint.second;

			INFO(functionPoint->getName() << "\n");
			if (instPoint != nullptr) {
				INFO(*instPoint << "\n");
			} else {
				sig.blockSigList.push_back(vector<string>());
				continue;
			}

			BasicBlock *blockPoint = instPoint->getParent();
			vector<BasicBlock*> blockPointVec;
			collectAllPredBlock(blockPoint, blockPointVec);

			initializeBasicBlock2IdxMap(functionPoint);
			vector<string> blockNameList;
			for(auto block:blockPointVec){
				blockNameList.push_back(GlobalCtx.BasicBlockIndexMap[functionPoint][block]);
			}
			sig.blockSigList.push_back(blockNameList);
			cnt += 1;
		}
		ConstraintInfo constraintInfo = constraintExtraction(callTraceInfo);
		if(filesystem != "" && sigfsparamsflag.size() != 0 && sm) {
			findFsConstFromIf(fsMountCons, callTraceInfo.callTrace, sigfsparamsenum, sigfsparamsflag, sigfsparamsint, sigfs2options, sigfs2options2onelayer, field_to_params, *sm);
			//findFsConstFromSwitch(constraintInfo, callTraceInfo.callTrace, sigfsparamsenum, sigfsparamsflag, sigfs2options, sigfs2options2onelayer);
		}
		sig.constraintInfo = constraintInfo;
		targetSigList.push_back(sig);
		/*if(testfsmountif.size() == 0) {
			outs() << "dont find fs mount opts!\n";
		} else {
			outs() << "find fs mount opts: \n";
			for(auto& fsif: testfsmountif) {
				outs() << fsif.first << "=" << fsif.second << "\n";
			}
			testfsmountif.clear();
		}*/
	}
	// Deduplicate: drop identical constraint groups from different call traces
	std::sort(fsMountCons.begin(), fsMountCons.end());
	auto last = std::unique(fsMountCons.begin(), fsMountCons.end());
	fsMountCons.erase(last, fsMountCons.end());
	return targetSigList;
}

void loadFsMountFile() {
	string filename = FsparamsEnumFile;
	std::ifstream filefsparamsenum(filename);
    if (!filefsparamsenum.is_open()) {
        return;
    }

    std::string line;
    while (std::getline(filefsparamsenum, line)) {
        std::istringstream iss(line);
        std::string key1, val1, val2;
        int key2, key3;

        if (!(iss >> key1 >> key2 >> val1 >> key3 >> val2)) {
            continue;
        }

        auto key_pair = std::make_pair(key2, val1);
        
        GlobalCtx.fsparamsenum[key1][key_pair][key3] = val2;
    }

    filefsparamsenum.close();

	filename = FsparamsFlagFile;
	std::ifstream filefsparamsflag(filename);
    if (!filefsparamsflag.is_open()) {
        return;
    }

    //std::string line;
    while (std::getline(filefsparamsflag, line)) {
        std::istringstream iss(line);
        std::string key1, val1;
        int key2;

        if (!(iss >> key1 >> key2 >> val1)) {
            continue;
        }

        
        GlobalCtx.fsparamsflag[key1][key2] = val1;
    }

    filefsparamsflag.close();

	filename = Fs2OptionsFile;
	std::ifstream filefs2options(filename);
    if (!filefs2options.is_open()) {
        return;
    }

    //std::string line;
    while (std::getline(filefs2options, line)) {
        std::istringstream iss(line);
        std::string key1, key2, val2;
        uint32_t val1;
        int val3, val4;

        if (!(iss >> key1 >> key2 >> val1 >> val2 >> val3 >> val4)) {
            continue;
        }

        auto first_pair = std::make_pair(val1, val2);
		auto second_pair = std::make_pair(val3, val4);
        auto element = std::make_pair(first_pair, second_pair);
        
        GlobalCtx.fs2options[key1][key2].insert(element);
    }

    filefs2options.close();

	filename = Fs2Options2OnelayerFile;
	std::ifstream filefs2options2onelayer(filename);
    if (!filefs2options2onelayer.is_open()) {
        return;
    }

    //std::string line;
    while (std::getline(filefs2options2onelayer, line)) {
        std::istringstream iss(line);
        std::string key1, key2, key4, val1, val3, cmp_op;
        uint32_t key3, val2;
        uint64_t cmp_val;

        if (!(iss >> key1 >> key2 >> key3 >> key4 >> val1 >> val2 >> val3 >> cmp_op >> cmp_val)) {
            continue;
        }

        auto key_pair = std::make_pair(key2, std::make_pair(key3, key4));
        auto val_inner = std::make_pair(val1, std::make_pair(val2, val3));
        auto val_cmp = std::make_pair(cmp_op, cmp_val);
        auto val_pair = std::make_pair(val_inner, val_cmp);
        
        GlobalCtx.fs2options2onelayer[key1][key_pair].insert(val_pair);
    }

    filefs2options2onelayer.close();

	// Load int params
	filename = FsparamsIntFile;
	if (!filename.empty()) {
		std::ifstream filefsints(filename);
		if (filefsints.is_open()) {
			while (std::getline(filefsints, line)) {
				std::istringstream iss(line);
				std::string key1, val1;
				int key2, val2;

				if (!(iss >> key1 >> key2 >> val1 >> val2)) {
					continue;
				}

				GlobalCtx.fsparamsint[key1][key2] = std::make_pair(val1, val2);
			}
			filefsints.close();
		}
	}

	// Load superblock mappings from directory
	if (!SuperblockMappingDir.empty()) {
		std::error_code EC;
		for (llvm::sys::fs::directory_iterator
		     DirIt(SuperblockMappingDir, EC), DirEnd;
		     DirIt != DirEnd; DirIt.increment(EC)) {
			if (EC) break;
			std::string path = DirIt->path();
			// Match superblock_mapping_*.json
			std::string fname = llvm::sys::path::filename(path);
			if (fname.find("superblock_mapping_") != 0 ||
			    fname.find(".json") == std::string::npos) {
				continue;
			}
			// Extract fsname: superblock_mapping_ext4.json → ext4
			std::string prefix = "superblock_mapping_";
			std::string suffix = ".json";
			std::string fsname = fname.substr(prefix.size(),
				fname.size() - prefix.size() - suffix.size());

			auto buf = llvm::MemoryBuffer::getFile(path);
			if (!buf) continue;
			auto jsonVal = llvm::json::parse(buf.get()->getBuffer());
			if (!jsonVal) continue;
			auto *obj = jsonVal->getAsObject();
			if (!obj) continue;

			auto *arr = obj->getArray("confd_to_superblock");
			if (!arr) continue;

			std::vector<SuperblockMappingEntry> entries;
			for (auto &elem : *arr) {
				auto *e = elem.getAsObject();
				if (!e) continue;
				SuperblockMappingEntry entry;
				if (auto *v = e->getString("confd_param"))
					entry.confd_param = v->str();
				if (auto *v = e->getString("confd_variable"))
					entry.confd_variable = v->str();
				if (auto *v = e->getString("disk_field"))
					entry.disk_field = v->str();
				if (auto *v = e->getString("bitmask_hex"))
					entry.bitmask_hex = v->str();
				if (auto *v = e->getInteger("bitmask_value"))
					entry.bitmask_value = *v;
				if (auto *v = e->getString("kernel_func"))
					entry.kernel_func = v->str();
				if (auto *v = e->getString("kernel_mem_field"))
					entry.kernel_mem_field = v->str();
				if (auto *v = e->getString("transform"))
					entry.transform = v->str();
				if (auto *v = e->getString("formula"))
					entry.formula = v->str();
				if (auto *v = e->getString("embedded_struct_type"))
					entry.embedded_struct_type = v->str();
				if (auto *v = e->getInteger("embedded_field_offset"))
					entry.embedded_field_offset = *v;
				else
					entry.embedded_field_offset = -1;
				entries.push_back(entry);
			}
			GlobalCtx.superblock_mappings[fsname] = entries;
		}
	}
}

void loadSyscallFile() {
	string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
	string line;
	ifstream syscallFile(exedir + "/configs/syscall.txt");
	if (syscallFile.is_open()) {
		while (!syscallFile.eof()) {
			getline(syscallFile, line);
			strip(line);
			if (line.empty()) continue;
			GlobalCtx.syscallSet.insert(line);
		}
		syscallFile.close();
	}
	string fileName = KernelInterfaceFile;
	INFO("parsing file " << fileName << '\n');
	ifstream fileStream(fileName);
	string content((istreambuf_iterator<char>(fileStream)),
									(istreambuf_iterator<char>()));
	auto E = json::parse(content);	
	if(!E){
		ERR("Error reading json: "+fileName);
		exit(1);
	}
	json::Path::Root R("");
	json::fromJSON(E.get(), GlobalCtx.kernelSig2syscallVariant, R);

	ifstream fpCallerFile(exedir + "/configs/fp-cg-edge.txt");
	if (fpCallerFile.is_open()) {
		while (!fpCallerFile.eof()) {
			getline(fpCallerFile, line);
			strip(line);
			if (line.empty()) continue;
			vector<string> splitRes;
			splitString(line, splitRes, "<-");
			strip(splitRes[0]);
			strip(splitRes[1]);
			string to = splitRes[0];
			string from =  splitRes[1];
			if (GlobalCtx.FunctionNameMap.count(to) == 0 || GlobalCtx.FunctionNameMap.count(from) == 0) {
				continue;
			}
			Function* toF = GlobalCtx.FunctionNameMap[to];
			Function *fromF = GlobalCtx.FunctionNameMap[from];
			GlobalCtx.FPCallerMap[toF].insert(fromF);
		}
	} else {
		outs() << exedir << "dont contain fp-cg-edge file\n";
	}


	ifstream missingCallerFile(exedir + "/configs/miss-cg-edge.txt");
	if (missingCallerFile.is_open()) {
		while (!missingCallerFile.eof()) {
			getline(missingCallerFile, line);
			strip(line);
			if (line.empty()) continue;
			vector<string> splitRes;
			splitString(line, splitRes, "<-");
			strip(splitRes[0]);
			strip(splitRes[1]);
			string to = splitRes[0];
			string from =  splitRes[1];
			if (GlobalCtx.FunctionNameMap.count(to) == 0 || GlobalCtx.FunctionNameMap.count(from) == 0) {
				continue;
			}
			Function* toF = GlobalCtx.FunctionNameMap[to];
			Function *fromF = GlobalCtx.FunctionNameMap[from];
			DEBUG("missing cg: " << toF->getName() << " " << fromF->getName() << "\n");
			GlobalCtx.MissingCallerMap[toF].insert(fromF);
		}
	}

	ifstream registerFunctionFile(exedir + "/configs/register-funcs.txt");
	if (registerFunctionFile.is_open()) {
		while (!registerFunctionFile.eof()) {
			getline(registerFunctionFile, line);
			strip(line);
			vector<string> splitRes;
			splitString(line, splitRes, " ");
			string registerF = splitRes[0];
			int constPos = stoi(splitRes[1]);
			int functionPointerPos = stoi(splitRes[2]);
			GlobalCtx.RegisterFunctionMap[registerF].insert(make_pair(constPos, functionPointerPos));
			DEBUG("register: " << registerF << " " << constPos << " " << constPos << "\n");
		}
	}
}

map<string, BasicBlock*> NewParseDataset(){

	map<int, string> index2functionName;
	ifstream multiPositionPointsFile(MultiPositionPoints);
	if (multiPositionPointsFile.is_open()) {
		while (!multiPositionPointsFile.eof()) {
			string line;
			getline(multiPositionPointsFile, line);
			strip(line);
			if (line == "")
				break;
			DEBUG("multi-point" << MultiPositionPoints << "\n");
			DEBUG("line: " << line << "\n");
			vector<string> splitRes;
			splitString(line, splitRes, " ");
			strip(splitRes[0]);
			strip(splitRes[1]);
			int index = stoi(splitRes[0]);
			string functionName = splitRes[1];
			index2functionName[index] = functionName;
		}
	}

	map<string, BasicBlock*> Dataset;
	map<string, set<string>> DuplicateCases;
	DEBUG("Starting parsing dataset...\n")
	for(auto p: GlobalCtx.Modules){
		Module* M=p.first;
		for (auto mi = M->begin(), ei = M->end(); mi != ei; mi++) {
			Function *F = &*mi;
			for(auto &inst: instructions(F)){
				if(CallInst* CI= dyn_cast<CallInst>(&inst)){
					if(getCalledFuncName(CI)=="kcov_mark_block"){
						if(ConstantInt *CCI = dyn_cast<ConstantInt>(CI->getOperand(0))){
							int caseIdx=CCI->getZExtValue();
							INFO("index: " << caseIdx << " | currentfunction: " << CI->getFunction()->getName() << "\n");
							if (index2functionName.count(caseIdx)!=0){
								auto DesignatedTargetFunction=index2functionName[caseIdx];
								INFO("multipoints " << caseIdx << " designate tf:" << DesignatedTargetFunction << "\n");
								DEBUG("currentfunction: " << CI->getFunction()->getName() << "\n");
								if (DesignatedTargetFunction!=CI->getFunction()->getName()){
										continue;
								}
							}
							else if(Dataset.count(to_string(caseIdx))!=0 && Dataset[to_string(caseIdx)]->getParent()!=F){
								INFO("===\n");
								INFO("case " << caseIdx << ": More than one point!!!\n");
								INFO(Dataset[to_string(caseIdx)]->getParent()->getName() << " --- " << F->getName() << "\n");
								INFO("===\n");
								if (DuplicateCases.find(to_string(caseIdx))==DuplicateCases.end()){
									DuplicateCases[to_string(caseIdx)]=set<string>();
									DuplicateCases[to_string(caseIdx)].insert(Dataset[to_string(caseIdx)]->getParent()->getName().str());
								}
								DuplicateCases[to_string(caseIdx)].insert(F->getName().str());
							}
							if (TargetIndex == -1 || caseIdx == TargetIndex)
								Dataset[to_string(caseIdx)]=CI->getParent();
						}
					}
				}
			}
		}
	}
	std::error_code OutErrorInfo;
	if(DuplicateCases.size()>0){
		raw_fd_ostream DuplicatePoints(StringRef("./duplicate_points.txt"),OutErrorInfo, sys::fs::CD_CreateAlways);
		for(auto p: DuplicateCases){
			string xidx=p.first;
			DuplicatePoints << "xidx: " << p.first << "\n";
			DuplicatePoints << "duplicate point numbers: " << p.second.size() << "\n";
			for (auto r: DuplicateCases[xidx]){
				DuplicatePoints << "function name: " << r << "\n";
			}
			DuplicatePoints << "*********************\n";
		}
		exit(1);
	}
	return Dataset;
}


int main(int argc, char **argv) {
	clock_t startTime, endTime;
	startTime = clock();

	// Print a stack trace if we signal out.
	sys::PrintStackTraceOnErrorSignal(argv[0]);
	PrettyStackTraceProgram X(argc, argv);

	clock_t begin = clock();
	llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

	cl::ParseCommandLineOptions(argc, argv, "Syzdirect: kernel global analysis\n");
	SMDiagnostic Err;

	// full file path -> Module class
	map<string, Module*> ModuleMap;

	vector<string> InputFilenames;

	loadFsMountFile();

	for (const auto& p : filesystem::recursive_directory_iterator(std::string(kernelBCDir))) {
			if (!filesystem::is_directory(p)) {
					filesystem::path path = p.path();
					if (boost::algorithm::ends_with(path.string(), ".bc") && !boost::algorithm::ends_with(path.string(), "built-in.bc")) {
						InputFilenames.push_back(path.string());
					}
					// cout << (path.u8string()) << endl;
			}
	}

	// Loading modules
	OP << "Total " << InputFilenames.size() << " file(s)\n";

	for (unsigned i = 0; i < InputFilenames.size(); ++i) {

		LLVMContext *LLVMCtx = new LLVMContext();
		unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

		if (M == NULL) {
				Err.print("Analyzer.cc",OP);
				OP << "\n";
			OP << argv[0] << ": error loading file '"
				<< InputFilenames[i] << "'\n";
			continue;
		}

		Module *Module = M.release();
		StringRef MName = StringRef(strdup(InputFilenames[i].data()));
		GlobalCtx.Modules.push_back(make_pair(Module, MName));
		GlobalCtx.ModuleMaps[Module] = InputFilenames[i];

		string location = InputFilenames[i];
		vector<string> splitRes;
		splitString(location, splitRes, ".");
		location = splitRes[0];
		for (auto it = Module->begin(); it != Module->end(); ++it) {
			Function *F = &*it;
			if (!F->hasName())
				continue;
			string functionName = static_cast<string>(F->getName());
			if (functionName == "") 
				continue;
			auto tmpPair = make_pair(Module->getSourceFileName(), functionName);
			GlobalCtx.FunctionMap[tmpPair] = F;
			if (!F->isDeclaration()) {
				GlobalCtx.FunctionNameMap[functionName] = F;
			}
		}
		ModuleMap[Module->getSourceFileName()] = Module;
	}


	// Main workflow
	// Initilaize global type map
	TypeInitializerPass TIPass(&GlobalCtx);
	TIPass.run(GlobalCtx.Modules);
	TIPass.BuildTypeStructMap();

	// Build global callgraph.
	CallGraphPass CGPass(&GlobalCtx);
	CGPass.run(GlobalCtx.Modules);

	std::error_code OutErrorInfo;

	loadSyscallFile();
	raw_fd_ostream shrinkOutput(StringRef("./syscall_shrink.txt"), OutErrorInfo, sys::fs::CD_CreateAlways);


	ConstraintPass CtPass(&GlobalCtx);
	CtPass.run(GlobalCtx.Modules);

	raw_fd_ostream targetFunctionInfoFile(StringRef("./target_functions_info.txt"), OutErrorInfo, sys::fs::CD_CreateAlways);


	// for debug
	// raw_fd_ostream calleeFile(StringRef("./callee.txt"), OutErrorInfo, sys::fs::CD_CreateAlways);
	// raw_fd_ostream callerFile(StringRef("./caller.txt"), OutErrorInfo, sys::fs::CD_CreateAlways);

	// calleeFile << "===callees info===" << "\n";
	// for (auto item: GlobalCtx.Callees) {
	// 	CallInst *callInst = item.first;
	// 	Function *FuncFrom = callInst->getFunction();
	// 	for (auto FuncTo: item.second) {
	// 		calleeFile << FuncFrom->getName() << " -> " << FuncTo->getName() << "\n";
	// 	}
	// }
	// callerFile << "===callers info===" << "\n";
	// for (auto item: GlobalCtx.Callers) {
	// 	Function *FuncFrom = item.first;
	// 	for (auto callInst: item.second) {
	// 		callerFile << FuncFrom->getName() << " <- " << callInst->getFunction()->getName() << "\n";
	// 	}
	// }


	raw_fd_ostream OutputJ(StringRef("./CompactOutput.json"), OutErrorInfo, sys::fs::CD_CreateAlways);
 	json::OStream J(OutputJ,4);

 	struct OutputFrame{
		string caseIdx;
		struct tcallinfoFrame{
			string tcall;
			int rank;
			struct constraintFrame{
					struct fuconstraintFrame{
							string name;
							uint64_t value;
							fuconstraintFrame(string _name,uint64_t _value):name(_name),value(_value){}
					};
					vector<struct fuconstraintFrame> flag_union_constraints;
					string string_constraint;
			}constraint;
		};
		map<string,struct tcallinfoFrame> tcall_info_map;
	};

 	vector<struct OutputFrame> outputFrames;
	map<string, BasicBlock*> Dataset = NewParseDataset();

	for (auto item: Dataset) {
		string caseIdx = item.first;
		struct OutputFrame currentOF;
		currentOF.caseIdx = item.first;

		BasicBlock *targetBB = item.second;
		Function *targetFunc = targetBB->getParent();

		INFO("cid: " << caseIdx << "|" << targetFunc->getName() << "\n");
		if (targetFunc->getName() == "") 
			continue;

		targetFunctionInfoFile << caseIdx << " " << targetFunc->getName() << " " << targetFunc->getParent()->getSourceFileName() << "\n";

		map<string, int> targetSyscallRank;
		map<string, ConstraintInfo> targetSyscallConstraint;
		vector<set<pair<string, string>>> fsMountConstraint;
		vector<TargetSignature> targetSignatures = collectSignature(targetBB, stoi(caseIdx), fsMountConstraint);
		int minCalltraceLen=-1;
		for (const auto& sig: targetSignatures) {
			ConstraintInfo constraintInfo = sig.constraintInfo;
			if (minCalltraceLen==-1)
				minCalltraceLen=sig.functionList.size();
			else if (minCalltraceLen>sig.functionList.size())
				minCalltraceLen=sig.functionList.size();

			DEBUG("Calltrace length: " << sig.functionList.size() << " while min calltrace length is " << minCalltraceLen << "\n");
			bool hasConstraintInfo = false;
			if (constraintInfo.switchConstSet.size() > 0 ||
					constraintInfo.handlerConstSet.size() > 0 ||
					constraintInfo.ifNotConstSet.size()>0) {
				hasConstraintInfo = true;
			}

			string commonSyscall = sig.commonSyscall;
			int rank = sig.rank;
			if (commonSyscall != "") {
				if (targetSyscallRank.count(commonSyscall) == 0 || targetSyscallRank[commonSyscall] > rank) {
					targetSyscallRank[commonSyscall] = rank;
					if (hasConstraintInfo) {
						targetSyscallConstraint[commonSyscall] = constraintInfo;
					} else {
						targetSyscallConstraint.erase(commonSyscall);
					}
				}
			}
			string handler = sig.handler;
			
			// from bottom to top
			for (int cmdEntryFuncIdx = sig.functionList.size()-1; cmdEntryFuncIdx>=0; cmdEntryFuncIdx--) {
				string cmdEntryFunc = sig.functionList[cmdEntryFuncIdx];
				int exactMatchBlock = 0, exactMatchBlockNumMax=2;

				DEBUG("Current cmdEntryFunc: " << cmdEntryFunc << " in interface json: " << GlobalCtx.kernelSig2syscallVariant.count(cmdEntryFunc) << "\n");

				/// accurate match according to block idx
				for (auto &blockIdxStr: sig.blockSigList[cmdEntryFuncIdx]) {

					if (GlobalCtx.kernelSig2syscallVariant.count(cmdEntryFunc) != 0 && GlobalCtx.kernelSig2syscallVariant[cmdEntryFunc].count(blockIdxStr) != 0) {

						for (auto &syscall: GlobalCtx.kernelSig2syscallVariant[cmdEntryFunc][blockIdxStr]) {
							if (targetSyscallRank.count(syscall) == 0 || targetSyscallRank[syscall] > rank) {
								targetSyscallRank[syscall] = rank;
								if (hasConstraintInfo) {
									targetSyscallConstraint[syscall] = constraintInfo;
								} else {
									targetSyscallConstraint.erase(syscall);
								}
							}
							exactMatchBlock++;
							DEBUG("exact match block: " << "blockidx(" << blockIdxStr << ")" << "|" << syscall << "\n");
							if(exactMatchBlock>=exactMatchBlockNumMax){
								break;
							}
						}
						if(exactMatchBlock>=exactMatchBlockNumMax){
							break;
						}
					}
				}

				/// match with all block idx when fail
				bool findVariant = false;

				if (sig.functionList.size()-minCalltraceLen<2){
					if (!exactMatchBlock && GlobalCtx.kernelSig2syscallVariant.count(cmdEntryFunc) != 0) {
						for (auto &blockSigs: GlobalCtx.kernelSig2syscallVariant[cmdEntryFunc]) {
							if (blockSigs.second.size() > 10 && targetFunc->getName() != "netlink_sendmsg" && cmdEntryFunc != "nfnetlink_rcv_msg") {
								INFO("[-] too much syscall variant for handler: " << cmdEntryFunc << " : " << blockSigs.first << "\n");
								continue;
							}
							int syscallCount = 0;
							for (auto &syscall: blockSigs.second) {
								if (targetFunc->getName() == "netlink_sendmsg" && syscallCount > 5) break;
								if (targetSyscallRank.count(syscall) == 0 || targetSyscallRank[syscall] > rank || (hasConstraintInfo && targetSyscallConstraint.count(syscall)==0)) {
									targetSyscallRank[syscall] = rank;
									INFO("Not exact match of " << cmdEntryFunc << " : " << syscall << "\n");
									if (hasConstraintInfo) {
										targetSyscallConstraint[syscall] = constraintInfo;
									} else {
										targetSyscallConstraint.erase(syscall);
									}
								}
								findVariant = true;
								syscallCount += 1;
							}
						}
					}
				}
				if (exactMatchBlock || findVariant) {
					break;
				}
			}
		}

		map<string, vector<pair<string, int>>> syscall2Variant;
		for (auto syscallItem: targetSyscallRank) {
			string syscallVariant = syscallItem.first;
			int rank = syscallItem.second;
			if (syscallVariant.find('$') != string::npos) {
				vector<string> splitRes;
				splitString(syscallVariant, splitRes, "$");
				string syscall = splitRes[0];
				string variant = splitRes[1];
				syscall2Variant[syscall].push_back(make_pair(variant, rank));
			} else {
				syscall2Variant[syscallVariant].push_back(make_pair("", rank));
			}
		}
		set<pair<string, int>> finaltargetSyscallSet;

		for (auto syscallItem: syscall2Variant) {
			string syscall = syscallItem.first;
			vector<pair<string, int>> variantList = syscallItem.second;
			for (auto variantItem: variantList) {
				string variant = variantItem.first;
				int rank = variantItem.second;
				if (variant == "") {
					if (variantList.size() > 1)
						continue;
					else
						finaltargetSyscallSet.insert(make_pair(syscall, rank));
				} else {
					finaltargetSyscallSet.insert(make_pair(syscall + "$" + variant, rank));
				}
			}
		}
		
		for (auto syscall: finaltargetSyscallSet) {
			struct OutputFrame::tcallinfoFrame currentTIF;
			currentTIF.tcall=syscall.first;
			currentTIF.rank=syscall.second;
			currentOF.tcall_info_map[currentTIF.tcall]=currentTIF;
			
			string fullPath = targetFunc->getParent()->getSourceFileName();
			vector<string> splitRes;
			splitString(fullPath, splitRes, "/");
			for (auto subItem: splitRes) {
				if (filesystem_set.count(subItem) != 0) {
					string filesystem = subItem;
					ConstraintInfo constraintInfo;
				constraintInfo.relateModule = filesystem;
				
				// Write mount option constraints to per-case clean file (per-path groups)
				if (!fsMountConstraint.empty()) {
					// Split mount vs mkfs constraints by "mkfs:" prefix in c.second
					vector<set<pair<string, string>>> mountGroups, mkfsGroups;
					for (auto &pathSet : fsMountConstraint) {
						set<pair<string, string>> mountSet, mkfsSet;
						for (auto &c : pathSet) {
							if (c.second.find("mkfs:") == 0) {
								mkfsSet.insert({c.first, c.second.substr(5)});
							} else {
								mountSet.insert(c);
							}
						}
						if (!mountSet.empty()) mountGroups.push_back(mountSet);
						if (!mkfsSet.empty()) mkfsGroups.push_back(mkfsSet);
					}
					// Write mount constraints
					{
						std::string outFile = "mount_opts_" + caseIdx + ".txt";
						std::ofstream ofs(outFile);
						ofs << filesystem << "\n";
						for (auto &pathSet : mountGroups) {
							ofs << "---\n";
							if (pathSet.empty()) continue;
							for (auto &c : pathSet) {
								if (c.second == " ") ofs << c.first << "\n";
								else ofs << c.first << c.second << "\n";
							}
						}
					}
					// Write mkfs constraints
					{
						std::string outFile = "mkfs_opts_" + caseIdx + ".txt";
						std::ofstream ofs(outFile);
						ofs << filesystem << "\n";
						for (auto &pathSet : mkfsGroups) {
							ofs << "---\n";
							if (pathSet.empty()) continue;
							for (auto &c : pathSet) {
								if (c.second.empty()) ofs << c.first << "\n";
								else if (c.second == "^") ofs << "no" << c.first << "\n";
								else ofs << c.first << c.second << "\n";
							}
						}
					}
				}
					targetSyscallConstraint["mount"] = constraintInfo;
					break;
				}
			}
		}

		if (targetSyscallConstraint.size() > 0) {

			for (auto citem: targetSyscallConstraint) {
				string syscall = citem.first;
				ConstraintInfo constraintInfo = citem.second;


				if(currentOF.tcall_info_map.count(syscall)==0){
					DEBUG("constraint for unknown syscall!\n");
					currentOF.tcall_info_map[syscall]=OutputFrame::tcallinfoFrame();
					currentOF.tcall_info_map[syscall].tcall=syscall;
				}
				for (auto c: constraintInfo.switchConstSet) {
					DEBUG("switchConstSet: " << syscall << "\t\t" << c.second << " " << c.first << "\n");
					currentOF.tcall_info_map[syscall].constraint.flag_union_constraints.push_back(OutputFrame::tcallinfoFrame::constraintFrame::fuconstraintFrame(c.second,c.first));
				}
				for (auto c: constraintInfo.handlerConstSet) {
					DEBUG("handlerConstSet:" << syscall << "\t\t" << c.second << " " << c.first << "\n");
					currentOF.tcall_info_map[syscall].constraint.flag_union_constraints.push_back(OutputFrame::tcallinfoFrame::constraintFrame::fuconstraintFrame(c.second,c.first));
				}
				for (auto c: constraintInfo.ifNotConstSet) {
					DEBUG("ifNotConstSet:" << syscall << "\t\t" << c.second << " " << c.first << "\n");
					currentOF.tcall_info_map[syscall].constraint.flag_union_constraints.push_back(OutputFrame::tcallinfoFrame::constraintFrame::fuconstraintFrame(c.second,c.first));
				}
				shrinkOutput << "\t\t" << constraintInfo.relateModule << "\n";
				currentOF.tcall_info_map[syscall].constraint.string_constraint=constraintInfo.relateModule;
			}
		}
	
		outputFrames.push_back(currentOF);

		INFO("[+] index: " << caseIdx << " distance cal...\n"); 
		set<BasicBlock*> targetBBSet;
		targetBBSet.insert(targetBB);
    	DistanceCal *distanceCal = new DistanceCal(targetBBSet);
    	string outputDir = "distance_xidx" + caseIdx + "/";
    	distanceCal->outputBlocksDistance(outputDir, kernelBCDir);
	}


	J.array([&]{
		for(auto OF:outputFrames){
			J.object([&] {
				J.attribute("case index", OF.caseIdx);

					J.attributeArray("target syscall infos",[&] {
						for (auto p: OF.tcall_info_map) {
							J.object([&] {
									OutputFrame::tcallinfoFrame &TIF = p.second;
									J.attribute("target syscall", TIF.tcall);
									J.attribute("rank", TIF.rank);

									J.attributeObject("constraints", [&] {
										if(TIF.constraint.flag_union_constraints.size()!=0) {
											J.attributeArray("int", [&] {
													for (auto c: TIF.constraint.flag_union_constraints) {
														J.object([&] {
																J.attribute("name", c.name);
																string res = "";
																raw_string_ostream ss(res);
																ss << c.value;
																J.attribute("value", ss.str());
														});
													}
											});
										}
										if(TIF.constraint.string_constraint!="")
											J.attribute("string", TIF.constraint.string_constraint);
									});
							});
						}
					});
				});
			}
		});

	endTime = clock();
	double time = (double)(endTime - startTime) / CLOCKS_PER_SEC;
	outs() << "[+] time: " << time << "\n";
}
