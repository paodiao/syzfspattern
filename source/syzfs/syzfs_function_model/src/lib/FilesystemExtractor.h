#ifndef FILESYSTEM_EXTRACTOR_H
#define FILESYSTEM_EXTRACTOR_H

#include "Analyzer.h"

class FilesystemInfoItem : public InfoItem {
	public:
		Value* filesystemTypeStruct;
		vector<GlobalVariable*> fileOperations;
		vector<pair<string, Function*>> SyscallHandler;
		virtual string generateDeviceSignature(Function*);
};

class SpecialFSItem : public FilesystemInfoItem
{
	public:
		string SubsystemName;
		SpecialFSItem();
		map<Function*,string> Func2Dev;
		SpecialFSItem(FilesystemInfoItem*);
		void ExtendFunc2DevMap(Function*);
		virtual string generateDeviceSignature(Function*);
};


class FilesystemExtractorPass : public IterativeModulePass {

	private:
		
		// functions
		void ProcessRegisterFilesystem(CallInst* callInst, set<GlobalVariable*>& fsctxoper);
		GlobalVariable* getGlobalVaraible(StringRef);
		Function* getFunctionFromModules(StringRef funcName);
		vector<Module*> getRelatedModule(Module* M);
		void HandleFsTypeStruct(GlobalVariable* globalVar, FilesystemInfoItem* filesystemInfoItem, set<GlobalVariable*>& fsctxoper);
		set<Function*> findGetTreeFromInitFsCtx(Function* initFsCtx, set<GlobalVariable*>& fsctxoper);
		vector<pair<string, Function*>> getHandlerFromFileOperations(GlobalVariable* globalVar, string fsname);
		vector<pair<string, Function*>> getHandlerFromASOperations(GlobalVariable* globalVar, string fsname);
		void getFileOperationsFromFillSuper(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, unsigned depth);
		void getFileOperationsFromEntry(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, unsigned depth);
		set<string> getFsParamsNames(Function* parseF);
		vector<GlobalVariable*> getFsParams(Module* M, set<string> paramsname);
		std::map<int, std::pair<std::string, int>> getFlagsinParams(GlobalVariable* fsparams, std::map<int, std::pair<std::string, int>>& intParams);
		std::map<std::pair<int, std::string>, std::map<int, std::string>> getEnumsinParams(GlobalVariable* fsparams);
		std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> collectParamsParse(Function* parseF, std::map<std::pair<int, std::string>, std::map<int, std::string>> enumParams, std::map<int, std::pair<std::string, int>> flagParams, std::map<int, std::pair<std::string, int>>& intParams, std::set<string>& relatedSt);
		OneLayerPairSet getStFromTrunc(TruncInst* trunci, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& ParamsParse, bool isnobranch);
		std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> collectOneLayerParamsProp(llvm::Function* currentF, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> ParamsParse);
		void CollectBitFieldSet(StoreInst* si, int cmd_value, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& res, set<string>& relatedSt, string BitFieldType);
		vector<pair<string, Function*>> getHandlerFromINodeOperations(GlobalVariable* globalVar, string fsname);
		void findAllRelatedSt(GetElementPtrInst* flaggep, set<string>& relatedSt);

		void getOldParseMountOptionsFromFillSuper(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, CallInst* UpperCall, unsigned depth);
		void getOldParseMountOptionsFromEntry(Function* F, FilesystemInfoItem* filesystemInfoItem, set<Function*>& visited, CallInst* UpperCall, unsigned depth);
		set<string> getOldFsParamsNames(Function* parseF);
		vector<GlobalVariable*> getFsOldParams(Module* M, set<string> paramsname);
		std::map<int, std::string> getPotentialFlagsinOldParams(GlobalVariable* fsparams, std::map<int, std::pair<std::string, int>>& intParams, std::map<int, std::string>& enumParams);
		std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int,int>>>> collectOldParamsParse(Function* parseF, CallInst* CallToParseF, std::map<int, std::string> flagParams, std::map<int, std::pair<std::string, int>>& intParams, std::map<int, std::string> enumParams, std::set<string>& relatedSt, std::map<int, std::map<int, std::string>>& enumCollect);
		std::map<std::string, std::set<string>> collectFunctionTableAlloc(Function* InodeInitF, std::map<std::pair<int, std::string>, std::map<int, std::string>> &sigfsparamsenum, std::map<int, string> &sigfsparamsflag, std::map<int, std::pair<std::string, int>> &sigfsparamsint, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>> &sigfs2options, std::map<std::pair<std::string, std::pair<uint32_t, std::string>>, OneLayerPairSet> &sigfs2options2onelayer);
		set<string> BranchCondIsFileType(string srcFileName, BranchInst *BI);
		bool SwitchCondIsFileType(string srcFileName, SwitchInst *SWI);
		OneLayerPairSet getStFromIcmp(ICmpInst* icmp, std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int, int>>>>& ParamsParse);
		set<Instruction*> TryGetMountOptInIfCall(CallInst* ifCall);
		std::map<std::string, std::set<std::pair<std::pair<uint32_t, string>, std::pair<int,int>>>> collectExt4ParamParse(Module* Ext4Super, std::set<string>& relatedSt);
		
		bool MountOptFieldIsOneBit01(string srcFileName, StoreInst *SI);
		string MountOptFieldIsOneBitBooleanOrNegated(string srcFileName, StoreInst *SI);

		void TryGetAnotherExt4FillSuper(Function* ext4fillsuper, FilesystemInfoItem* filesystemInfoItem);
		Function* TryGetActualInitFs(Function* initfsctx);
		
	public:
		FilesystemExtractorPass(GlobalContext *Ctx_) :
			IterativeModulePass(Ctx_, "FilesystemExtractor") {}

		virtual bool doInitialization(llvm::Module *);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *);

};

#endif