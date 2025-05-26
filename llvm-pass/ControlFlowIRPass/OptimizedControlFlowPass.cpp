/**
***  Optimized Version
***  This pass is used to record the control-flow of target program  
***  author: PengPeng
**/

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

#define OPERATION_TYPE_ENTRY 0x01
#define OPERATION_TYPE_EXIT  0x02
#define OPERATION_TYPE_HASH  0x03

using namespace llvm;

namespace {

struct OptimizedControlFlowPass : public PassInfoMixin<OptimizedControlFlowPass> {
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
        uint64_t counter = 1;
        uint64_t functionID = 1;
        uint64_t loopID = 1000000;

        FunctionAnalysisManager &FAM = 
            AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

        LLVMContext &Ctx = M.getContext();
        std::vector<Type*> paramTypes = {Type::getInt64Ty(Ctx)};
        Type *retType = Type::getVoidTy(Ctx);
        FunctionType *FT = FunctionType::get(retType, paramTypes, false);
        FunctionCallee trampolineFunc = M.getOrInsertFunction("trampoline", FT);

        for (Function &F : M.functions()) {
            if (F.isDeclaration() || F.getName() == "trampoline" || !shouldProcessFunction(&F)) {
                continue;
            }

            LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
            SmallPtrSet<BasicBlock*, 16> loopHeaders;
            SmallPtrSet<BasicBlock*, 16> loopLatches;
            collectLoopsHeader(LI, loopHeaders);
            collectLoopsLatch(LI, loopLatches);

            uint64_t operation = convert(OPERATION_TYPE_ENTRY, functionID);
            insertBeforeFunctionEntry(M, F, trampolineFunc, operation);
            functionID++;

            processLoops(M, LI, trampolineFunc, loopID, loopHeaders, loopLatches);

            for (BasicBlock &BB : F) {
                operation = convert(OPERATION_TYPE_EXIT, 0);
                insertBeforeReturnInst(M, BB, trampolineFunc, operation);
                if (&BB == &F.getEntryBlock() || loopHeaders.contains(&BB)) {
                    continue;
                }
                if (isConditionalTarget(BB, loopHeaders, loopLatches)) {
                    operation = convert(OPERATION_TYPE_HASH, counter);
                    insertBeforeBasicBlock(M, BB, trampolineFunc, operation);
                    counter++;
                }
            }
        }

        return PreservedAnalyses::none();
    }

private:
    bool isSystemPath(StringRef FilePath) {
        if (!FilePath.contains("/")) {
            return false;
        }
        if (FilePath.starts_with("/usr/include")) {
            return true;
        }
        if (FilePath.contains("Xcode.app/Contents/Developer/Platforms/")) {
            return true;
        }
        return false;
    }

    bool shouldProcessFunction(Function *F) {
        if (DISubprogram *SP = F->getSubprogram()) {
            if (DIFile *File = SP->getFile()) {
                StringRef FilePath = File->getFilename();
                return !isSystemPath(FilePath);
            }
        }
        return true;
    }

    bool isDoWhileLoopType(Loop *loop) {
        if (!loop) {
            return false;
        }
        BasicBlock *header = loop->getHeader();
        BasicBlock *latch = loop->getLoopLatch();
        return latch && latch == header->getSingleSuccessor();
    }

    void collectLoopsHeader(LoopInfo &LI, SmallPtrSetImpl<BasicBlock*> &loopHeaders) {
        std::function<void(Loop*)> collectHeader = [&](Loop *loop) {
            if (BasicBlock *header = loop->getHeader()) {
                loopHeaders.insert(header);
            }
            for (Loop *subLoop : loop->getSubLoops()) {
                collectHeader(subLoop);
            }
        };

        for (Loop *loop : LI) {
            collectHeader(loop);
        }
    }

    void collectLoopsLatch(LoopInfo &LI, SmallPtrSetImpl<BasicBlock*> &loopLatches) {
        std::function<void(Loop*)> collectLatch = [&](Loop *loop) {
            if (BasicBlock *latch = loop->getLoopLatch()) {
                loopLatches.insert(latch);
            }
            for (Loop *subLoop : loop->getSubLoops()) {
                collectLatch(subLoop);
            }
        };

        for (Loop *loop : LI) {
            collectLatch(loop);
        }
    }

    bool isConditionalTarget(BasicBlock &BB, SmallPtrSetImpl<BasicBlock*> &loopHeaders, SmallPtrSetImpl<BasicBlock*> &loopLatches) {
        for (BasicBlock *pre : predecessors(&BB)) {
            if (auto *BI = dyn_cast<BranchInst>(pre->getTerminator())) {
                if (BI->isConditional()) {
                    return !(loopHeaders.contains(pre) || loopLatches.contains(pre));
                }
            }
        }

        return false;
    }

    bool isComplexLoop(Loop *loop, SmallPtrSetImpl<BasicBlock*> &loopHeaders, SmallPtrSetImpl<BasicBlock*> &loopLatches) {
        if (!loop) {
            return false;
        }
        for (Loop *subLoop : loop->getSubLoops()) {
            if (isComplexLoop(subLoop, loopHeaders, loopLatches)) {
                return true;
            }
        }
        for (BasicBlock *BB : loop->getBlocks()) {
            for (Instruction &I : *BB) {
                if (auto *CI = dyn_cast<CallInst>(&I)) {
                    if (Function *Callee = CI->getCalledFunction()) {
                        if (Callee->getName() != "trampoline" && shouldProcessFunction(Callee)) {
                            return true;
                        }
                    } else {
                        return true;
                    }
                }
            }
            if (loopHeaders.contains(BB) || loopLatches.contains(BB)) {
                continue;
            }
            if (auto *BI = dyn_cast<BranchInst>(BB->getTerminator())) {
                return BI->isConditional();
            }
        }
        
        return false;
    }

    uint64_t convert(uint64_t type, uint64_t value) {
        return (value << 2) | type;
    }

    void insertBeforeBasicBlock(Module &M, BasicBlock &BB, FunctionCallee &trampolineFunc, uint64_t operation) {
        IRBuilder<> builder(&BB, BB.getFirstInsertionPt());
        Constant *param = 
            ConstantInt::get(Type::getInt64Ty(M.getContext()), operation, false);
        std::vector<Value*> args = {param};
        builder.CreateCall(trampolineFunc, args);
    }

    void insertBeforeFunctionEntry(Module &M, Function &F, FunctionCallee &trampolineFunc, uint64_t operation) {
        BasicBlock &entryBB = F.getEntryBlock();
        insertBeforeBasicBlock(M, entryBB, trampolineFunc, operation);
    }

    void insertBeforeReturnInst(Module &M, BasicBlock &BB, FunctionCallee &trampolineFunc, uint64_t operation) {
        for (Instruction &I : BB) {
            if (auto *ret = dyn_cast<ReturnInst>(&I)) {
                IRBuilder<> builder(ret);
                Constant *param = 
                    ConstantInt::get(Type::getInt64Ty(M.getContext()), operation, false);
                std::vector<Value*> args = {param};
                builder.CreateCall(trampolineFunc, args);
            }
        }
    }

    void processLoops(Module &M, LoopInfo &LI, FunctionCallee &trampolineFunc, 
        uint64_t &loopID, SmallPtrSetImpl<BasicBlock*> &loopHeaders, SmallPtrSetImpl<BasicBlock*> &loopLatches) {
        
        std::function<void(Loop*)> process = [&](Loop *loop) {
            if (!isComplexLoop(loop, loopHeaders, loopLatches)) {
                return;
            }

            if (BasicBlock *header = loop->getHeader()) {
                IRBuilder<> builder(&header->front());
                uint64_t operation = convert(OPERATION_TYPE_ENTRY, loopID);
                loopID++;
                Constant *param = 
                    ConstantInt::get(Type::getInt64Ty(M.getContext()), operation, false);
                std::vector<Value*> args = {param};
                builder.CreateCall(trampolineFunc, args);
            }
            if (BasicBlock *latch = loop->getLoopLatch()) {
                if (auto *term = latch->getTerminator()) {
                    IRBuilder<> builder(term);
                    uint64_t operation = convert(OPERATION_TYPE_EXIT, 0);
                    Constant *param = 
                        ConstantInt::get(Type::getInt64Ty(M.getContext()), operation, false);
                    std::vector<Value*> args = {param};
                    builder.CreateCall(trampolineFunc, args);
                }
            }

            if (!isDoWhileLoopType(loop)) {
                SmallVector<BasicBlock*, 4> exits;
                loop->getExitBlocks(exits);
                for (BasicBlock *exitBB : exits) {
                    if (exitBB) {
                        IRBuilder<> builder(&exitBB->front());
                        uint64_t operation = convert(OPERATION_TYPE_EXIT, 0);
                        Constant *param = 
                            ConstantInt::get(Type::getInt64Ty(M.getContext()), operation, false);
                        std::vector<Value*> args = {param};
                        builder.CreateCall(trampolineFunc, args);
                    }
                }
            }

            for (Loop *subLoop : loop->getSubLoops()) {
                process(subLoop);
            }
        };

        for (Loop *loop : LI) {
            process(loop);
        }
    }
};

}

extern "C" LLVM_ATTRIBUTE_WEAK::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
    return {
        .APIVersion = LLVM_PLUGIN_API_VERSION,
        .PluginName = "Optimized Control Flow Pass",
        .PluginVersion = "v1.0",
        .RegisterPassBuilderCallbacks = [](PassBuilder &PB) {
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                    MPM.addPass(OptimizedControlFlowPass());
                }
            );
        }
    };
}
