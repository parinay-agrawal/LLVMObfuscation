#define DEBUG_TYPE "Loop_Version"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/RandomNumberGenerator.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/CommandLine.h"
#include <typeinfo>
#include <vector>
#include <cmath>
#include <random>
#include <cstring> 
#include <bits/stdc++.h>
using namespace llvm;
using namespace std;

cl::opt<unsigned> seed_rand("seed", cl::desc("Enter no of partitions"), cl::value_desc("Default = 10"));


namespace llvm {
    void changeval(Loop *L, int v);
    std::vector<Loop *> loops;
    struct Loop_Version : FunctionPass {
        static char ID;
        Loop_Version() : FunctionPass(ID) {}
        void getAnalysisUsage(AnalysisUsage &AU) const {                      
            AU.addRequired<LoopInfoWrapperPass>();  
            AU.addRequired<LoopAccessLegacyAnalysis>();
            AU.addRequired<DominatorTreeWrapperPass>(); 

        }
        void innermostloop(Loop *L, LoopInfo &LI){                  
              bool flag = false;
              for (auto *BB : L->getBlocks()){                            
                if (LI.getLoopFor(BB) != L){
                  flag = true;
                  continue;
                }                           
              }
              if(flag)
                for (Loop *SL : L->getSubLoops())
                  innermostloop(SL, LI);
              else{
                loops.push_back(L);
              }
        }

        unsigned long randomNumGen(){
            static unsigned long x=123456789, y=362436069, z=521288629;
            unsigned long t=seed_rand;
            x ^= x<<16;
            x ^= x>>5;
            x ^= x<<1;
            z = t ^ x ^ y ^ z;
            return z;
        }

        int get_random_classify(){
            return randomNumGen()%2;
        }

        Value* check_ins(Instruction *I, Instruction *I2, Instruction *cur){

            Type *T = llvm::Type::getInt32Ty(I->getContext());
            IRBuilder <Instruction*> Builder(cur);
            int para;
            
            if(I->getOpcode() == 31)
                para = 0;
            else
                para = 1;
            if(auto V = dyn_cast<ConstantInt>(I->getOperand(para))){
                
                int val = V->getSExtValue();
                auto alloc = Builder.CreateAlloca(T);
                alloc->setAlignment(4);
                string s1 = to_string(val);
                ConstantInt* int1  = ConstantInt::get(I->getContext(), APInt(32, StringRef(s1.c_str()), 10));
                (Builder.CreateStore(int1, alloc))->setAlignment(4);
                return alloc;
            }
            else{
                return I2->getOperand(0);
            }

        }
        
        void versioning(LoopInfo &LI, DominatorTree &DT, Function &F){
            for(auto *L : loops){
                Type *T = llvm::Type::getInt32Ty(F.getContext());
                int v = get_random_classify();
                Value *cond, *iter;
                ValueToValueMapTy VMap;
                SmallVector<BasicBlock *, 8> blocks;
                Instruction *I1, *I2, *I2_prev, *prev_ins;

                BasicBlock *ent = L->getLoopPreheader()->getUniquePredecessor();
                BasicBlock *exi = L->getUniqueExitBlock();
                BasicBlock *end = exi->getUniqueSuccessor();
                end->setName("if.end");
                BasicBlock *ifthen = BasicBlock::Create(ent->getContext(), Twine("if.then"), &F);
                BasicBlock *ifelse = BasicBlock::Create(ent->getContext(), Twine("if.else"), &F);
                BasicBlock *forend1 = BasicBlock::Create(ent->getContext(), Twine("for.end"), &F);
                BasicBlock *forend2 = BasicBlock::Create(ent->getContext(), Twine("for.end"), &F);
                BasicBlock *edge = BasicBlock::Create(ent->getContext(), Twine(exi->getName()), &F);
                dbgs() << exi->getName() << "\n";
        
                BasicBlock *BB1, *BB2;
                BB1 = L->getUniqueExitBlock();
                BB2 = BB1->getUniqueSuccessor();
                assert(L->getLoopPreheader());
                Loop *new_loop = cloneLoopWithPreheader(BB1, BB2, L, VMap, Twine(""), &LI, &DT, blocks);
                remapInstructionsInBlocks(blocks, VMap);
               
                for(Instruction &I : *ent){
                    if(I.getOpcode() == 31){
                        I1 = &I;
                    }
                    if(I.getOpcode() == 51){
                        I2_prev = prev_ins;
                        I2 = &I;
                    }
                    prev_ins = &I;
                }

                cond = check_ins(I2, I2_prev, I2);
                iter = I1->getOperand(1);


                
                string s1 = to_string(v);
                ConstantInt* int1  = ConstantInt::get(I1->getContext(), APInt(32, StringRef(s1.c_str()), 10));
                string s2 = to_string(1);
                ConstantInt* int2  = ConstantInt::get(I1->getContext(), APInt(32, StringRef(s2.c_str()), 10));
                
                IRBuilder <> build9(I2);
                auto alloc = build9.CreateAlloca(T);
                alloc->setAlignment(4);
                (build9.CreateStore(int1, alloc))->setAlignment(4);
                auto ld = build9.CreateLoad(alloc);
                ld->setAlignment(4);
                auto icmp = build9.CreateICmpSLT(ld, int2);
                build9.CreateCondBr(icmp, ifthen, ifelse);                
                
                Instruction *I5, *I6;
                for(auto &I : *ent){
                    I5 = I6;
                    I6 = &I;
                }
                I6->eraseFromParent();
                I5->eraseFromParent();

                IRBuilder <> build5(ifthen);
                auto l1 = build5.CreateLoad(iter);
                auto l2 = build5.CreateLoad(cond);
                l1->setAlignment(4);
                l2->setAlignment(4);
                auto l3 = build5.CreateICmp(dyn_cast<CmpInst>(I2)->getPredicate(), l1, l2);
                build5.CreateCondBr(l3, L->getLoopPreheader(), forend1);

                IRBuilder <> build6(ifelse);
                l1 = build6.CreateLoad(iter);
                l2 = build6.CreateLoad(cond);
                l1->setAlignment(4);
                l2->setAlignment(4);
                l3 = build6.CreateICmp(dyn_cast<CmpInst>(I2)->getPredicate(), l1, l2);
                build6.CreateCondBr(l3, new_loop->getLoopPreheader(), forend2);

                ent->getTerminator()->setSuccessor(0,ifthen);
                ent->getTerminator()->setSuccessor(1,ifelse);
               
                new_loop->getLoopLatch()->getTerminator()->setSuccessor(1,edge);
                IRBuilder <> build3(edge);
                build3.CreateBr(forend2);
                exi->getTerminator()->setSuccessor(0,forend1);
                IRBuilder <> build4(forend1);
                build4.CreateBr(end);
                IRBuilder <> build8(forend2);
                build8.CreateBr(end);
            }
        }
        bool runOnFunction(Function &F) override{ 
            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
            for(Loop *L : LI){   
                innermostloop(L, LI);
            }
            versioning(LI, DT, F);
            return false;
        }
    };
}


char Loop_Version::ID = 'a';
static RegisterPass<Loop_Version> X("Loop_Version", "Calculate Loop_Version");