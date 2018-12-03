#define DEBUG_TYPE "Loop-Reverse"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
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
#include <cstring> 
#include <bits/stdc++.h>
using namespace llvm;
using namespace std;


namespace llvm {
    void changeval(Loop *L, int v);
    std::vector<Loop *> loops;
    struct Loop_Reverse : FunctionPass {
        static char ID;
        Loop_Reverse() : FunctionPass(ID) {}
        void getAnalysisUsage(AnalysisUsage &AU) const {                      
            AU.addRequired<LoopInfoWrapperPass>();  
            AU.addRequired<LoopAccessLegacyAnalysis>();
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
        bool dependencies(Value *V, Loop *L, LoopInfo &LI){
            for(auto X : V->users()){
                if(auto Y = dyn_cast<Instruction>(X)){
                    if((Y->getOpcode() == 31 || Y->getOpcode() == 30)
                     && Y->getParent()!=L->getLoopLatch() && LI.getLoopFor(Y->getParent()) == L){
                        dbgs() << "Loop Dependecies: ILLEGAL TO REVERSE\n";
                        return false;
                    }
                }
            }
            return true;
        }
        void reverse(LoopInfo &LI, Function &F){
            for(auto *L : loops){
                Value *cond, *iter, *init, *incr;
                ValueToValueMapTy VMap;
                SmallVector<BasicBlock *, 8> blocks;
                Instruction *I1, *I2, *I3, *I1_prev, *I2_prev, *I3_prev, *prev_ins,*I4;
                BasicBlock *BB;

                BasicBlock *inc = L->getUniqueExitBlock()->getUniquePredecessor();
                BasicBlock *ent = L->getLoopPreheader()->getUniquePredecessor();
                BB = L->getLoopPreheader();
                
                for(Instruction &I : *ent){
                    if(I.getOpcode() == 31){
                        I1_prev = prev_ins;
                        I1 = &I;
                    }
                    if(I.getOpcode() == 51){
                        I2_prev = prev_ins;
                        I2 = &I;
                    }
                    if(I.getOpcode() == 2)
                        I4 = &I;
                    prev_ins = &I;
                }

                I3_prev = inc->getFirstNonPHI();
                for(Instruction &I : *inc){
                    if(I.getOpcode() == 11 || I.getOpcode() ==13){
                        I3 = &I;
                    }
                }

                init = check_ins(I1, I1_prev, I2);
                cond = check_ins(I2, I2_prev, I2);
                incr = check_ins(I3, I3_prev, I2);
                iter = I1->getOperand(1);

                if(!dependencies(init, L, LI))  return;
                if(!dependencies(cond, L, LI))  return;
                if(!dependencies(incr, L, LI))  return;
                if(!dependencies(iter, L, LI))  return;

                Type *T = llvm::Type::getInt32Ty(BB->getContext());
                IRBuilder <> Builder(I2);
                LoadInst* l1 = Builder.CreateLoad(T, cond);
                l1->setAlignment(4);
                (Builder.CreateStore(l1, iter))->setAlignment(4);

                auto l2 = Builder.CreateLoad(T, init);
                l2->setAlignment(4);
                auto l3 = Builder.CreateLoad(T, iter);
                l3->setAlignment(4);
                
                auto V = dyn_cast<CmpInst>(I2);
                Value * I_cmp;
                if(V->getPredicate() == 38)
                    I_cmp = (Builder.CreateICmpSLT(l3, l2));
                else if(V->getPredicate() == 39)
                    I_cmp = (Builder.CreateICmpSLE(l3, l2));
                else if(V->getPredicate() == 40)
                    I_cmp = (Builder.CreateICmpSGT(l3, l2));
                else if(V->getPredicate() == 41)
                    I_cmp = (Builder.CreateICmpSGE(l3, l2));
                else{
                    I_cmp = (Builder.CreateICmp(V->getPredicate(), l3, l2));
                }

                
                I4->setOperand(0,I_cmp);
                I2->eraseFromParent();

                
                Instruction * I_incr, *I_comp,*I_store,*I_br;
                BasicBlock *B_incr = L->getLoopLatch();
                for(Instruction & I: *B_incr){
                    if(I.getOpcode() ==11 || I.getOpcode() ==13 )
                        I_incr = &I;
                    else if(I.getOpcode() ==51)
                        I_comp = &I;
                    else if(I.getOpcode() ==31)
                        I_store = &I;
                    else if(I.getOpcode() == 2)
                        I_br = &I;
                }

                IRBuilder <> Builder1(I_incr);
                auto l4 = Builder1.CreateLoad(T, iter);
                l4->setAlignment(4);
                auto l5 = Builder1.CreateLoad(T, incr);
                l5->setAlignment(4);
                Value * new_I_incr;
                if(I_incr->getOpcode() ==11)
                    new_I_incr = Builder1.CreateNSWSub(l4,l5);
                else if(I_incr->getOpcode() ==13)
                    new_I_incr = Builder1.CreateNSWAdd(l4,l5);
                
                I_store->setOperand(0,new_I_incr);
                I_incr->eraseFromParent();

                
                IRBuilder <> Builder2(I_comp);
                auto V1 = dyn_cast<CmpInst>(I_comp);


                auto l6 = Builder2.CreateLoad(T, iter);
                l6->setAlignment(4);
                auto l7 = Builder2.CreateLoad(T, init);
                l7->setAlignment(4);
            

                if(V1->getPredicate() == 38)
                    I_cmp = (Builder2.CreateICmpSLT(l6, l7));
                else if(V1->getPredicate() == 39)
                    I_cmp = (Builder2.CreateICmpSLE(l6, l7));
                else if(V1->getPredicate() == 40)
                    I_cmp = (Builder2.CreateICmpSGT(l6, l7));
                else if(V1->getPredicate() == 41)
                    I_cmp = (Builder2.CreateICmpSGE(l6, l7));
                else{
                    I_cmp = (Builder2.CreateICmp(V1->getPredicate(), l6, l7));
                }
                
                I_br->setOperand(0,I_cmp);
                I_comp->eraseFromParent();


                BB = BB->getUniquePredecessor();
            }
        }
        bool runOnFunction(Function &F) override{ 
            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            for (Loop *L : LI){   
                innermostloop(L, LI);
            }
            reverse(LI,F);
            return false;
        }
    };
}


char Loop_Reverse::ID = 'a';
static RegisterPass<Loop_Reverse> X("Loop_Reverse", "Calculate Loop-Reverse");