#define DEBUG_TYPE "Loop_Split"
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

cl::opt<unsigned> NSP("splits", cl::desc("Enter no of NSP"), cl::value_desc("Default = 3"));

namespace llvm {
    void changeval(Loop *L, int v);
    std::vector<Loop *> loops;
    struct Loop_Split : FunctionPass {
        static char ID;
        Loop_Split() : FunctionPass(ID) {}
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

        void add_init(BasicBlock *BB, Value *ptr1, Value *ptr2, Value *ptr3, Value *ptr4, CmpInst *In, BasicBlock *t, BasicBlock *f, int k){
            
            Instruction *I1;
            Type *T = llvm::Type::getInt32Ty(BB->getContext());
            for(Instruction &I : *BB){
                I1 = &I;
            }
            string stemp = to_string(k);
            ConstantInt* iter  = ConstantInt::get(BB->getContext(), APInt(32, StringRef(stemp.c_str()), 10));
             
            IRBuilder <> Builder(I1);
            LoadInst* load_inst1, *load_inst2;
            load_inst1 = Builder.CreateLoad(T, ptr2);
            load_inst2 = Builder.CreateLoad(T, ptr3);
            load_inst1->setAlignment(4);
            load_inst2->setAlignment(4);
            auto mul = BinaryOperator::Create(Instruction::Mul, load_inst2, iter, Twine("mu"), &*I1);
            auto add = BinaryOperator::Create(Instruction::Add, load_inst1, mul, Twine("inc"), &*I1);
            (Builder.CreateStore(add, ptr1))->setAlignment(4);
            load_inst1 = Builder.CreateLoad(T, ptr1);
            load_inst2 = Builder.CreateLoad(T, ptr4);
            load_inst1->setAlignment(4);
            load_inst2->setAlignment(4);
            
        }
        void add_change(BasicBlock *BB, int k){
            Instruction *I1;
            for(Instruction &I : *BB){
                if(I.getOpcode() == 15){
                    I1 = &I;
                    break;
                }
            }
            I1->setOperand(1, ConstantInt::get(I1->getOperand(1)->getType(), k));
        }

        bool dependencies(Value *V, Loop *L, LoopInfo &LI){
            for(auto X : V->users()){
                if(auto Y = dyn_cast<Instruction>(X)){
                    if((Y->getOpcode() == 31 || Y->getOpcode() == 30)
                     && Y->getParent()!=L->getLoopLatch() && LI.getLoopFor(Y->getParent()) == L){
                        dbgs() << "Loop Dependecies: ILLEGAL TO SPLIT\n";
                        return false;
                    }
                }
            }
            return true;
        }

        void add_inc(BasicBlock *BB, Value *ptr1, Value *ptr2){
            Instruction *I1;
            Type *T = llvm::Type::getInt32Ty(BB->getContext());
            for(Instruction &I : *BB){
                I1 = &I;
                break;
            }
            string stemp = to_string(NSP);
            ConstantInt* multiplier  = ConstantInt::get(BB->getContext(), APInt(32, StringRef(stemp.c_str()), 10));
            IRBuilder <> Builder(I1);
            LoadInst* load_inst1, *load_inst2;
            load_inst1 = Builder.CreateLoad(T, ptr1);
            load_inst2 = Builder.CreateLoad(T, ptr2);
            load_inst1->setAlignment(4);
            load_inst2->setAlignment(4);
            auto mul = BinaryOperator::Create(Instruction::Mul, load_inst2, multiplier, Twine("mu"), &*I1);
            auto add = BinaryOperator::Create(Instruction::Add, load_inst1, mul, Twine("inc"), &*I1);
            (Builder.CreateStore(add, ptr1))->setAlignment(4);
            bool flag1 = false, flag2 = false;
            deque <Instruction *> Ins;
            for(Instruction &I : *BB){
                if(I1 == &I)
                    flag1 = true;
                if(!flag1)
                    continue;
                if(flag2)
                    break;
                if(I.getOpcode() == 31){
                    flag2 = true;
                }
                Ins.push_front(&I);
            }
            int tot = Ins.size();
            for(int i = 0; i < tot; i++){
                Ins[i]->eraseFromParent();
            }
        }
        void split(LoopInfo &LI, DominatorTree &DT, Function &F, int NSP){
            for(auto *L : loops){
                Value *cond, *iter, *init, *incr;
                ValueToValueMapTy VMap;
                SmallVector<BasicBlock *, 8> blocks;
                Instruction *I1, *I2, *I3, *I1_prev, *I2_prev, *I3_prev, *prev_ins;
                BasicBlock *BB1, *BB2, *BB;

                BasicBlock *inc = L->getUniqueExitBlock()->getUniquePredecessor();
                BasicBlock *ent = L->getLoopPreheader()->getUniquePredecessor();
                BasicBlock *body = L->getLoopPreheader()->getUniqueSuccessor();
                BasicBlock *pre = L->getLoopPreheader();
                BasicBlock *exi = L->getUniqueExitBlock();
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
                    prev_ins = &I;
                }

                I3_prev = inc->getFirstNonPHI();
                for(Instruction &I : *inc){
                    if(I.getOpcode() == 11 || I.getOpcode() == 13){
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

                auto V = dyn_cast<CmpInst>(I2);

                BB = BB->getUniquePredecessor();
                
                BasicBlock *ins = CloneBasicBlock(L->getLoopPreheader(), VMap, Twine(""), &F,NULL,NULL);
                ent->getTerminator()->setSuccessor(0,ins);
                ins->getTerminator()->setSuccessor(0,pre);
                pre->getTerminator()->setSuccessor(0,body);
                add_init(pre, iter, init, incr, cond, V, body, exi, 0);
                add_inc(inc, iter, incr);
                
                BB1 = L->getUniqueExitBlock();
                BB2 = BB1->getUniqueSuccessor();
                assert(L->getLoopPreheader());
                Loop *new_loop[NSP-1];
                for(int i = 0; i < NSP-1; i++){
                    new_loop[i] = cloneLoopWithPreheader(BB1, BB2, L, VMap, Twine(""), &LI, &DT, blocks);
                    remapInstructionsInBlocks(blocks, VMap);
                    L->getLoopLatch()->getTerminator()->setSuccessor(1,new_loop[i]->getLoopPreheader());
                }
                add_change(L->getUniqueExitBlock(), 1);
                for(int i = 1; i < NSP-1; i++){
                    add_change(new_loop[i]->getUniqueExitBlock(), NSP-i);
                }
               

            }
        }
        bool runOnFunction(Function &F) override{ 
            if(!NSP)
                NSP = 3;
            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
            for (Loop *L : LI){   
                innermostloop(L, LI);
            }
            split(LI, DT, F, NSP);
            return false;
        }
    };
}


char Loop_Split::ID = 'a';
static RegisterPass<Loop_Split> X("Loop_Split", "Calculate Loop_Split");