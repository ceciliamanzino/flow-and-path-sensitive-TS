module Transformation.Transformation {n} where
                    
open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}

-- Expression transformation.
transExp : ExpS → 𝒜 → Exp
transExp (IntVal n) _ = INTVAL n
transExp (Var v) A = VAR (v , lookup A v)
transExp (Add exp₁ exp₂) A = ADD (transExp exp₁ A) (transExp exp₂ A)

-- Program transformation from bracketed to non-bracketed statements, following the rules from Figure 4.
transStm : StmS → 𝒜 → Stm × 𝒜
transStm Skip A = SKIP , A
transStm (v := e) A = ASSIGN (v , lookup A v) (transExp e A) , A

transStm ⟦ v := e ⟧ A =  let i = suc (lookup A v) 
                        in ASSIGN (v , i) (transExp e A) , A [ v ]≔ i

transStm (Seq s₁ s₂) A =  let tS₁ , A₁ = transStm s₁ A
                              tS₂ , A₂ = transStm s₂ A₁
                          in SEQ tS₁ tS₂ , A₂
    
transStm (If e sT sF) A =  let tE = transExp e A
                               tST , A₁ = transStm sT A
                               tSF , A₂ = transStm sF A
                               A₃ = merge𝒜 A₁ A₂
                               sT₁ = SEQ tST (A₃ :=𝒜 A₁)
                               sF₁ = SEQ tSF (A₃ :=𝒜 A₂)
                           in IF tE sT₁ sF₁ , A₃

transStm (While e s) A =  let _ , A₁ = transStm s A
                              A₂ = merge𝒜 A A₁
                              tE = transExp e A₂
                              tS , A₃ = transStm s A₂
                          in SEQ (A₂ :=𝒜 A) (WHILE tE (SEQ tS (A₂ :=𝒜 A₃))) , A₂

-- Transformation of a bracketed program to its non-bracketed version.
transform : StmS → Stm × 𝒜
transform stm = transStm stm (replicate {n = n} zero)
