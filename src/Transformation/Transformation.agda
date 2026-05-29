module Transformation.Transformation {n} where

open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}

-- Expression transformation.
transExp : ASTExpS → 𝒜 → ASTExp
transExp (IntVal n) _ = INTVAL n
transExp (Var v) A = VAR (v , lookup A v)
transExp (Add exp₁ exp₂) A = ADD (transExp exp₁ A) (transExp exp₂ A)

-- Program transformation from bracketed to non-bracketed statements, following the rules from Figure 4.
transStm : ASTStmS → 𝒜 → ASTStm × 𝒜
transStm Skip A = SKIP , A

transStm (v := e) A = ASSIGN (v , lookup A v) (transExp e A) , A

transStm ⟦ v := e ⟧ A = 
   let i = suc (lookup A v) 
    in ASSIGN (v , i) (transExp e A) , A [ v ]≔ i

transStm (Seq s₁ s₂) A = 
   let tS₁ , A₁ = transStm s₁ A
       tS₂ , A₂ = transStm s₂ A₁
    in SEQ tS₁ tS₂ , A₂
    
transStm (If cond sT sF) A =
   let tCond = transExp cond A
       tST , A₁ = transStm sT A
       tSF , A₂ = transStm sF A
       A₃ = merge𝒜 A₁ A₂
       sT₁ = SEQ tST (A₃ :=𝒜 A₁)
       sF₁ = SEQ tSF (A₃ :=𝒜 A₂)
    in IF tCond sT₁ sF₁ , A₃

transStm (While cond s) A =
   let _ , A₁ = transStm s A
       A₂ = merge𝒜 A A₁
       tCond = transExp cond A₂
       tS , A₃ = transStm s A₂
    in SEQ (A₂ :=𝒜 A) (WHILE tCond (SEQ tS (A₂ :=𝒜 A₃))) , A₂

zeros : (n : ℕ) → ℕ → Vec ℕ n
zeros zero  x = []
zeros (suc n) x = x ∷ zeros n x

-- Transformation of a bracketed program to its non-bracketed version.
transform : ASTStmS → ASTStm × 𝒜
transform stm = transStm stm (zeros n zero)
