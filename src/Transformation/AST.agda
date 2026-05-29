module Transformation.AST {n} where

open import Agda.Builtin.Nat 
open import Data.Bool.Base
open import Data.Fin
open import Data.Nat

open import Transformation.VariableSet {n}

-- Expressions for language with brackets.
data ASTExpS : Set where
   IntVal : ℕ → ASTExpS 
   Var    : Fin n → ASTExpS
   Add    : ASTExpS → ASTExpS → ASTExpS
   
-- Statements with brackets.
data ASTStmS : Set where
   Skip   : ASTStmS
   _:=_   : Fin n → ASTExpS → ASTStmS
   ⟦_:=_⟧ : Fin n → ASTExpS → ASTStmS
   Seq    : ASTStmS → ASTStmS → ASTStmS
   If    : ASTExpS → ASTStmS → ASTStmS → ASTStmS 
   While  : ASTExpS → ASTStmS → ASTStmS   

-- Expressions for language without brackets.
data ASTExp : Set where
   INTVAL : ℕ → ASTExp 
   VAR    : Vars → ASTExp
   ADD    : ASTExp → ASTExp → ASTExp 

-- Equality test for expressions.
_==ₑ_ : ASTExp → ASTExp → Bool
(INTVAL n₁) ==ₑ (INTVAL n₂) = n₁ == n₂
(VAR v₁) ==ₑ (VAR v₂) = v₁ ==ᵥ v₂
(ADD e₁ e₂) ==ₑ (ADD e₃ e₄) = (e₁ ==ₑ e₃) ∧ (e₂ ==ₑ e₄)
_ ==ₑ _ = false


-- expressionVariables = fv
-- Set of free variables of an expression.
fv : ASTExp → SetVar
fv (INTVAL _) = ∅ 
fv (VAR v) = singletonᵥₛ v
fv (ADD e₁ e₂) =  (fv e₁) ∪ (fv e₂)

-- Statements without brackets.
data ASTStm : Set where
   SKIP   : ASTStm 
   ASSIGN : Vars → ASTExp → ASTStm
   SEQ    : ASTStm → ASTStm → ASTStm 
   IF     : ASTExp → ASTStm → ASTStm → ASTStm 
   WHILE  : ASTExp → ASTStm → ASTStm 
   
-- Statements without brackets and with assignment identifiers.
-- A program is parameterized by the total number of assignment statements it has.
data ASTStmId (t : ℕ) : Set where
   SKIP   : ASTStmId t
   ASSIGN : Vars → Fin t → ASTExp → ASTStmId t
   SEQ    : ASTStmId t → ASTStmId t → ASTStmId t
   IF     : ASTExp → ASTStmId t → ASTStmId t → ASTStmId t
   WHILE  : ASTExp → ASTStmId t → ASTStmId t
   
