module Transformation.AST {n} where

open import Agda.Builtin.Nat 
open import Data.Bool.Base
open import Data.Fin
open import Data.Nat

open import Transformation.VariableSet {n}

-- Expressions for language with brackets.
data ExpS : Set where
   IntVal : ℕ → ExpS 
   Var    : Fin n → ExpS
   Add    : ExpS → ExpS → ExpS
   
-- Statements with brackets.
data StmS : Set where
   Skip   : StmS
   _:=_   : Fin n → ExpS → StmS
   ⟦_:=_⟧ : Fin n → ExpS → StmS
   Seq    : StmS → StmS → StmS
   If    : ExpS → StmS → StmS → StmS 
   While  : ExpS → StmS → StmS   

-- Expressions for language without brackets.
data Exp : Set where
   INTVAL : ℕ → Exp 
   VAR    : Vars → Exp
   ADD    : Exp → Exp → Exp 

-- Equality test for expressions.
_==ₑ_ : Exp → Exp → Bool
(INTVAL n₁) ==ₑ (INTVAL n₂) = n₁ == n₂
(VAR v₁) ==ₑ (VAR v₂) = v₁ ==ᵥ v₂
(ADD e₁ e₂) ==ₑ (ADD e₃ e₄) = (e₁ ==ₑ e₃) ∧ (e₂ ==ₑ e₄)
_ ==ₑ _ = false


-- expressionVariables = fv
-- Set of free variables of an expression.
fv : Exp → SetVar
fv (INTVAL _) = ∅ 
fv (VAR v) = singletonᵥₛ v
fv (ADD e₁ e₂) =  (fv e₁) ∪ (fv e₂)


-- Statements without brackets.
data Stm : Set where
   SKIP   : Stm 
   ASSIGN : Vars → Exp → Stm
   SEQ    : Stm → Stm → Stm 
   IF     : Exp → Stm → Stm → Stm 
   WHILE  : Exp → Stm → Stm 
   
-- Statements without brackets and with assignment identifiers.
-- A program is parameterized by the total number of assignment statements it has.
data StmId (t : ℕ) : Set where
   SKIP   : StmId t
   ASSIGN : Vars → Fin t → Exp → StmId t
   SEQ    : StmId t → StmId t → StmId t
   IF     : Exp → StmId t → StmId t → StmId t
   WHILE  : Exp → StmId t → StmId t
   
