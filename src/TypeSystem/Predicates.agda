module TypeSystem.Predicates {n} where

open import Data.Bool.Base
open import Data.List.Base
  hiding (replicate)
open import Data.Nat
open import Data.Product
open import Data.Vec.Base 
  hiding (replicate)

open import Transformation.AST {n}
open import Transformation.VariableSet {n}

data Pred : Set where
    True : Pred
    ExpZero : ASTExp → Pred
    ExpNonZero : ASTExp → Pred
    And : Pred → Pred → Pred

simplify : Pred → Pred → Pred
simplify True p = p
simplify p True = p
simplify p q = And p q


-- Removes all parts of a predicate that contain a given variable.
removeVar : Pred → Vars → Pred
removeVar True _ = True
removeVar p@(ExpZero e) v = if v ∈ (fv e) then True else p
removeVar p@(ExpNonZero e) v = if v ∈ (fv e) then True else p
removeVar (And p₁ p₂) v = simplify (removeVar p₁ v) (removeVar p₂ v)


-- Equality test for predicates.
_==ₚ_ : Pred → Pred → Bool
True ==ₚ True = true
ExpZero e₁ ==ₚ ExpZero e₂ = e₁ ==ₑ e₂
ExpNonZero e₁ ==ₚ ExpNonZero e₂ = e₁ ==ₑ e₂
And p₁ p₂ ==ₚ And p₃ p₄ = (p₁ ==ₚ p₃) ∧ (p₂ ==ₚ p₄)
_ ==ₚ _ = false


-- Checks if a base predicate is part of another predicate.
contains : Pred → Pred → Bool
contains p (And p₁ p₂) = (contains p p₁) ∨ (contains p p₂)
contains p₁ p₂ = p₁ ==ₚ p₂


-- Finds all base predicates that are part of both the given predicates and return a conjunction of them.
intersect : Pred → Pred → Pred
intersect (And p₁ p₂) p = simplify (intersect p₁ p) (intersect p₂ p)
intersect p₁ p₂ = if contains p₁ p₂ then p₁ else True


-- Iterates through the given program statement and determines a predicate that should always be true after its execution.
-- For that, it takes a predicate previous to the execution of the statement and uses that to determine predicates of the
-- intermediate steps of the execution doing a shallow branch analysis on IF and WHILE statements.
-- Additionally, when the function finds an assignment statement, it stores the predicate that was true before its execution
-- in the n-th index of a vector, where n is the index number of the assignment.

populate : {t : ℕ} → ASTStmId t → Pred → Vec Pred t → Pred × (Vec Pred t)
populate SKIP p ps = p , ps

populate (ASSIGN v id _) p ps = removeVar p v , ps [ id ]≔ p

populate (SEQ s₁ s₂) p ps = 
  let p' , ps' = populate s₁ p ps
  in populate s₂ p' ps'

populate (IF e sT sF) p ps = 
  let pT , psT = populate sT (simplify p (ExpNonZero e)) ps
      pF , psF = populate sF (simplify p (ExpZero e)) psT
   in intersect pT pF , psF

populate (WHILE e s) p ps = 
  let p' , ps' = populate s (simplify p (ExpNonZero e)) ps
      p'' = intersect p p'
   in simplify p'' (ExpZero e) , ps'


replicate : {A : Set}  {m : ℕ} → A → Vec A m
replicate {m = zero}  x = []
replicate {m = suc n} x = x ∷ replicate x


-- Given a program statement, returns a vector of predicates so that the element in its n-th
-- position is a predicate that is always true before the execution of the n-th assignment 
-- of the program. 
-- generatePredicates = generatePred
generatePred : {t : ℕ} → ASTStmId t → Vec Pred t
generatePred {t} stm = proj₂ (populate stm True (replicate {m = t} True))
