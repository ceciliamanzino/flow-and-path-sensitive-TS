module TypeSystem.Predicates {n} where

open import Data.Bool.Base
open import Data.List.Base
  hiding (replicate ; lookup)
open import Data.Nat
open import Data.Product
open import Data.Vec.Base 
open import Data.Fin.Base
open import Relation.Binary.PropositionalEquality 


open import Transformation.AST {n}
open import Transformation.VariableSet {n}

data Pred : Set where
    True : Pred
    ExpZ : Exp → Pred
    ExpNonZ : Exp → Pred
    And : Pred → Pred → Pred

simplify : Pred → Pred → Pred
simplify True p = p
simplify p True = p
simplify p q = And p q


-- Removes all parts of a predicate that contain a given variable.
removeVar : Pred → Vars → Pred
removeVar True _ = True
removeVar p@(ExpZ e) v = if v ∈ (fv e) then True else p
removeVar p@(ExpNonZ e) v = if v ∈ (fv e) then True else p
removeVar (And p₁ p₂) v = simplify (removeVar p₁ v) (removeVar p₂ v)


-- Equality test for predicates.
_==ₚ_ : Pred → Pred → Bool
True ==ₚ True = true
ExpZ e₁ ==ₚ ExpZ e₂ = e₁ ==ₑ e₂
ExpNonZ e₁ ==ₚ ExpNonZ e₂ = e₁ ==ₑ e₂
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

generate : {t : ℕ} → StmId t → Pred → Vec Pred t → Pred × (Vec Pred t)
generate SKIP p ps = p , ps

generate (ASSIGN v id _) p ps = removeVar p v , ps [ id ]≔ p

generate (SEQ s₁ s₂) p ps = let p' , ps' =  generate s₁ p ps
                            in generate s₂ p' ps'

generate (IF e sT sF) p ps = 
  let pT , psT = generate sT (simplify p (ExpNonZ e)) ps
      pF , psF = generate sF (simplify p (ExpZ e)) psT
   in intersect pT pF , psF

generate (WHILE e s) p ps =
   let p' , ps' = generate s (simplify p (ExpNonZ e)) ps
       p'' = intersect p p'
   in simplify p'' (ExpZ e) , ps'


-- Given a program statement, returns a vector of predicates so that the element in its n-th
-- position is a predicate that is always true before the execution of the n-th assignment 
-- of the program. 
generatePred : {t : ℕ} → StmId t → Vec Pred t
generatePred {t} stm = proj₂ (generate stm True (replicate {n = t} True))


