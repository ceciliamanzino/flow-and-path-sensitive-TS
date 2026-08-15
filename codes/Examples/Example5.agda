open import TypeSystem.SecurityTypes
open import Data.Nat

module Examples.Example5 {c ℓ₁ ℓ₂}
                      -- environment dimension
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂) where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.List
open import Data.Vec
  hiding ([_])

open import Data.Bool

n : ℕ
n = 4

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n = n} FChDBL
open import TypeSystem.TypeSystem {n = n} FChDBL

open FinChnDecBoundedLattice FChDBL 
  renaming (⊥ to Low ; ⊤ to High)


x : Fin n
x = zero

y : Fin n
y = suc zero 

s : Fin n
s = suc (suc zero)

p : Fin n
p = suc (suc (suc zero)) 


-- This example is similar to the introduction:
-- if (x > 0) then y := s else skip
-- if (x = 0) then p := y else skip

-- EXAMPLE 5: The type system accepts this program if a dependent
-- value is used in the security label of variable y, thus accepting
-- a program that requires path-sensitivity to be considered secure.

example5 : StmS
example5 = Seq (If (Var x) (y := Var s) Skip) (If (Var x) Skip (p := Var y))
               

env : TyEnv
env = [ Level Low ]  ∷ [ CondExp (VAR (x , zero)) (Level High) (Level Low) ] ∷ [ Level High ] ∷ [ Level Low ] ∷ [] 


typed : Maybe TypingProof
typed = typeProgram example5 env

ej5 : Bool
ej5 = isTyped example5 env




















