
module Examples.Example5 where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.Product
open import Data.Vec
  hiding ([_])
open import Data.Bool
open import Data.List


n : ℕ
n = 4

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n}
open import TypeSystem.TypeSystem {n}

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
env = [ Level Low ]  ∷ [ CondExp (VAR (x , zero)) (Level High) (Level Low) ] ∷ [ Level High ] ∷ [ Level Low ] ∷ [] -- {!(Level Low)  ∷ !}

-- typeEnv : TyEnv
-- typeEnv = (toList [ Level Low ]) ∷  
--          (toList (CondExp (VAR (x , zero)) (Level High) (Level Low) ∷ [])) ∷ 
--          (toList [ Level High ]) ∷ 
--          (toList [ Level Low ]) ∷
--          [] 

typed : Maybe TypingProof
typed = typeProgram example5 env

ej5 : Bool
ej5 = isTyped example5 env




















