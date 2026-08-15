open import TypeSystem.SecurityTypes
open import Data.Nat

module Examples.Example6 {c ℓ₁ ℓ₂}
                      -- environment dimension
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂) where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Product
open import Data.Vec
  hiding ([_])
open import Data.Bool
open import Data.List


n : ℕ
n = 5

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n = n} FChDBL
open import TypeSystem.TypeSystem {n = n} FChDBL

open FinChnDecBoundedLattice FChDBL 
  renaming (⊥ to Low ; ⊤ to High)


x : Fin n
x = zero

y : Fin n
y = suc zero 

z : Fin n
z = suc (suc zero) 

s : Fin n
s = suc (suc (suc zero))

p : Fin n
p = suc (suc (suc (suc zero))) 


-- This example is similar to (presented in section 3.2):
-- x := 0; y := 0;
-- if z = 0 then y := s else skip;
-- z := 1;
-- if z > 0 then x := y else skip;
-- p := x 

-- EXAMPLE 6: The type system rejects this program 

ex6 : StmS
ex6 = Seq (Seq (x := IntVal 0) (y := IntVal 0))
          (Seq (Seq (If (Var z) Skip (y := Var s)) (z := IntVal 1))
            (Seq (If (Var z) (x := Var y) Skip)
                 (p := Var x))) 
               

env : TyEnv
env = [ Level Low ] ∷ [ CondExp (VAR (z , zero)) (Level High) (Level Low) ] ∷ [ Level Low ] ∷ [ Level High ] ∷ [ Level Low ] ∷ [] 


typed : Maybe TypingProof
typed = typeProgram ex6 env

ej6 : Bool
ej6 = isTyped ex6 env

