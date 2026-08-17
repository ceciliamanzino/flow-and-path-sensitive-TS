open import TypeSystem.SecurityTypes
open import Data.Nat
module Examples.Example4 {c ℓ₁ ℓ₂}
                      -- environment dimension
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂) where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.Vec
  hiding ([_])

open import Data.Bool

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

h : Fin n
h = suc (suc zero)

l : Fin n
l = suc (suc (suc zero)) 

l2 : Fin n
l2 = suc (suc (suc (suc zero)))

-- EXAMPLE 4: This program has an implicit declassification problem
-- when changing the value of l1 in the fourth instruction, so it
-- is rejected by our type system due to it being insecure.
example4 : StmS
example4 = Seq (x := IntVal 0)
          (Seq (y := IntVal 0)
          (Seq (If (Var l) Skip (y := Var h))
          (Seq (l := IntVal 1)
          (Seq (If (Var l) (x := Var y) Skip)
               (l2 := Var x)))))

typeEnv : TyEnv
typeEnv = [ Level Low ] ∷ [ CondExp (VAR (l , {!zero!})) (Level Low) (Level High) ] ∷ 
          [ Level High ] ∷ [ Level Low ] ∷ [ Level Low ] ∷ [] 

typed : Maybe TypingProof
typed = typeProgram example4 typeEnv

ej4 = isTyped example4 typeEnv
