open import TypeSystem.SecurityTypes
open import Data.Nat

module Examples.Example3 {c ℓ₁ ℓ₂}
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
open import Data.Product

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

l1 : Fin n
l1 = suc (suc (suc zero)) 

l2 : Fin n
l2 = suc (suc (suc (suc zero)))

-- EXAMPLE 3: The type system accepts this program if a dependent
-- value is used in the security label of variable y, thus accepting
-- a program that requires path-sensitivity to be considered secure.

example3 : StmS
example3 = Seq (x := IntVal 0)
          (Seq (y := IntVal 0)
          (Seq (If (Var l1) Skip (y := Var h))
          (Seq (If (Var l1) (x := Var y) Skip)
               (l2 := Var x))))

typeEnv : TyEnv
typeEnv =  [ Level Low ]  ∷ [ CondExp (VAR ( l1 , zero) ) (Level Low) (Level High) ]  ∷ 
           [ Level High ]  ∷ [ Level Low ]  ∷ [ Level Low ]  ∷ [] 

typed : Maybe TypingProof
typed = typeProgram example3 typeEnv

ej3 : Bool
ej3 = isTyped example3 typeEnv
