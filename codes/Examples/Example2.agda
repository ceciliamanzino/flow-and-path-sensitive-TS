open import TypeSystem.SecurityTypes
open import Data.Nat

module Examples.Example2 {c ℓ₁ ℓ₂}
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
n = 3

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n = n} FChDBL
open import TypeSystem.TypeSystem {n = n} FChDBL

open FinChnDecBoundedLattice FChDBL 
  renaming (⊥ to Low ; ⊤ to High)

x : Fin n
x = zero

h : Fin n
h = suc zero

l : Fin n
l = suc (suc zero)

-- EXAMPLE 2: This program is considered secure by the type system 
-- since the bracketed assignment breaks the false dataflow dependency
-- between l and h using x as proxy.
example2 : StmS
example2 = Seq (x := Var h)
          (Seq ⟦ x := IntVal 0 ⟧
               (l := Var x))

typeEnv : TyEnv
typeEnv = toList ((Level High) ∷ (Level Low) ∷ []) ∷ [ Level High ] ∷ [ Level Low ] ∷ [] 



typed : Maybe TypingProof
typed = typeProgram example2 typeEnv

ej2 = isTyped example2 typeEnv
