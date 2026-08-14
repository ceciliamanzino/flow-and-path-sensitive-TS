module Examples.Example2 where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.Vec
open import Data.Bool

n : ℕ
n = 3

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n}
open import TypeSystem.TypeSystem {n}

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
typeEnv = (toList ((Level High) ∷ (Level Low) ∷ [])) ∷ 
          (toList [ Level High ]) ∷ 
          (toList [ Level Low ]) ∷ 
          [] 



typed : Maybe TypingProof
typed = typeProgram example2 typeEnv

ej2 = isTyped example2 typeEnv
