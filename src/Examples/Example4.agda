module Examples.Example4 where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.Product
open import Data.Vec
open import Data.Bool

n : ℕ
n = 5

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n}
open import TypeSystem.TypeSystem {n}

x : Fin n
x = raise 4 (fromℕ 0) 

y : Fin n
y = raise 3 (fromℕ 1) 

h : Fin n
h = raise 2 (fromℕ 2) 

l1 : Fin n
l1 = raise 1 (fromℕ 3) 

l2 : Fin n
l2 = fromℕ 4

-- EXAMPLE 4: This program has an implicit declassification problem
-- when changing the value of l1 in the fourth instruction, so it
-- is rejected by our type system due to it being insecure.
example4 : ASTStmS
example4 = Seq (x := IntVal 0)
          (Seq (y := IntVal 0)
          (Seq (If (Var l1) Skip (y := Var h))
          (Seq (l1 := IntVal 1)
          (Seq (If (Var l1) (x := Var y) Skip)
               (l2 := Var x)))))

typeEnv : TyEnv
typeEnv = (toList [ Level Low ]) ∷  
          (toList [ CondExp (VAR (l1 , zero)) (Level Low) (Level High) ]) ∷ 
          (toList [ Level High ]) ∷ 
          (toList [ Level Low ]) ∷ 
          (toList [ Level Low ]) ∷
          [] 

typed : Maybe TypingProof
typed = typeProgram example4 typeEnv

ej4 = isTyped example4 typeEnv
