module Examples.Example1 where

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
x = raise 2 (fromℕ 0) 

h : Fin n
h = raise 1 (fromℕ 1) 

l : Fin n
l = fromℕ 2

-- EXAMPLE 1: This program is considered insecure by the type system 
-- due to not using the bracketed assignments to gain flow-sensitivity.
example1 : ASTStmS
example1 = Seq (x := Var h)
          (Seq (x := IntVal 0)
               (l := Var x))

typeEnv : TyEnv
typeEnv = (toList [ Level Low ]) ∷ 
          (toList [ Level High ]) ∷ 
          (toList [ Level Low ]) ∷ 
          [] 

typed : Maybe TypingProof
typed = typeProgram example1 typeEnv

ej1 : Bool 
ej1 = isTyped example1 typeEnv
