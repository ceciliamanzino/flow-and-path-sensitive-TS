open import TypeSystem.SecurityTypes
open import Data.Nat

module Examples.Example1 {c ℓ₁ ℓ₂}
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

-- EXAMPLE 1: This program is considered insecure by the type system 
-- due to not using the bracketed assignments to gain flow-sensitivity.
example1 : StmS
example1 = Seq (x := Var h)
          (Seq (x := IntVal 0)
               (l := Var x))

ex1 : StmS
ex1 = x := Var h


env : TyEnv
env = [ Level Low ] ∷ [ Level High ] ∷ [ Level Low ] ∷  [] 



typed : Maybe TypingProof
typed = typeProgram example1 env

ej1 : Bool 
ej1 = isTyped example1 env


