module Transformation.ActiveSet {n} where


open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin 
  hiding (_≟_ ; _+_)
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties
open import Data.Product 
open import Data.Vec.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}

-- Active Sets.
-- Using a vector to represent a Fin n → ℕ mapping.
𝒜 : Set _
𝒜 = Vec ℕ n



-- Nunmber of variables used in an active set.
-- 𝒜varCount = fresh
fresh : {m : ℕ} → Vec ℕ m → ℕ
fresh [] = 0
fresh (h ∷ tl) = suc h + fresh tl

-- Active sets merge function from Figure 5.
merge𝒜 : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
merge𝒜 [] [] = []
merge𝒜 (h₁ ∷ tl₁) (h₂ ∷ tl₂) =
   (if h₁ == h₂ then h₁ else (suc (h₁ ⊔ h₂))) ∷ (merge𝒜 tl₁ tl₂)

-- Auxiliary property needed in the definition of active sets assignment.
0<n=>n'+1=n : {m : ℕ} → zero <ₙ m → Σ[ m' ∈ ℕ ] (suc m' ≡ m)
0<n=>n'+1=n (s≤s {zero} {n'} z≤n) = n' , refl

-- 𝒜varAssignment = x:=x'
x:=x' : Fin n → 𝒜 → 𝒜 → ASTStm
x:=x' var A A' with lookup A var ≟ lookup A' var 
...  | yes _ = SKIP
...  | no _  = ASSIGN (var , (lookup A var)) (VAR (var , (lookup A' var)))

 
postulate 𝒜assignAux : (m : ℕ) → m <ₙ n → 𝒜 → 𝒜 → ASTStm

-- 𝒜assignAux zero z<n A A' = x:=x' (fromℕ< z<n) A A'
-- 𝒜assignAux (suc m') m<n A A' = 
--  let m'<n = <-pred (m<n⇒m<1+n m<n)
--   in SEQ (x:=x' (fromℕ< m<n) A A') 
--          (𝒜assignAux m' m'<n A A')

-- Definition of active sets assignment from Figure 4.
_:=𝒜_ : 𝒜 → 𝒜 → ASTStm
A :=𝒜 A' with n ≟ zero 
...    | no n<>0 = let n' , n'+1=n = 0<n=>n'+1=n (n≢0⇒n>0 n<>0)
                       n'<n = subst (λ x → n' <ₙ x) n'+1=n (n<1+n n')
                    in 𝒜assignAux n' n'<n A A'
...    | yes _ = SKIP
