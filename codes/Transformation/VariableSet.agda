module Transformation.VariableSet {n} where

open import Agda.Builtin.Nat
  renaming (_<_ to _<ₙ_ ; _==_ to _==ₙ_)
open import Data.Bool.Base
open import Data.Nat
open import Data.Fin
open import Data.List.Base
open import Data.Product
open import Function.Base

-- A variable in a transformed program consists of a variable name (represented by a Fin n)
-- and a natural number subindex indicating its version in the active set in a certain program point.
-- TransVariable = Vars

Vars : Set _
Vars = Fin n × ℕ

-- We represent sets of variables with lists without repeated elements.
-- VariableSet = SetVar
SetVar : Set _
SetVar = List Vars

-- Variable equality test.
_==ᵥ_ : Vars → Vars → Bool
(v₁ , i₁) ==ᵥ (v₂ , i₂) = (toℕ v₁ ==ₙ toℕ v₂) ∧ (i₁ ==ₙ i₂)

-- Element check.
-- elem = ∈
_∈_ : Vars → SetVar → Bool
_ ∈ [] = false
v₁ ∈ (v₂ ∷ vs) = (v₁ ==ᵥ v₂) ∨ (v₁ ∈ vs) 

-- Conversion from and to lists.
-- fromListᵥₛ = fromList
fromList : List Vars → SetVar
fromList = foldr (λ v vs → if v ∈ vs then vs else v ∷ vs) [] 

-- Empty set.
-- emptyᵥₛ =  ∅  
∅ : SetVar
∅ = fromList []

-- Set size.
sizeᵥₛ : SetVar → ℕ
sizeᵥₛ = length 

-- Singleton set.
-- singletonᵥₛ =  {_}
singletonᵥₛ : Vars → SetVar
singletonᵥₛ v = fromList (v ∷ [])

-- Element removal.
popᵥₛ : Vars → SetVar → SetVar
popᵥₛ _ [] = []
popᵥₛ v₁ (v₂ ∷ vs) = if v₁ ==ᵥ v₂ then vs else v₂ ∷ (popᵥₛ v₁ vs)

-- Operations between sets.
-- unionᵥₛ = ∪ 

_∪_ : SetVar → SetVar → SetVar
vs₁ ∪ vs₂ = fromList (vs₁ ++ vs₂) 

_diffᵥₛ_ : SetVar → SetVar → SetVar
vs diffᵥₛ [] = vs
vs₁ diffᵥₛ (v ∷ vs₂) = (popᵥₛ v vs₁) diffᵥₛ vs₂

-- Set comparisons.
-- subsetᵥₛ = ⊆
_⊆_ : SetVar → SetVar → Bool
[] ⊆ _ = true
(v ∷ vs₁) ⊆ vs₂ = (v ∈ vs₂) ∧ (vs₁ ⊆ vs₂)

-- strictSubset =⊂
_⊂_ : SetVar → SetVar → Bool
vs₁ ⊂ vs₂ = (sizeᵥₛ vs₁ <ₙ sizeᵥₛ vs₂) ∧ (vs₁ ⊆ vs₂)
 
_==ᵥₛ_ : SetVar → SetVar → Bool
vs₁ ==ᵥₛ vs₂ = (sizeᵥₛ vs₁ ==ₙ sizeᵥₛ vs₂) ∧ (vs₁ ⊆ vs₂) 

 
