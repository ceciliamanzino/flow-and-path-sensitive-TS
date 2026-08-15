module Semantic.Memory {n} where

open import Data.Empty
open import Data.Fin
  hiding (_+_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Function
open import Relation.Binary.PropositionalEquality 

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.VariableSet {n}


-- ver dónde están ------------------------------
n≮0 : ∀ {m} → m ≮ 0
n≮0 ()


-----------------------------------------------

-- State of the memory at a certain program point for the bracketed program.
Storeᵢ : Set 
Storeᵢ = Vec ℕ n

-- Update the value of a variable in memory.
infixl 6 _[_↦_]
_[_↦_] : Storeᵢ → Fin n → ℕ → Storeᵢ
m [ name ↦ v ] = m [ name ]≔ v

-- Semantic evaluation of expressions.
⟦_⟧ₑ : ExpS → Storeᵢ → ℕ
⟦ IntVal n ⟧ₑ m = n
⟦ Var v ⟧ₑ m = lookup m v
⟦ Add exp₁ exp₂ ⟧ₑ m = ⟦ exp₁ ⟧ₑ m + ⟦ exp₂ ⟧ₑ m

-- State of the memory at a certain program point for the transformed program.
Storeₜ : Set _
Storeₜ = Vec (List ℕ) n

-- lookupOr0 = lookupOrDefault
lookupOr0 : ℕ → List ℕ → ℕ
lookupOr0 _ [] = 0
lookupOr0 0 (x ∷ xs) = x
lookupOr0 (suc n) (x ∷ xs) = lookupOr0 n xs

-- update = safeListUpdate 
update : List ℕ → ℕ → ℕ → List ℕ
update [] _ _ = []
update (x ∷ xs) 0 v = v ∷ xs
update (x ∷ xs) (suc n) v = x ∷ (update xs n v)

-- Update the value of a variable in memory of the transformed program.
infixl 6 _[_↦_]ₜ
_[_↦_]ₜ : Storeₜ → Vars → ℕ → Storeₜ
m [ var , i ↦ v ]ₜ = 
  m [ var ]≔ (update (lookup m var) i v)

-- Semantic evaluation of tranformed expressions.
⟦_⟧ₜ : Exp → Storeₜ → ℕ
⟦ INTVAL n ⟧ₜ m = n
⟦ VAR (v , i) ⟧ₜ m = lookupOr0 i (lookup m v)       
⟦ ADD e₁ e₂ ⟧ₜ m = ⟦ e₁ ⟧ₜ m + ⟦ e₂ ⟧ₜ m

-- Lookup of a variable in a transformed memory.
lookupₜ : Storeₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ A x = lookupOr0 (lookup A x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set (Definition 2).
_==ₘ_-_ : Storeᵢ → Storeₜ → 𝒜 → Set
m ==ₘ mₜ - A = ∀ x → lookup m x ≡ lookupₜ mₜ A x

-- Equality between two memory projections on active sets.
_-_==ₘₜ_-_ : Storeₜ → 𝒜 → Storeₜ → 𝒜 → Set
mₜ - A ==ₘₜ mₜ' - A' = ∀ x → lookupₜ mₜ A x ≡ lookupₜ mₜ' A' x

-- Transitive property between ==ₘ and ==ₘₜ.
==ₘ-trans : {m : Storeᵢ} {mₜ mₜ' : Storeₜ} {A A' : 𝒜}
  → m ==ₘ mₜ - A
  → mₜ - A ==ₘₜ mₜ' - A'
  → m ==ₘ mₜ' - A'
==ₘ-trans meq meq' v = trans (meq v) (meq' v)   

-- MEMORY LOOKUP PROPERTIES
lookupx∘changex : 
  {X : Set} {m : ℕ} {v : X} (index : Fin m) (vector : Vec X m) 
  → lookup (vector [ index ]≔ v) index ≡ v
lookupx∘changex zero (head ∷ tail) = refl
lookupx∘changex (suc m) (head ∷ tail) = lookupx∘changex m tail 

lookupy∘changex : 
  {X : Set} {m : ℕ} {v : X} (i₁ i₂ : Fin m) (vector : Vec X m)
  → i₂ ≢  i₁
  → lookup (vector [ i₁ ]≔ v) i₂ ≡ lookup vector i₂
lookupy∘changex zero zero _ i₂<>i₁ = ⊥-elim (i₂<>i₁ refl)
lookupy∘changex zero (suc _) (_ ∷ _) _ = refl
lookupy∘changex (suc _) zero (_ ∷ _) _ = refl
lookupy∘changex (suc i₁') (suc i₂') (_ ∷ tail) i₂<>i₁ = lookupy∘changex i₁' i₂' tail (i₂<>i₁ ∘ cong suc)  


-- lookupx∘updatex = listLookupx∘listUpdatex
lookupx∘updatex : 
  {v : ℕ} (m : ℕ) (list : List ℕ)  
  → m <ₙ length list
  → lookupOr0 m (update list m v) ≡ v
lookupx∘updatex m [] i<0 = ⊥-elim (n≮0 i<0)
lookupx∘updatex 0 (_ ∷ _) _ = refl
lookupx∘updatex (suc i) (_ ∷ xs) si<ll = lookupx∘updatex i xs (<-pred si<ll)

lookupₜx∘changeₜx : 
  {m v var : ℕ} (i : Fin m) (vec : Vec (List ℕ) m) 
  → var <ₙ length (lookup vec i)
  → lookupOr0 var (lookup (vec [ i ]≔ (update (lookup vec i) var v)) i) ≡ v
lookupₜx∘changeₜx {var = v} zero (x ∷ _) v<lh = lookupx∘updatex v x v<lh
lookupₜx∘changeₜx (suc i) (_ ∷ xs) v<lvi = lookupₜx∘changeₜx i xs v<lvi

lookupₜy∘changeₜx : 
  {m v v₁ v₂ : ℕ} (i₁ i₂ : Fin m) (vec : Vec (List ℕ) m) 
  → i₂ ≢  i₁
  → lookupOr0 v₁ (lookup (vec [ i₁ ]≔ (update (lookup vec i₁) v₂ v)) i₂) ≡ lookupOr0 v₁ (lookup vec i₂)
lookupₜy∘changeₜx zero zero _ i₂<>i₁ = ⊥-elim (i₂<>i₁ refl)
lookupₜy∘changeₜx zero (suc _) (_ ∷ _) _ = refl
lookupₜy∘changeₜx (suc _) zero (_ ∷ _) _ = refl
lookupₜy∘changeₜx (suc i₁') (suc i₂') (_ ∷ xs) i₂<>i₁ = lookupₜy∘changeₜx i₁' i₂' xs (i₂<>i₁ ∘ cong suc)  

