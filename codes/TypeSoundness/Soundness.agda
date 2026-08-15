module TypeSoundness.Soundness {n} where

open import Data.Bool.Base
open import Data.Bool.Properties
  hiding (≤-reflexive)
open import Data.Fin
  hiding (_≟_)
open import Data.List
  hiding (lookup ; replicate)
open import Data.Maybe.Base
open import Data.Nat
  hiding (_≟_ ; _⊔_ ; _⊓_)
open import Data.Nat.Properties
  hiding (_≟_)
open import Data.Product
open import Data.Vec.Base
  hiding (_++_ ; [_] ; _>>=_ ; toList)
open import Function.Base
open import Relation.Binary.PropositionalEquality
  hiding ([_])
open import Relation.Nullary
 
open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}
open import TypeSystem.AssignmentId {n}
open import TypeSystem.Liveness {n}
open import TypeSystem.Predicates {n}
open import TypeSystem.SecurityLabels {n}
open import TypeSystem.TypeSystem {n}
open import Semantic.Memory {n}
open import Transformation.ActiveSet {n}


-- Storeₜ = Vec (List ℕ) n

-- Definition 4 For a security label τ , we evaluate its concrete level under memory m ( ⟨ τ , m ⟩⇒  ℓ )  `
-- TΓ (x, m) = V(Γ(x), m)

infixl 5 ⟨_,_⟩⇒_
data ⟨_,_⟩⇒_ : SLabel → Storeₜ  → SecL → Set where
  Levelₑ : {ℓ : SecL}{m : Storeₜ} → ⟨ Level ℓ , m ⟩⇒ ℓ
  CondExpT : {m : Storeₜ} {e : Exp}{τ₁ τ₂ : SLabel}{ℓ : SecL}{v : ℕ}
     → ⟦ e ⟧ₜ m ≡ v
     → v ≢  0
     → ⟨ τ₁ , m ⟩⇒  ℓ
     → ⟨ CondExp e τ₁ τ₂ , m ⟩⇒  ℓ

  CondExpF : {m : Storeₜ} {e : Exp}{τ₁ τ₂ : SLabel}{ℓ : SecL}{v : ℕ}
     → ⟦ e ⟧ₜ m ≡ v
     → v ≡  0
     → ⟨ τ₂ , m ⟩⇒  ℓ
     → ⟨ CondExp e τ₁ τ₂ , m ⟩⇒  ℓ    
     
  Meetₑ : {m : Storeₜ}{τ₁ τ₂ : SLabel}{ℓ₁ ℓ₂ : SecL}
    → ⟨ τ₁ , m ⟩⇒  ℓ₁
    → ⟨ τ₂ , m ⟩⇒  ℓ₂
    → ⟨ Meet τ₁ τ₂ , m ⟩⇒  ℓ₁ ⊓ ℓ₂

  Joinₑ : {m : Storeₜ}{τ₁ τ₂ : SLabel}{ℓ₁ ℓ₂ : SecL}
    → ⟨ τ₁ , m ⟩⇒  ℓ₁
    → ⟨ τ₂ , m ⟩⇒  ℓ₂
    → ⟨ Meet τ₁ τ₂ , m ⟩⇒  ℓ₁ ⊔ ℓ₂ 



-- Definition 5 ((Γ, ℓ)-Equivalence) Given any concrete level ℓ and Γ, we say two memories m₁
-- and m₂ are equivalent up to ℓ under Γ (denoted by m₁ ≈[ ℓ , Γ ] m₂ ) if all variables
-- with a level below level ℓ agree on both their concrete levels and values.

_≈[_,_]_ : Storeₜ  → SecL → TyEnv → Storeₜ → Set
m₁ ≈[ ℓ , Γ ] m₂ = ∀ ((v , i) : Vars) → ∀  ℓ₁ ℓ₂ → ⟨ findType Γ (v , i) , m₁ ⟩⇒ ℓ₁ → ⟨ findType Γ (v , i) , m₂ ⟩⇒ ℓ₂
                         → ℓ₁ ≡ ℓ₂ → ℓ₂ ≲ ℓ →  lookupOr0 i (lookup m₁ v) ≡ lookupOr0 i (lookup m₂ v)   


_≃[_,_,_]_ : Storeₜ  → SecL → TyEnv → 𝒜 → Storeₜ → Set
m₁ ≃[ ℓ , Γ , A ] m₂ = ∀ ((x , i) : Vars) → ∀  ℓ₁ ℓ₂ → ⟨ findType Γ (x , i) , m₁ ⟩⇒ ℓ₁ → ⟨ findType Γ (x , i) , m₂ ⟩⇒ ℓ₂
                         → ℓ₁ ≡ ℓ₂ → ℓ₂ ≲ ℓ → lookupₜ m₁ A x ≡ lookupₜ m₂ A x    


-- two memories are Low ∼ si coinciden en los valores low
_∼[_,_]_ : Storeₜ  → TyEnv → 𝒜 → Storeₜ → Set
m₁ ∼[ Γ , A ] m₂ = ∀ ((x , i) : Vars)
                  → ⟨ findType Γ (x , i) , m₁ ⟩⇒ Low
                  → ⟨ findType Γ (x , i) , m₂ ⟩⇒ Low
                  → lookupₜ m₁ A x ≡ lookupₜ m₂ A x    

-- A typing environment Γ is well-formed, written ⊢Γ, if and only if: ∀x ∈ Vars. (∀x0 ∈ FV(Γ(x)). Γ(x0 ) v Γ(x)) ∧(∀x0 ∈ FV(Γ(x)). FV(Γ(x0 )) = ∅)

-- TyEnv = Vec (List SLabel) n 
-- findType : TyEnv → Vars → SLabel
-- fvl : SLabel → SetVar

⊢_ : TyEnv → Set
⊢ Γ = ∀ ((x , i) : Vars) → all (λ (x' , i') → is⊑ (findType Γ (x' , i')) (findType Γ (x , i))) (fvl (findType Γ (x , i))) ≡ true   

-- Equality between two memory projections on active sets.
-- _-_==ₘₜ_-_ : Storeₜ → 𝒜 → Storeₜ → 𝒜 → Set
-- mₜ - A ==ₘₜ mₜ' - A' = ∀ x → lookupₜ mₜ A x ≡ lookupₜ mₜ' A' x

-- NIₜ(S) = ∀ ρ ρ' .  ρᵢ ≃[Γ,t]ρᵢ' ∧ ⟨ s,ρᵢ ⟩⇓ᵢ ρ₁ ∧ ⟨ s,ρᵢ' ⟩⇓ᵢ ρ₂ ⇒ ρ₁ ≃[Γ,t] ρ₂
-- Type Soundness : p ⊢ s ⇒ NIₚ(S)
-------------------------------------------------------------------------------------


-- Auxiliary lemmas
-- Lemma 12 The type comparison is conservative: ∀m, τ1 , τ2 . τ1 ≲ τ2 ⇒ V(τ1 , m) ≲ V(τ2 , m)

-- postulate lemma12 : ∀ {τ₁ τ₂ : SLabel}{m : Storeₜ}{ℓ₁ ℓ₂ : SecL} →  τ₁ ≲ₗ τ₂ → ⟨ τ₁ , m ⟩⇒  ℓ₁ → ⟨ τ₁ , m ⟩⇒  ℓ₂ → ℓ₁ ≲ ℓ₂   

-- typeSoundess : {l : 𝕊} {ρᵢ ρᵢ' ρ₁ ρ₂ : Storeᵢ}  (s : Stm ⊥) → ρᵢ ≌[≤ l ] ρᵢ'  → (d : ⟨ s , ρᵢ ⟩⇓ᵢ ρ₁) 
--               → ⟨ s , ρᵢ' ⟩⇓ᵢ ρ₂  → (i : ℕ)         -- used for termination
--               → i ≥ dim' d   → ρ₁ ≌[≤ l ] ρ₂

--∀c, c, m1 , m2 , m01 , m02 , `, Γ, A, A0 .hc, Ai V hc, A0 i∧ ` Γ ∧ Γ ` c ∧ m1 ≈`ΓA m2 ∧
--hc, m1 i →∗ hskip, m01 i ∧ hc, m2 i →∗ hskip, m02 i = ⇒ m01 ≈`ΓA0 m02

typeSoundess : ∀ {s : StmS } {s' : Stm} {m₁ m₁' m₂ m₂' : Storeₜ} {Γ : TyEnv}{A A' : 𝒜}
             --  →  ⟨ proj₁ (transStm s A) , m₁ ⟩⇓ₜ m₁'                                -- s' = proj₁ (transStm s A) → 
             --  →  ⟨ proj₁ (transStm s A) , m₂ ⟩⇓ₜ m₂' 
               →  m₁ ∼[ Γ , A ] m₂
               →  m₁' ∼[ Γ , proj₂ (transStm s A) ] m₂'
typeSoundess = {!!} 
