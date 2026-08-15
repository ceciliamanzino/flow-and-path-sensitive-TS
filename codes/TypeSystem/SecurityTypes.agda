module TypeSystem.SecurityTypes  where

open import Relation.Binary.Lattice
open import Level using (suc; _⊔_)
open import Relation.Binary
open import Data.Nat
  hiding (suc;_⊔_ ;_≟_)
  renaming (_<_ to _<ℕ_;_≤_ to _≤ℕ_) 
open import Data.Nat.Properties
  hiding (_≟_)
open import Algebra
open import Data.Product
open import Relation.Nullary

open import Relation.Binary.PropositionalEquality
  hiding (trans ; refl)

record IsFiniteChain {c ℓ₁ ℓ₂}
                     {A : Set c}
                     (_≈_ : Rel A ℓ₁)
                     (_<_ : Rel A (ℓ₁ ⊔ ℓ₂))
                     : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    ♯_               : A → ℕ     -- distance to ⊤  
    ♯-cong           : ∀ {x y : A} → x ≈ y → ♯ x ≡ ♯ y
    ♯-str-decreasing : ∀ {x y : A} → x < y → ♯ y <ℕ ♯ x
    ♯-min-uniqueness : ∀ {x y : A} → ♯ x ≡ 0 → ♯ y ≡ 0 → x ≡ y

record IsFinChnDecBoundedLattice
                           {c ℓ₁ ℓ₂}
                           {A : Set c}
                           (_≈_ : Rel A ℓ₁)
                           (_≤_ : Rel A ℓ₂)
                           (_∨_ : Op₂ A)
                           (⊤ : A)
                           (⊥ : A)
                           : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≟_
  field
    maximum            : Maximum _≤_ ⊤     
    isBJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥
    -- properties of equality
    _≟_                : Decidable _≈_
    ≈-subst            : ∀ {x y} → (P : A → Set ℓ₂) → x ≈ y → P x → P y
    ≈-cong             : ∀ {x y} → (f : A → A) → x ≈ y → f x ≈ f y
    _≲?_               : Decidable _≤_                -- Agregué esta línea
    
  _<_ : Rel A (ℓ₁ ⊔ ℓ₂)
  x < y = x ≤ y × ¬ x ≈ y  

  field
    isFiniteChain      : IsFiniteChain {c} {ℓ₁} {ℓ₂} _≈_ _<_ 

  open IsFiniteChain isFiniteChain public
  open IsBoundedJoinSemilattice isBJoinSemilattice public

  ∨-monotonic : _∨_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ∨-monotonic {x} {y} {u} {v} x≤y u≤v =
    let _     , _     , least  = supremum x u
        y≤y∨v , v≤y∨v , _      = supremum y v
    in least (y ∨ v) (trans x≤y y≤y∨v) (trans u≤v v≤y∨v)

  ∨-comm : ∀ x y → (x ∨ y) ≈ (y ∨ x)
  ∨-comm x y =
    let x<x∨y , y<x∨y , least  = supremum x y
        y<y∨x , x<y∨x , least' = supremum y x
    in antisym (least (y ∨ x) x<y∨x y<y∨x) (least' (x ∨ y) y<x∨y x<x∨y)

 

record FinChnDecBoundedLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_                 : Rel Carrier ℓ₂  -- The partial order.
    _∨_                : Op₂ Carrier     -- The join operation.
    _∧_                : Op₂ Carrier
    ⊤                  : Carrier         -- The maximum.
    ⊥                  : Carrier         -- The minimum.
    isFCDBoundedLattice : IsFinChnDecBoundedLattice _≈_ _≤_ _∨_  ⊤ ⊥
    
  open IsFinChnDecBoundedLattice isFCDBoundedLattice public

  

