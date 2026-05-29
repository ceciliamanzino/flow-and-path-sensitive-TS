module Semantic.WellFormed {n} where

open import Data.Fin
  renaming (_≟_ to _≟f_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Semantic.Memory {n}
open import Semantic.Semantic {n}
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}

-- A memory being well-formed relative to an active set means that it has
-- enough room to fit all variable subindices specified in the active set.

wellFormed : Storeₜ → 𝒜 → Set
wellFormed mₜ A = ∀ x → lookup A x <ₙ length (lookup mₜ x)

-- A statement and memory being well-formed relative to an active set
-- means that all memory states executing the statement are well-formed.
-- wellFStm = wellFormedStm

-- ver si se puede separar como propiedad de un código

data wellFStm : ASTStmS → Storeₜ → 𝒜 → Set where
  SkipWF : {mₜ : Storeₜ} {A : 𝒜}
    → wellFormed mₜ A
    → wellFStm Skip mₜ A
    
  AssignWF : {v : Fin n} {e : ASTExpS} {mₜ : Storeₜ} {A : 𝒜}
    → wellFormed mₜ A
    → wellFStm (v := e) mₜ A
    
  AssignBrWF : {v : Fin n} {e : ASTExpS} {mₜ : Storeₜ} {A : 𝒜}  
    → wellFormed mₜ (proj₂ (transStm ⟦ v := e ⟧ A))
    → wellFStm ⟦ v := e ⟧ mₜ A
    
  SeqWF : {s₁ s₂ : ASTStmS} {mₜ : Storeₜ} {A : 𝒜}
    → wellFStm s₁ mₜ A
    → wellFStm s₂ mₜ (proj₂ (transStm s₁ A))
    → wellFStm (Seq s₁ s₂) mₜ A
    
  IfWF : {e : ASTExpS} {sT sF : ASTStmS} {mₜ : Storeₜ} {A : 𝒜}
    → wellFormed mₜ (proj₂ (transStm (If e sT sF) A))
    → wellFStm sT mₜ A
    → wellFStm sF mₜ A
    → wellFStm (If e sT sF) mₜ A
    
  WhileWF : {e : ASTExpS} {s : ASTStmS} {mₜ : Storeₜ} {A : 𝒜}
    → wellFormed mₜ (merge𝒜 A (proj₂ (transStm s A)))
    → wellFStm s mₜ (merge𝒜 A (proj₂ (transStm s A)))
    → wellFStm (While e s) mₜ A

-- Auxiliary property: Updating a value of a list does not change its length.
-- lengthUpdateL=lengthL = lenUpdate=len
lenUpdate=len : (l : List ℕ) → (i : ℕ) → (val : ℕ) 
  → length (update l i val) ≡ length l
lenUpdate=len [] _ _ = refl
lenUpdate=len (_ ∷ _) zero _ = refl
lenUpdate=len (_ ∷ xs) (suc i) v = cong suc (lenUpdate=len xs i v)

-- wellFormed-trans = wellFTrans
wellFTrans : {s : ASTStm} {mₜ mₜ' : Storeₜ} {A : 𝒜} 
  → wellFormed mₜ A 
  → ⟨ s , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ' A
wellFTrans wFmₜA Skipₜ = wFmₜA
wellFTrans {_} {mₜ} {mₜ'} {A} wFmₜA (Assignₜ {_} {x , i} {e}) var with var ≟f x
...   | yes vN=x = let lmₜ'x=lUmₜx : lookup mₜ' x ≡ update (lookup mₜ x) i (⟦ e ⟧ₜ mₜ)
                       lmₜ'x=lUmₜx = lookupx∘changex x mₜ
                       lenlUmₜx=lenlmₜx : length (update (lookup mₜ x) i (⟦ e ⟧ₜ mₜ)) ≡ length (lookup mₜ x)
                       lenlUmₜx=lenlmₜx = lenUpdate=len (lookup mₜ x) i (⟦ e ⟧ₜ mₜ)
                       lenlmₜ'x=lenlmₜx : length (lookup mₜ' x) ≡ length (lookup mₜ x)
                       lenlmₜ'x=lenlmₜx = trans (cong length lmₜ'x=lUmₜx) lenlUmₜx=lenlmₜx
                       lenlmₜ'vN=lenlmₜvN : length (lookup mₜ' var) ≡ length (lookup mₜ var)
                       lenlmₜ'vN=lenlmₜvN = subst (λ v → length (lookup mₜ' v) ≡ length (lookup mₜ v)) (sym vN=x) lenlmₜ'x=lenlmₜx
                    in subst (λ v → lookup A var <ₙ v) (sym lenlmₜ'vN=lenlmₜvN) (wFmₜA var)
...   | no vN<>x = let lmₜ'vN=lmₜvN : lookup mₜ' var ≡ lookup mₜ var
                       lmₜ'vN=lmₜvN = lookupy∘changex x var mₜ vN<>x
                    in subst (λ v → lookup A var <ₙ length v) (sym lmₜ'vN=lmₜvN) (wFmₜA var)
wellFTrans {A = A} wFmₜA (Seqₜ d d') = 
  wellFTrans {A = A} (wellFTrans {A = A} wFmₜA d) d'
wellFTrans {A = A} wFmₜA (IfTₜ _ _ d) = wellFTrans {A = A} wFmₜA d
wellFTrans {A = A} wFmₜA (IfFₜ _ d) = wellFTrans {A = A} wFmₜA d
wellFTrans {A = A} wFmₜA (WhileTₜ _ _ d d') = 
  wellFTrans {A = A} (wellFTrans {A = A} wFmₜA d) d'
wellFTrans wFmₜA (WhileFₜ _) = wFmₜA

-- wellFormedStm-trans = wellF-tranStm
wellF-tranStm : {s : ASTStmS} {sₜ : ASTStm} {mₜ mₜ' : Storeₜ} {A : 𝒜}
  → wellFStm s mₜ A
  → ⟨ sₜ , mₜ ⟩⇓ₜ mₜ'
  → wellFStm s mₜ' A
  
wellF-tranStm {A = A} (SkipWF wFmₜA) d = 
  SkipWF (wellFTrans {A = A} wFmₜA d)
 
wellF-tranStm {A = A} (AssignWF wFmₜA) d = 
  AssignWF (wellFTrans {A = A} wFmₜA d)

wellF-tranStm (AssignBrWF {v} {e} {_} {A} wFmₜA') d = 
  AssignBrWF (wellFTrans {A = proj₂ (transStm ⟦ v := e ⟧ A)} wFmₜA' d)

wellF-tranStm (SeqWF wFs₁mₜA wFs₂mₜA) d = 
  SeqWF (wellF-tranStm wFs₁mₜA d) 
        (wellF-tranStm wFs₂mₜA d) 

wellF-tranStm (IfWF {e} {sT} {sF} {_} {A} wFmₜA' wFsTmₜA wFsFmₜA) d = 
  IfWF (wellFTrans {A = proj₂ (transStm (If e sT sF) A)} wFmₜA' d) 
       (wellF-tranStm wFsTmₜA d) 
       (wellF-tranStm wFsFmₜA d) 

wellF-tranStm (WhileWF {s = s} {A = A} wFmₜA' wFsmₜA') d = 
  WhileWF (wellFTrans {A = merge𝒜 A (proj₂ (transStm s A))} wFmₜA' d) 
          (wellF-tranStm wFsmₜA' d) 
