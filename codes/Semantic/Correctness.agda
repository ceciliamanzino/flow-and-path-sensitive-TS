module Semantic.Correctness {n} where

open import Data.Empty
open import Data.Fin
  renaming (_≟_ to _≟f_)
open import Data.List
  hiding (lookup)
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 
open ≡-Reasoning

open import Semantic.CorrectnessLemmas {n}
open import Semantic.Memory {n}
open import Semantic.Semantic {n}
open import Semantic.WellFormed {n}
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}

mutual
  -- Correctness of the program transformation.
  correctness : {s : StmS} {m m' : Storeᵢ} {mₜ mₜ' : Storeₜ} {A : 𝒜}
    → ⟨ s , m ⟩⇓ m'
    → ⟨ proj₁ (transStm s A) , mₜ ⟩⇓ₜ mₜ'
    → wellFStm s mₜ A
    → m ==ₘ mₜ - A
    → m' ==ₘ mₜ' - (proj₂ (transStm s A))
  correctness Skip Skipₜ _ meq = meq
  correctness s@{x := e} {m} {.(m [ x ↦ ⟦ e ⟧ₑ m ])} {mₜ} {.(mₜ [ x , lookup A x ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ)} {A} 
    Assign
    Assignₜ
    (AssignWF wFmₜA)
    meq varName with varName ≟f x
  ...              | yes vN=x = begin
                                  lookup (m [ x ↦ ⟦ e ⟧ₑ m ]) varName
                                    ≡⟨ cong (λ y → lookup (m [ y ]≔ ⟦ e ⟧ₑ m) varName) (sym vN=x) ⟩  
                                  lookup (m [ varName ]≔ ⟦ e ⟧ₑ m) varName
                                    ≡⟨ lookupx∘changex varName m ⟩  
                                  ⟦ e ⟧ₑ m
                                    ≡⟨ expEquality {e} {m} {mₜ} meq refl refl ⟩
                                  ⟦ transExp e A ⟧ₜ mₜ
                                    ≡⟨ sym (lookupₜx∘changeₜx varName mₜ (wFmₜA varName)) ⟩
                                  lookupₜ (mₜ [ varName , lookup A varName ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) A varName
                                    ≡⟨ cong (λ y → lookupₜ (mₜ [ y , lookup A y ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) A varName) vN=x ⟩
                                  lookupₜ (mₜ [ x , lookup A x ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) A varName
                                ∎
  ...              | no vN!=x = begin 
                                  lookup (m [ x ↦ ⟦ e ⟧ₑ m ]) varName
                                    ≡⟨ lookupy∘changex x varName m vN!=x ⟩  
                                  lookup m varName 
                                    ≡⟨ meq varName ⟩  
                                  lookupₜ mₜ A varName
                                    ≡⟨ sym (lookupₜy∘changeₜx x varName mₜ vN!=x) ⟩ 
                                  lookupₜ (mₜ [ x , lookup A x ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) A varName  
                                ∎
  correctness s@{⟦ x := e ⟧} {m} {.(m [ x ↦ ⟦ e ⟧ₑ m ])} {mₜ} {mₜ'} {A} 
    AssignBr 
    Assignₜ 
    (AssignBrWF wFmₜA')
    meq varName with varName ≟f x
  ...              | yes vN=x = begin
                                    lookup (m [ x ↦ ⟦ e ⟧ₑ m ]) varName
                                  ≡⟨ cong (λ y → lookup (m [ y ↦ ⟦ e ⟧ₑ m ]) varName) (sym vN=x) ⟩  
                                    lookup (m [ varName ↦ ⟦ e ⟧ₑ m ]) varName
                                  ≡⟨ lookupx∘changex varName m ⟩  
                                    ⟦ e ⟧ₑ m
                                  ≡⟨ expEquality {e} {m} {mₜ} meq refl refl ⟩   
                                    ⟦ transExp e A ⟧ₜ mₜ
                                  ≡⟨ sym (lookupx∘updatex (suc (lookup A x)) (lookup mₜ x) (subst (λ y → y <ₙ length (lookup mₜ x)) (lookupx∘changex x A) (wFmₜA' x))) ⟩   
                                    lookupOr0 (suc (lookup A x)) (update (lookup mₜ x) (suc (lookup A x)) (⟦ transExp e A ⟧ₜ mₜ))
                                  ≡⟨ cong (λ y → lookupOr0 y (update (lookup mₜ x) (suc (lookup A x)) (⟦ transExp e A ⟧ₜ mₜ))) (sym (lookupx∘changex x A)) ⟩   
                                    lookupOr0 (lookup (A [ x ]≔ suc (lookup A x)) x) (update (lookup mₜ x) (suc (lookup A x)) (⟦ transExp e A ⟧ₜ mₜ))
                                  ≡⟨ cong (λ y → lookupOr0 (lookup (A [ x ]≔ suc (lookup A x)) x) y) (sym (lookupx∘changex x mₜ)) ⟩   
                                    lookupOr0 (lookup (A [ x ]≔ suc (lookup A x)) x) (lookup (mₜ [ x , suc (lookup A x) ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) x)
                                  ≡⟨⟩
                                    lookupₜ (mₜ [ x , suc (lookup A x) ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) (A [ x ]≔ suc (lookup A x)) x
                                  ≡⟨ cong (λ y → lookupₜ (mₜ [ x , suc (lookup A x) ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) (A [ x ]≔ suc (lookup A x)) y) (sym vN=x) ⟩   
                                    lookupₜ (mₜ [ x , suc (lookup A x) ↦ ⟦ transExp e A ⟧ₜ mₜ ]ₜ) (A [ x ]≔ suc (lookup A x)) varName
                                ∎
  ...              | no vN!=x = begin 
                                  lookup (m [ x ↦ ⟦ e ⟧ₑ m ]) varName
                                    ≡⟨ lookupy∘changex x varName m vN!=x ⟩  
                                  lookup m varName
                                    ≡⟨ meq varName ⟩  
                                  lookupₜ mₜ A varName  
                                    ≡⟨ sym (lookupₜy∘changeₜx x varName mₜ vN!=x) ⟩
                                  lookupₜ mₜ' A varName  
                                    ≡⟨ cong (λ y → lookupOr0 y (lookup mₜ' varName)) (sym (lookupy∘changex x varName A vN!=x)) ⟩
                                  lookupₜ mₜ' (proj₂ (transStm s A)) varName  
                                ∎
  correctness {Seq s₁ s₂} (Seq d₁ d₂) (Seqₜ dₜ₁ dₜ₂) (SeqWF wFs₁mₜA wFs₂mₜA') meq = 
    let correct₁ = correctness d₁ dₜ₁ wFs₁mₜA meq
        wFs₂mₜ₁A' = ? -- wellFTrans wFs₂mₜA' dₜ₁
     in correctness d₂ dₜ₂ wFs₂mₜ₁A' correct₁
  correctness {If cond sT sF} {m} {m'} {mₜ} {mₜ'} {A} 
    (IfT _ _ d) 
    (IfTₜ _ _ (Seqₜ {.mₜ} {mₜ₁} {.mₜ'} dₜ₁ dₜ₂))
    (IfWF wFmₜA' wFsTmₜA _)
    meq = 
      let AT = proj₂ (transStm sT A)
          AF = proj₂ (transStm sF A)
          A' = merge𝒜 AT AF
          m'=mₜ₁AT : m' ==ₘ mₜ₁ - AT
          m'=mₜ₁AT = correctness d dₜ₁ wFsTmₜA meq 
          mₜ₁AT=mₜ'A' : mₜ₁ - AT ==ₘₜ mₜ' - A'
          mₜ₁AT=mₜ'A' = :=𝒜-memEq dₜ₂ (wellFTrans {A = A'} wFmₜA' dₜ₁)
        in ==ₘ-trans {m'} {mₜ₁} {mₜ'} {AT} {A'} m'=mₜ₁AT mₜ₁AT=mₜ'A'
  correctness {If cond _ _} {m} {_} {mₜ} {_} {A} (IfT {v = v} em=v v<>0 _) (IfFₜ em'=0 _) _ meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {v} {0} {A} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')
  correctness {If cond _ _} {m} {_} {mₜ} {_} {A} (IfF em=0 _) (IfTₜ {v = v} em'=v v<>0 _) _ meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {0} {v} {A} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))
  correctness {If cond sT sF} {m} {m'} {mₜ} {mₜ'} {A}
    (IfF _ d) 
    (IfFₜ _ (Seqₜ {.mₜ} {mₜ₁} {.mₜ'} dₜ₁ dₜ₂))
    (IfWF wFmₜA' _ wFsFmₜA)
    meq = 
      let AT = proj₂ (transStm sT A)
          AF = proj₂ (transStm sF A)
          A' = merge𝒜 AT AF
          m'=mₜ₁AF : m' ==ₘ mₜ₁ - AF
          m'=mₜ₁AF = correctness d dₜ₁ wFsFmₜA meq
          mₜ₁AF=mₜ'A' : mₜ₁ - AF ==ₘₜ mₜ' - A'
          mₜ₁AF=mₜ'A' = :=𝒜-memEq dₜ₂ (wellFTrans {A = A'} wFmₜA' dₜ₁)
        in ==ₘ-trans {m'} {mₜ₁} {mₜ'} {AF} {A'} m'=mₜ₁AF mₜ₁AF=mₜ'A'
  correctness {While cond s} {m} {_} {mₜ} {_} {A} d 
    (Seqₜ {.mₜ} {mₜ₁} {_} dₜ₁ dₜ₂) 
    wF@(WhileWF wFmₜA₁ _)
    meq = 
      let A₁ = merge𝒜 A (proj₂ (transStm s A))
          mₜA=mₜ₁A₁ : mₜ - A ==ₘₜ mₜ₁ - A₁
          mₜA=mₜ₁A₁ = :=𝒜-memEq {A} {A₁} {mₜ} {mₜ₁} dₜ₁ wFmₜA₁
       in whileCorrectness refl refl refl refl d dₜ₂ (wellFTrans wF dₜ₁) (==ₘ-trans {m} {mₜ} {mₜ₁} {A} {A₁} meq mₜA=mₜ₁A₁)

  -- Correctness of the program transformation for the While case.
  whileCorrectness : {e : ExpS} {s : StmS} {e' : Exp} {s' : Stm} {m m' : Storeᵢ} {mₜ mₜ' : Storeₜ} {A A₁ A₂ : 𝒜}
    → e' ≡ transExp e A₁
    → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
    → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
    → A₂ ≡ proj₂ (transStm s A₁)
    → ⟨ While e s , m ⟩⇓ m'
    → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
    → wellFStm (While e s) mₜ A
    → m ==ₘ mₜ - A₁
    → m' ==ₘ mₜ' - A₁
  whileCorrectness _ _ _ _ (WhileF _) (WhileFₜ _) _ meq = meq
  whileCorrectness {e = e} {m = m} refl refl refl refl (WhileF em=0) (WhileTₜ {v = v} em'=v v<>0 _ _) _ meq = 
    let em=em' = expEquality {e} {m} {_} {0} {v} {_} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))
  whileCorrectness {e = e} {m = m} refl refl refl refl (WhileT {v = v} em=v v<>0 _ _) (WhileFₜ em'=0) _ meq = 
    let em=em' = expEquality {e} {m} {_} {v} {0} {_} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')
  whileCorrectness {A₁ = A₁} {A₂ = A₂} 
    refl refl refl refl
    (WhileT {m} {m₁} {m'} _ _ d₁ d₂) 
    (WhileTₜ {mₜ} {mₜ₂} {mₜ'} _ _ dₜ@(Seqₜ {.mₜ} {mₜ₁} {.mₜ₂} dₜ₁ dₜ₂) dₜ₃)
    wF@(WhileWF wFmₜA₁ wFsmₜA₁)
    meq = 
      let m₁=mₜ₁A₂ : m₁ ==ₘ mₜ₁ - A₂
          m₁=mₜ₁A₂ = correctness d₁ dₜ₁ wFsmₜA₁ meq
          mₜ₁A₂=mₜ₂A₁ : mₜ₁ - A₂ ==ₘₜ mₜ₂ - A₁
          mₜ₁A₂=mₜ₂A₁ = :=𝒜-memEq dₜ₂ (wellFTrans {A = A₁} wFmₜA₁ dₜ₁)
       in whileCorrectness refl refl refl refl d₂ dₜ₃ (wellFTrans wF dₜ) (==ₘ-trans {m₁} {mₜ₁} {mₜ₂} {A₂} {A₁} m₁=mₜ₁A₂ mₜ₁A₂=mₜ₂A₁)
