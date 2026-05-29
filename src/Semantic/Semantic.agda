module Semantic.Semantic {n} where

open import Data.Fin
open import Data.Nat 
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}
open import Transformation.VariableSet {n}
open import Semantic.Memory {n}
open import TypeSystem.SecurityLabels {n}

-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓_
data ⟨_,_⟩⇓_ : ASTStmS → Storeᵢ → Storeᵢ → Set where
  Skip : {m : Storeᵢ} → ⟨ Skip , m ⟩⇓ m
  Assign : {m : Storeᵢ} {v : Fin n} {e : ASTExpS} 
    → ⟨ v := e , m ⟩⇓ m [ v  ↦ ⟦ e ⟧ₑ m ]
  AssignBr : {m : Storeᵢ} {v : Fin n} {e : ASTExpS} 
    → ⟨ ⟦ v := e ⟧ , m ⟩⇓ m [ v  ↦ ⟦ e ⟧ₑ m ]
  Seq : {m m' m'' : Storeᵢ} {s₁ s₂ : ASTStmS}
    → ⟨ s₁ , m ⟩⇓ m'  
    → ⟨ s₂ , m' ⟩⇓ m'' 
    → ⟨ Seq s₁ s₂ , m ⟩⇓ m'' 
  IfT : {m m' : Storeᵢ} {e : ASTExpS} {v : ℕ} {sT sF : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ sT , m ⟩⇓ m' 
    → ⟨ If e sT sF , m ⟩⇓ m'  
  IfF : {m m' : Storeᵢ} {e : ASTExpS} {sT sF : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ 0 
    → ⟨ sF , m ⟩⇓ m' 
    → ⟨ If e sT sF , m ⟩⇓ m'  
  WhileT : {m m' m'' : Storeᵢ} {e : ASTExpS} {v : ℕ} {s : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ s , m ⟩⇓ m'  
    → ⟨ While e s , m' ⟩⇓ m'' 
    → ⟨ While e s , m ⟩⇓ m''
  WhileF : {m : Storeᵢ} {e : ASTExpS} {s : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ 0 
    → ⟨ While e s , m ⟩⇓ m

-- Big step semantics of transformed statements.
infixl 5 ⟨_,_⟩⇓ₜ_
data ⟨_,_⟩⇓ₜ_ : ASTStm → Storeₜ → Storeₜ → Set where
  Skipₜ : {mₜ : Storeₜ} → ⟨ SKIP , mₜ ⟩⇓ₜ mₜ
  Assignₜ : {mₜ : Storeₜ} {v : Vars} {e : ASTExp} 
    → ⟨ ASSIGN v e , mₜ ⟩⇓ₜ mₜ [ v  ↦ ⟦ e ⟧ₜ mₜ ]ₜ
  Seqₜ : {mₜ mₜ' mₜ'' : Storeₜ} {s₁ s₂ : ASTStm}
    → ⟨ s₁ , mₜ ⟩⇓ₜ mₜ'  
    → ⟨ s₂ , mₜ' ⟩⇓ₜ mₜ'' 
    → ⟨ SEQ s₁ s₂ , mₜ ⟩⇓ₜ mₜ'' 
  IfTₜ : {mₜ mₜ' : Storeₜ} {e : ASTExp} {v : ℕ} {sT sF : ASTStm}
    → ⟦ e ⟧ₜ mₜ ≡ v
    → v ≢  0 
    → ⟨ sT , mₜ ⟩⇓ₜ mₜ' 
    → ⟨ IF e sT sF , mₜ ⟩⇓ₜ mₜ'  
  IfFₜ : {mₜ mₜ' : Storeₜ} {e : ASTExp} {sT sF : ASTStm}
    → ⟦ e ⟧ₜ mₜ ≡ 0 
    → ⟨ sF , mₜ ⟩⇓ₜ mₜ' 
    → ⟨ IF e sT sF , mₜ ⟩⇓ₜ mₜ'  
  WhileTₜ : {mₜ mₜ' mₜ'' : Storeₜ} {e : ASTExp} {v : ℕ} {s : ASTStm}
    → ⟦ e ⟧ₜ mₜ ≡ v
    → v ≢  0  
    → ⟨ s , mₜ ⟩⇓ₜ mₜ'  
    → ⟨ WHILE e s , mₜ' ⟩⇓ₜ mₜ'' 
    → ⟨ WHILE e s , mₜ ⟩⇓ₜ mₜ''
  WhileFₜ : {mₜ : Storeₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ mₜ ≡ 0 
    → ⟨ WHILE e s , mₜ ⟩⇓ₜ mₜ
