module Semantic.Semantic {n} where

open import Data.Fin
open import Data.Nat 
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}
open import Transformation.VariableSet {n}
open import Semantic.Memory {n}
open import Transformation.ActiveSet {n}

-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓_
data ⟨_,_⟩⇓_ : StmS → Storeᵢ → Storeᵢ → Set where
  Skip : {m : Storeᵢ} → ⟨ Skip , m ⟩⇓ m
  Assign : {m : Storeᵢ} {v : Fin n} {e : ExpS} 
    → ⟨ v := e , m ⟩⇓ m [ v  ↦ ⟦ e ⟧ₑ m ]
  AssignBr : {m : Storeᵢ} {v : Fin n} {e : ExpS} 
    → ⟨ ⟦ v := e ⟧ , m ⟩⇓ m [ v  ↦ ⟦ e ⟧ₑ m ]
  Seq : {m m' m'' : Storeᵢ} {s₁ s₂ : StmS}
    → ⟨ s₁ , m ⟩⇓ m'  
    → ⟨ s₂ , m' ⟩⇓ m'' 
    → ⟨ Seq s₁ s₂ , m ⟩⇓ m'' 
  IfT : {m m' : Storeᵢ} {e : ExpS} {v : ℕ} {sT sF : StmS}
    → ⟦ e ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ sT , m ⟩⇓ m' 
    → ⟨ If e sT sF , m ⟩⇓ m'  
  IfF : {m m' : Storeᵢ} {e : ExpS} {sT sF : StmS}
    → ⟦ e ⟧ₑ m ≡ 0 
    → ⟨ sF , m ⟩⇓ m' 
    → ⟨ If e sT sF , m ⟩⇓ m'  
  WhileT : {m m' m'' : Storeᵢ} {e : ExpS} {v : ℕ} {s : StmS}
    → ⟦ e ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ s , m ⟩⇓ m'  
    → ⟨ While e s , m' ⟩⇓ m'' 
    → ⟨ While e s , m ⟩⇓ m''
  WhileF : {m : Storeᵢ} {e : ExpS} {s : StmS}
    → ⟦ e ⟧ₑ m ≡ 0 
    → ⟨ While e s , m ⟩⇓ m

-- Big step semantics of transformed statements.
infixl 5 ⟨_,_⟩⇓ₜ_
data ⟨_,_⟩⇓ₜ_ : Stm → Storeₜ → Storeₜ → Set where
  Skipₜ : {mₜ : Storeₜ} → ⟨ SKIP , mₜ ⟩⇓ₜ mₜ
  Assignₜ : {mₜ : Storeₜ} {v : Vars} {e : Exp} 
    → ⟨ ASSIGN v e , mₜ ⟩⇓ₜ mₜ [ v  ↦ ⟦ e ⟧ₜ mₜ ]ₜ
  Seqₜ : {mₜ mₜ' mₜ'' : Storeₜ} {s₁ s₂ : Stm}
    → ⟨ s₁ , mₜ ⟩⇓ₜ mₜ'  
    → ⟨ s₂ , mₜ' ⟩⇓ₜ mₜ'' 
    → ⟨ SEQ s₁ s₂ , mₜ ⟩⇓ₜ mₜ'' 
  IfTₜ : {mₜ mₜ' : Storeₜ} {e : Exp} {v : ℕ} {sT sF : Stm}
    → ⟦ e ⟧ₜ mₜ ≡ v
    → v ≢  0 
    → ⟨ sT , mₜ ⟩⇓ₜ mₜ' 
    → ⟨ IF e sT sF , mₜ ⟩⇓ₜ mₜ'  
  IfFₜ : {mₜ mₜ' : Storeₜ} {e : Exp} {sT sF : Stm}
    → ⟦ e ⟧ₜ mₜ ≡ 0 
    → ⟨ sF , mₜ ⟩⇓ₜ mₜ' 
    → ⟨ IF e sT sF , mₜ ⟩⇓ₜ mₜ'  
  WhileTₜ : {mₜ mₜ' mₜ'' : Storeₜ} {e : Exp} {v : ℕ} {s : Stm}
    → ⟦ e ⟧ₜ mₜ ≡ v
    → v ≢  0  
    → ⟨ s , mₜ ⟩⇓ₜ mₜ'  
    → ⟨ WHILE e s , mₜ' ⟩⇓ₜ mₜ'' 
    → ⟨ WHILE e s , mₜ ⟩⇓ₜ mₜ''
  WhileFₜ : {mₜ : Storeₜ} {e : Exp} {s : Stm}
    → ⟦ e ⟧ₜ mₜ ≡ 0 
    → ⟨ WHILE e s , mₜ ⟩⇓ₜ mₜ



-- Big step semantics with erase of transformed statements.

erase : Storeₜ → Vars → Storeₜ
erase mₜ x = mₜ

infixl 5 ⟨_,_,_⟩⇓ₑ_
data ⟨_,_,_⟩⇓ₑ_ : Stm → Storeₜ → 𝒜 → Storeₜ  → Set where
  Skipₑ : {mₜ : Storeₜ}{A : 𝒜} → ⟨ SKIP , mₜ , A ⟩⇓ₑ mₜ
  
  Assignₑ : {mₜ : Storeₜ}{x : Vars}{e : Exp}{A : 𝒜} 
    → ⟨ ASSIGN x e , mₜ , A ⟩⇓ₑ (erase (mₜ [ x  ↦ ⟦ e ⟧ₜ mₜ ]ₜ) x)
    
  Seqₑ : {mₜ mₜ' mₜ'' : Storeₜ}{s₁ s₂ : Stm}{A : 𝒜}
    → ⟨ s₁ , mₜ , A ⟩⇓ₑ mₜ'  
    → ⟨ s₂ , mₜ' , A ⟩⇓ₑ mₜ'' 
    → ⟨ SEQ s₁ s₂ , mₜ , A ⟩⇓ₑ mₜ''
    
  IfTₑ : {mₜ mₜ' : Storeₜ} {e : Exp} {v : ℕ} {sT sF : Stm} {A : 𝒜}
    → ⟦ e ⟧ₜ mₜ ≡ v
    → v ≢  0 
    → ⟨ sT , mₜ , A ⟩⇓ₑ mₜ' 
    → ⟨ IF e sT sF , mₜ , A ⟩⇓ₑ mₜ'
    
  IfFₑ : {mₜ mₜ' : Storeₜ} {e : Exp} {sT sF : Stm}{A : 𝒜}
    → ⟦ e ⟧ₜ mₜ ≡ 0 
    → ⟨ sF , mₜ , A ⟩⇓ₑ mₜ' 
    → ⟨ IF e sT sF , mₜ , A ⟩⇓ₑ mₜ'
    
  WhileTₑ : {mₜ mₜ' mₜ'' : Storeₜ} {e : Exp} {v : ℕ} {s : Stm} {A : 𝒜}
    → ⟦ e ⟧ₜ mₜ ≡ v
    → v ≢  0  
    → ⟨ s , mₜ , A ⟩⇓ₑ mₜ'  
    → ⟨ WHILE e s , mₜ' , A ⟩⇓ₑ mₜ'' 
    → ⟨ WHILE e s , mₜ , A ⟩⇓ₑ mₜ''
    
  WhileFₑ : {mₜ : Storeₜ} {e : Exp} {s : Stm}{A : 𝒜}
    → ⟦ e ⟧ₜ mₜ ≡ 0 
    → ⟨ WHILE e s , mₜ , A ⟩⇓ₑ mₜ
