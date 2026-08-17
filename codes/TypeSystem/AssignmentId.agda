module TypeSystem.AssignmentId {n} where

open import Data.Fin
  hiding (_≤_ ; _+_ ; _<_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}

-- Counts the number of assignments in a program statement.
assigns : Stm → ℕ
assigns SKIP = 0
assigns (ASSIGN _ _) = 1
assigns (SEQ s₁ s₂) = assigns s₁ + assigns s₂
assigns (IF _ sT sF) = assigns sT + assigns sF
assigns (WHILE _ s) = assigns s

mutual
  -- Function used to cover the IF and SEQ cases of idAss, which are analogous since
  -- both involve identifying all assignments in one statement and then in the other.
  idStmSeq : {t : ℕ} → (s₁ : Stm) → (s₂ : Stm) → (id : ℕ) → 
             id + (assigns s₁ + assigns s₂) ≤ t → StmId t × StmId t
             
  idStmSeq {t} s₁ s₂ id id+[aCs₁+aCs₂]≤t =
    let id+aCs₁+aCs₂-assoc : (id + assigns s₁) + assigns s₂ ≡ id + (assigns s₁ + assigns s₂)
        id+aCs₁+aCs₂-assoc = +-assoc id (assigns s₁) (assigns s₂)
        [id+aCs₁]+aCs₂≤t : (id + assigns s₁) + assigns s₂ ≤ t
        [id+aCs₁]+aCs₂≤t = subst (λ x → x ≤ t) (sym id+aCs₁+aCs₂-assoc) id+[aCs₁+aCs₂]≤t
        id+aCs₁≤t : id + assigns s₁ ≤ t
        id+aCs₁≤t = m+n≤o⇒m≤o (id + assigns s₁) [id+aCs₁]+aCs₂≤t
        s₁Id = idAssAux s₁ id id+aCs₁≤t
        s₂Id = idAssAux s₂ (id + assigns s₁) [id+aCs₁]+aCs₂≤t
     in s₁Id , s₂Id 
  
  -- Auxiliary function to identifyAss. Given a statement s, an integer id and another integer t,
  -- which is the total number of assignments in the program being analysed, this function recursively
  -- traverses s assigning indices of type Fin t to each assignment statement it finds, starting from id
  -- and increasing it by 1 each time.
  idAssAux : {t : ℕ} → (s : Stm) → (id : ℕ) → id + assigns s ≤ t → StmId t
  idAssAux SKIP _ _ = SKIP 
  idAssAux {t} s@(ASSIGN v e) id id+1≤t = 
    let 1+id≤t : assigns s + id ≤ t
        1+id≤t = subst (λ x → x ≤ t) (+-comm id (assigns s)) id+1≤t
    in ASSIGN v (fromℕ< 1+id≤t) e
  idAssAux {t} (SEQ s₁ s₂) id id+aCs≤t =
    let s₁Id , s₂Id = idStmSeq s₁ s₂ id id+aCs≤t
     in SEQ s₁Id s₂Id   
  idAssAux {t} (IF e sT sF) id id+aCs≤t =
    let sTId , sFId = idStmSeq sT sF id id+aCs≤t
    in IF e sTId sFId 
  idAssAux (WHILE e s) id id+aCs≤t =
    WHILE e (idAssAux s id id+aCs≤t)

-- Returns the given program with each assignment having a unique (integer) identifier.
identifyAss : (s : Stm) → StmId (assigns s)
identifyAss s = idAssAux s zero (≤-reflexive refl)
