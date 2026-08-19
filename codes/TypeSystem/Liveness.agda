open import TypeSystem.SecurityTypes
open import Data.Nat

module TypeSystem.Liveness {c ℓ₁ ℓ₂}
                      -- environment dimension
                      {n : ℕ}
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂)  where

open import Data.Bool.Base
  hiding (_<_)
open import Data.Nat
open import Data.Product
  hiding (zip) 
open import Data.Vec.Base
  hiding (fromList ; length ; foldr)
open import Data.List
  hiding (zip ; allFin ; replicate ; lookup)
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}
open import TypeSystem.SecurityLabels {n = n} FChDBL
open import Relation.Binary.PropositionalEquality 
open import Induction.WellFounded
open import Data.Empty
open import Data.Product
  hiding (zip)
open import Relation.Binary
open import Induction.WellFounded
open import Relation.Nullary
open import Data.Nat.Properties
 


-- Set of all active variables of an active set.

from𝒜 : 𝒜 → SetVar
from𝒜 A = fromList (toList (zip (allFin n) A))

-- Expression GEN function from Figure 9.
-- expGen = gen
gen : Exp → TyEnv → SetVar
gen (INTVAL _) _ = ∅
gen (VAR v) Γ = (singletonᵥₛ v) ∪ (fvl (findType Γ v))
gen (ADD exp₁ exp₂) Γ = (gen exp₁ Γ) ∪ (gen exp₂ Γ)


fromGen : Exp → TyEnv → SetVar → Set
fromGen e Γ set = all (λ v → v ∈ set) (gen e Γ) ≡ true


-- ver si dejar

data _≼_ : SetVar → SetVar → Set where
  nil : ∀ {xs} → [] ≼ xs
  in₁  : ∀ {x xs ys} → xs ≼ ys → (x ∷ xs) ≼ (x ∷ ys)
  in₂  : ∀ {x xs ys} → xs ≼ ys → xs ≼ (x ∷ ys)


_≋_ : SetVar → SetVar → Set
A ≋ B = A ≼ B × B ≼ A

_≺_ : SetVar → SetVar → Set 
A ≺ B = A ≼ B × ¬ (B ≼ A)       

postulate is≼? : ∀ x y → Dec (x ≼ y)


is≺? : ∀ x y → Dec (x ≺ y)
is≺? x y with is≼? x y
... | no ¬x=y = no λ { (x=y , _) → ¬x=y x=y }
... | yes x=y with is≼? y x
...   | yes q = no λ { (_ , ¬q) → ¬q q }
...   | no ¬q = yes (x=y , ¬q)

postulate trans-≺ : {A B C : SetVar} → A ≺ B → B ≺ C → A ≺ C  


postulate A≺B∪A : {A B : SetVar} → A ≺ (B ∪ A)


postulate x≺[] : {x : SetVar} → x ≺ [] → ⊥  


---------nueva relación : cantidad de elementos que pueden agregarse a liveIn

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m


♯ : 𝒜 → SetVar → ℕ
♯ A [] = 0
♯ A xs = foldr (λ (i , x) y → y + ((lookup A i) - x)) 0 xs  

postulate decr : {xs ys : SetVar} {A : 𝒜} → xs ≺ ys → ♯ A ys < ♯ A xs   


------ Use in the well-founded definition

-- relation used to probe termination of liveness analysis
least  : 𝒜 → SetVar →  SetVar  → Set
least A xs ys =  ♯ A xs < ♯ A ys


-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).

-- buscar <-wellFounded
postulate wfNat : ∀ n → Acc _<_ n


go : ∀ A xs → Acc _<_ (♯ A xs) → Acc (least A) xs
go A x (acc rs) = acc λ y y<x → go A y (rs (♯ A y) y<x)


wfSetVar : ∀ {A : 𝒜} → (xs : SetVar) → Acc (least A) xs   
wfSetVar {A} xs = go A xs (wfNat (♯ A xs)) 
  

  -- Uses an iterative method to calculate the liveIn set of a WHILE statement.
  -- It starts by taking the liveIn set of the statement following the WHILE block (nextLiveIn) 
  -- and joins it with the GEN set of the while condition. The result will be used as the liveIn 
  -- passed to the liveness analysis of the loop's body. Said analysis returns the liveIn set for the body. 
  -- Then, if that result is a subset of the liveIn set passed as an argument, then we have finished 
  -- iterating and have a final result. Otherwise, we take the union between those two sets and use that 
  -- as the nextLiveIn for a new iteration of the function.
  -- This process is guaranteed to finish because nextLiveIn can only grow in size between iterations
  -- and the total number of possible variables is set for the program so there is an upper bound to
  -- the resulting set size.

--  Acc _⊏_ finalLiveIn
mutual
-- version of liveAux that uses induction on well-founded relation
  liveAuxWF : {t : ℕ} → Exp → StmId t → TyEnv → (A : 𝒜)
            → (liveIn : SetVar)
            → Vec SetVar t
            → Acc (least A) liveIn
            → SetVar × Vec SetVar t
  liveAuxWF {t} e body Γ A liveIn liveOuts (acc rs) with is≺? ((gen e Γ) ∪ liveIn) ((proj₁ (liveness body Γ A ((gen e Γ) ∪ liveIn) liveOuts)) ∪ ((gen e Γ) ∪ liveIn)) 
  ... | yes li'≺fi =
   liveAuxWF e body Γ A finalLiveIn liveOuts' (rs finalLiveIn (decr li≺fi)) 
    where  liveIn' = (gen e Γ) ∪ liveIn
           finalLiveIn = (proj₁ (liveness body Γ A liveIn' liveOuts)) ∪ liveIn'
           liveOuts' = proj₂ (liveness body Γ A liveIn' liveOuts)
           li≺li' :  liveIn ≺ liveIn'
           li≺li' = A≺B∪A {liveIn} {gen e Γ} 
           li≺fi : liveIn ≺ finalLiveIn 
           li≺fi = trans-≺ li≺li' li'≺fi               
 
  ... | no ¬p = finalLiveIn , liveOuts' 
    where  liveIn' = (gen e Γ) ∪ liveIn
           finalLiveIn = (proj₁ (liveness body Γ A liveIn' liveOuts)) ∪ liveIn'
           liveOuts' = proj₂ (liveness body Γ A liveIn' liveOuts) 
                                             

  -- Calculates the liveIn set of a program by starting at its last statement and working backwards. 
  -- For that, it takes a VariableSet which holds the liveIn of a statement's successors, which corresponds to the liveOut of the statement.
  -- Also, it takes a vector of t VariableSet's, which at the end of the entire liveness analysis
  -- should hold the liveOut of each of the t assignments in the original program. As a side effect of the
  -- liveIn calculation of an assignment, the function updates its corresponding index in the vector.
  liveness : {t : ℕ} → StmId t → TyEnv → 𝒜 → SetVar → Vec SetVar t → SetVar × (Vec SetVar t)
  liveness SKIP _ _ liveIn liveOuts = liveIn , liveOuts

  liveness (ASSIGN v id e) Γ _ liveIn liveOuts = 
    let liveIn' = (liveIn diffᵥₛ (singletonᵥₛ v)) ∪ (gen e Γ)
        liveOuts' = liveOuts [ id ]≔ liveIn
     in liveIn' , liveOuts'
     
  liveness (SEQ s₁ s₂) Γ A liveIn liveOuts = 
    let liveIn' , liveOuts' = liveness s₂ Γ A liveIn liveOuts
     in liveness s₁ Γ A liveIn' liveOuts'
     
  liveness (IF e sT sF) Γ A liveIn liveOuts = 
    let liveInT , liveOutsT = liveness sT Γ A liveIn liveOuts
        liveInF , liveOutsF = liveness sF Γ A liveIn liveOutsT
     in (liveInT ∪ liveInF) ∪ (gen e Γ) , liveOutsF
     
  liveness (WHILE e s) Γ A liveIn liveOuts = 
    liveAuxWF e s Γ A liveIn liveOuts (wfSetVar liveIn)  



-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → StmId t → 𝒜 → TyEnv → Vec SetVar t
livenessAnalysis {t} s A Γ = 
  proj₂ (liveness s Γ A (from𝒜 A) (replicate {n = t} ∅))

