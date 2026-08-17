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
  hiding (fromList ; length)
open import Data.List
  hiding (zip ; allFin ; replicate)
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}
open import TypeSystem.SecurityLabels {n = n} FChDBL
open import Relation.Binary.PropositionalEquality 
open import Induction.WellFounded

-- open FinChnDecBoundedLattice FChDBL 
--  renaming (Carrier to 𝕊; _≲?_ to _is≲_ ; ⊥ to Low ; ⊤ to High)

-- Set of all active variables of an active set.
-- from𝒜ᵥₛ = from𝒜
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

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded


------ Use in the well-founded definition
-- orden relation: Set X is “smaller” than Y if it has fewer elements
_⊏_ : {A : Set} → List A → List A → Set
X ⊏ Y = length X < length Y
  

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
mutual  
  liveAux : {t : ℕ} → ℕ → Exp → StmId t → TyEnv → 𝒜 → SetVar → Vec SetVar t → SetVar × (Vec SetVar t)
  liveAux zero _ _ _ _ liveIn liveOuts = liveIn , liveOuts

  liveAux (suc i) e body Γ A liveIn liveOuts = 
    let liveIn' = (gen e Γ) ∪ liveIn
        bodyLiveIn , liveOuts' = liveness body Γ A liveIn' liveOuts
        finalLiveIn = bodyLiveIn ∪ liveIn'
      in if liveIn' ⊂ finalLiveIn 
           then liveAux i e body Γ A finalLiveIn liveOuts'
           else finalLiveIn , liveOuts'

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
    liveAux (fresh A) e s Γ A liveIn liveOuts



-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → StmId t → 𝒜 → TyEnv → Vec SetVar t
livenessAnalysis {t} s A Γ = 
  proj₂ (liveness s Γ A (from𝒜 A) (replicate {n = t} ∅))

