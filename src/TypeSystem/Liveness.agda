module TypeSystem.Liveness {n} where

open import Data.Bool.Base
open import Data.Nat
open import Data.Product
  hiding (zip) 
open import Data.Vec.Base
  hiding (replicate ; fromList)

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}
open import TypeSystem.SecurityLabels {n}

-- Set of all active variables of an active set.
-- from𝒜ᵥₛ = from𝒜
from𝒜 : 𝒜 → SetVar
from𝒜 A = fromList (toList (zip (allFin n) A))

-- Expression GEN function from Figure 9.
-- expGen = gen
gen : ASTExp → TyEnv → SetVar
gen (INTVAL _) _ = ∅
gen (VAR v) Γ = (singletonᵥₛ v) ∪ (fvl (findType Γ v))
gen (ADD exp₁ exp₂) Γ = (gen exp₁ Γ) ∪ (gen exp₂ Γ)

-- livenessAux = liveAux
-- livenessIteration = liveness
mutual 
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
  liveness : {t : ℕ} → ℕ → ASTExp → ASTStmId t → TyEnv → 𝒜 → SetVar → Vec SetVar t → SetVar × (Vec SetVar t)
  liveness zero _ _ _ _ nextLiveIn liveOuts = nextLiveIn , liveOuts

  liveness (suc i) e body Γ A nextLiveIn liveOuts = 
    let newLiveIn = (gen e Γ) ∪ nextLiveIn
        bodyLiveIn , liveOuts' = liveAux body Γ A newLiveIn liveOuts
        finalLiveIn = bodyLiveIn ∪ newLiveIn
     in if newLiveIn ⊂ finalLiveIn 
           then liveness i e body Γ A finalLiveIn liveOuts'
           else finalLiveIn , liveOuts'

  -- Calculates the liveIn set of a program by starting at its last statement and working backwards. 
  -- For that, it takes a VariableSet which holds the liveIn of a statement's successors, which corresponds to the liveOut of the statement.
  -- Also, it takes a vector of t VariableSet's, which at the end of the entire liveness analysis
  -- should hold the liveOut of each of the t assignments in the original program. As a side effect of the
  -- liveIn calculation of an assignment, the function updates its corresponding index in the vector.
  liveAux : {t : ℕ} → ASTStmId t → TyEnv → 𝒜 → SetVar → Vec SetVar t → SetVar × (Vec SetVar t)
  liveAux SKIP _ _ nextLiveIn liveOuts = nextLiveIn , liveOuts

  liveAux (ASSIGN v id e) Γ _ nextLiveIn liveOuts = 
    let liveIn = (nextLiveIn diffᵥₛ (singletonᵥₛ v)) ∪ (gen e Γ)
        liveOuts' = liveOuts [ id ]≔ nextLiveIn
     in liveIn , liveOuts'
     
  liveAux (SEQ s₁ s₂) Γ A nextLiveIn liveOuts = 
    let nextLiveIn' , liveOuts' = liveAux s₂ Γ A nextLiveIn liveOuts
     in liveAux s₁ Γ A nextLiveIn' liveOuts'
     
  liveAux (IF e sT sF) Γ A nextLiveIn liveOuts = 
    let liveInT , liveOutsT = liveAux sT Γ A nextLiveIn liveOuts
        liveInF , liveOutsF = liveAux sF Γ A nextLiveIn liveOutsT
     in (liveInT ∪ liveInF) ∪ (gen e Γ) , liveOutsF
     
  liveAux (WHILE e s) Γ A nextLiveIn liveOuts = 
    liveness (fresh A) e s Γ A nextLiveIn liveOuts


replicate : {A : Set}  {m : ℕ} → A → Vec A m
replicate {m = zero}  x = []
replicate {m = suc n} x = x ∷ replicate x


-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → ASTStmId t → 𝒜 → TyEnv → Vec SetVar t
livenessAnalysis {t} s A Γ = 
  proj₂ (liveAux s Γ A (from𝒜 A) (replicate {m = t} ∅))
