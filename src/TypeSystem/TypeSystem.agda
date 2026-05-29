module TypeSystem.TypeSystem {n} where

open import Data.Bool.Base
open import Data.Bool.Properties
  hiding (≤-reflexive)
open import Data.Fin
  hiding (_≟_)
open import Data.List
  hiding (lookup ; replicate)
open import Data.Maybe.Base
open import Data.Nat
  hiding (_≟_)
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

-- Proof obligations created by the type system's assignment rules.
-- ProofObligation = ProofOs
record ProofOs : Set where
  constructor ⊨_⇒_⊑_
  field
    premise : Pred
    subtype : SLabel
    supertype : SLabel

--------------- Solver

-- given a predicate return a list of true expresions and a list of false expressions
evalPremise : Pred → List ASTExp × List ASTExp 
evalPremise True = [] , [] 

evalPremise (ExpZero e) = [] , [ e ]

evalPremise (ExpNonZero e) = [ e ] , []

evalPremise (And e₁ e₂) = let xs , ys = evalPremise e₁
                              zs , ws = evalPremise e₂
                          in xs ++ zs , ys ++ ws    

-- 
solve : ProofOs → Bool
solve (⊨ True ⇒ l₁ ⊑ l₂) =  is⊑ l₁ l₂

solve (⊨ ExpZero e ⇒ l₁ ⊑ l₂) = solve (⊨ True ⇒ (replaceFalse l₁ [ e ]) ⊑ (replaceFalse l₂ [ e ]))   

solve (⊨ ExpNonZero e ⇒ l₁ ⊑ l₂) = solve (⊨ True ⇒ (replaceTrue l₁ [ e ]) ⊑ (replaceTrue l₂ [ e ]))

solve (⊨ And p₁ p₂  ⇒ l₁ ⊑ l₂) =  let ts , fs = evalPremise (And p₁ p₂)
                                   in solve (⊨ True ⇒ (replaceFalse (replaceTrue l₁ ts) fs)  ⊑ (replaceFalse (replaceTrue l₂ ts) fs))


-- Typing rules for expressions from Figure 10.
data _⊦_-_ : TyEnv → ASTExp → SLabel → Set where
  CONST : {Γ : TyEnv} {n : ℕ} 
    → Γ ⊦ INTVAL n - Level Low
  VAR : {Γ : TyEnv} {v : Vars}
    → Γ ⊦ VAR v - findType Γ v
  OP : {Γ : TyEnv} {exp₁ exp₂ : ASTExp} {τ₁ τ₂ : SLabel}
    → Γ ⊦ exp₁ - τ₁
    → Γ ⊦ exp₂ - τ₂
    → Γ ⊦ ADD exp₁ exp₂ - Join τ₁ τ₂


-- Property that a given variable does not belong to the security types
-- of any variable in a given set.
-- variableNotInFreeSets = v∉s
v∉s : Vars → TyEnv → SetVar → Set
v∉s var Γ set = 
  any (λ v → var ∈ (fvl (findType Γ v))) set ≡ false


-- Typing rules for statements from Figure 11.
data _,_⊦_[_,_]-_ : {t : ℕ} → TyEnv → SLabel → ASTStmId t → Vec Pred t → Vec SetVar t → List ProofOs → Set where

  SKIP : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {P : Vec Pred t} {L : Vec SetVar t} 
    → Γ , pc ⊦ SKIP [ P , L ]- []

  ASSIGN : {t : ℕ} {Γ : TyEnv} {pc τ : SLabel} {v : Vars} {id : Fin t} {exp : ASTExp} {P : Vec Pred t} {L : Vec SetVar t}
    → Γ ⊦ exp - τ
    → v∉s v Γ (lookup L id) 
    → Γ , pc ⊦ ASSIGN v id exp [ P , L ]- [ ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ v ]

  SEQ : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {s₁ s₂ : ASTStmId t} {P : Vec Pred t} {L : Vec SetVar t} {proofs₁ proofs₂ : List ProofOs}
    → Γ , pc ⊦ s₁ [ P , L ]- proofs₁
    → Γ , pc ⊦ s₂ [ P , L ]- proofs₂
    → Γ , pc ⊦ SEQ s₁ s₂ [ P , L ]- (proofs₁ ++ proofs₂)
    
  IF : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {τ : SLabel} {cond : ASTExp} {sT sF : ASTStmId t} {P : Vec Pred t} {L : Vec SetVar t} {proofsT proofsF : List ProofOs}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ sT [ P , L ]- proofsT
    → Γ , (Join τ pc) ⊦ sF [ P , L ]- proofsF
    → Γ , pc ⊦ IF cond sT sF [ P , L ]- (proofsT ++ proofsF)

  WHILE : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {τ : SLabel} {cond : ASTExp} {s : ASTStmId t} {P : Vec Pred t} {L : Vec SetVar t} {proofs : List ProofOs}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ s [ P , L ]- proofs
    → Γ , pc ⊦ WHILE cond s [ P , L ]- proofs

-- Returns a type proof for the given expression.   
typeExp : (Γ : TyEnv) (exp : ASTExp) → Σ[ τ ∈ SLabel ] (Γ ⊦ exp - τ)
typeExp Γ (INTVAL _) = Level Low , CONST
typeExp Γ (VAR v) = findType Γ v , VAR
typeExp Γ (ADD e₁ e₂) = 
  let τ₁ , proof₁ = typeExp Γ e₁
      τ₂ , proof₂ = typeExp Γ e₂
   in Join τ₁ τ₂ , OP proof₁ proof₂


-- Returns a type proof for the given statement, if possible.
typeStm : {t : ℕ} (Γ : TyEnv) (pc : SLabel) (s : ASTStmId t) (P : Vec Pred t) (L : Vec SetVar t)
  → Maybe (Σ[ proofs ∈ List ProofOs ] (Γ , pc ⊦ s [ P , L ]- proofs))
typeStm _ _ SKIP _ _ = just ([] , SKIP)  

typeStm Γ pc (ASSIGN x id e) P L 
  with (any (λ v → x ∈ (fvl (findType Γ v))) (lookup L id)) ≟ false
...          | yes x∉fvΓv = 
                let τ , eType = typeExp Γ e
                    proofOs = ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ x 
                 in just ([ proofOs ] , ASSIGN eType x∉fvΓv)
...         | no _ = nothing

typeStm Γ pc (SEQ s₁ s₂) P L = 
  typeStm Γ pc s₁ P L >>=
  λ (proofs₁ , s₁Type) → typeStm Γ pc s₂ P L >>=
  λ (proofs₂ , s₂Type) → just (proofs₁ ++ proofs₂ , SEQ s₁Type s₂Type)
  
typeStm Γ pc (IF e sT sF) P L = 
  let τ , eType = typeExp Γ e
   in typeStm Γ (Join τ pc) sT P L >>=
      λ (proofsT , sTType) → typeStm Γ (Join τ pc) sF P L >>=
      λ (proofsF , sFType) → just (proofsT ++ proofsF , IF eType sTType sFType)
      
typeStm Γ pc (WHILE e s) P L = 
  let τ , eType = typeExp Γ e
   in typeStm Γ (Join τ pc) s P L >>=
      λ (proofs , sType) → just (proofs , WHILE eType sType)

-- Type containing all the components necessary for determining the security type of a program,
-- as well as the proof for the typing result.
record TypingProof : Set where
  field
    typeEnv : TyEnv
    pc : SLabel
    t : ℕ
    stmId : ASTStmId t
    predicates : Vec Pred t
    liveSets : Vec SetVar t
    proofObligations : List ProofOs
    proof : typeEnv , pc ⊦ stmId [ predicates , liveSets ]- proofObligations

-- Takes a bracketed program and a typing environment and returns the typing proof for it
-- after it is transformed to its non-bracketed version, if possible.
typeProgram : ASTStmS → TyEnv → Maybe TypingProof
typeProgram stm Γ = 
  let stmTrans , A = transform stm
      stmId = identifyAss stmTrans
      predicates = generatePred stmId
      liveSets = livenessAnalysis stmId A Γ
   in typeStm Γ (Level Low) stmId predicates liveSets >>=
      λ (proofs , stmType) → just record {typeEnv = Γ; 
                                           pc = Level Low; 
                                           stmId = stmId; 
                                           predicates = predicates; 
                                           liveSets = liveSets; 
                                           proofObligations = proofs; 
                                           proof = stmType
                                         }



isTyped : ASTStmS → TyEnv → Bool 
isTyped stm Γ =
  let stmTrans , A = transform stm
      stmId = identifyAss stmTrans
      predicates = generatePred stmId
      liveSets = livenessAnalysis stmId A Γ
   in maybe (λ (proofs , _) → all solve proofs) false (typeStm Γ (Level Low) stmId predicates liveSets) 
      
