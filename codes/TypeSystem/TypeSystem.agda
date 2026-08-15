open import TypeSystem.SecurityTypes
open import Data.Nat
   hiding (_≟_)
module TypeSystem.TypeSystem {c ℓ₁ ℓ₂}
                      -- environment dimension
                      {n : ℕ}
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂) where

open import Data.Bool.Base
open import Data.Bool.Properties
  hiding (≤-reflexive)
open import Data.Fin
  hiding (_≟_)
open import Data.List
  hiding (lookup ; replicate)
open import Data.Maybe.Base
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
open import TypeSystem.Liveness {n = n} FChDBL
open import TypeSystem.Predicates {n}
open import TypeSystem.SecurityLabels {n = n} FChDBL

open FinChnDecBoundedLattice FChDBL 
  renaming (Carrier to 𝕊; _≲?_ to _is≲_ ; ⊥ to Low ; ⊤ to High ; _≟_ to _==𝕊_)


-- Proof obligations created by the type system's assignment rules.
-- ProofObligation = ProofOs
record ProofOs : Set c where
  constructor ⊨_⇒_⊑_
  field
    premise : Pred
    subtype : SLabel
    supertype : SLabel

--------------- Solver

-- given a predicate return a list of true expresions and a list of false expressions
evalP : Pred → List Exp × List Exp 
evalP True = [] , [] 
evalP (ExpZ e) = [] , [ e ]
evalP (ExpNonZ e) = [ e ] , []
evalP (And e₁ e₂) = let xs , ys = evalP e₁
                        zs , ws = evalP e₂
                    in xs ++ zs , ys ++ ws    

-- solver for proofObligations
solve : ProofOs → Bool
solve (⊨ True ⇒ l₁ ⊑ l₂) =  is⊑ l₁ l₂

solve (⊨ ExpZ e ⇒ l₁ ⊑ l₂) = solve (⊨ True ⇒ (elimFalse l₁ [ e ]) ⊑ (elimFalse l₂ [ e ]))   

solve (⊨ ExpNonZ e ⇒ l₁ ⊑ l₂) = solve (⊨ True ⇒ (elimTrue l₁ [ e ]) ⊑ (elimTrue l₂ [ e ]))

solve (⊨ And p₁ p₂  ⇒ l₁ ⊑ l₂) =  let ts , fs = evalP (And p₁ p₂)
                                   in solve (⊨ True ⇒ (elimFalse (elimTrue l₁ ts) fs)  ⊑ (elimFalse (elimTrue l₂ ts) fs))


-- Typing rules for expressions from Figure 10.
data _⊦_-_ : TyEnv → Exp → SLabel → Set where
  CONST : {Γ : TyEnv} {n : ℕ} 
    → Γ ⊦ INTVAL n - Level Low
  VAR : {Γ : TyEnv} {v : Vars}
    → Γ ⊦ VAR v - findType Γ v
  OP : {Γ : TyEnv} {exp₁ exp₂ : Exp} {τ₁ τ₂ : SLabel}
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
data _,_⊦_[_,_]-_ : {t : ℕ} → TyEnv → SLabel → StmId t → Vec Pred t → Vec SetVar t → List ProofOs → Set c where

  SKIP : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {P : Vec Pred t} {L : Vec SetVar t} 
    → Γ , pc ⊦ SKIP [ P , L ]- []

  ASSIGN : {t : ℕ} {Γ : TyEnv} {pc τ : SLabel} {v : Vars} {id : Fin t} {exp : Exp} {P : Vec Pred t} {L : Vec SetVar t}
    → Γ ⊦ exp - τ
    → v∉s v Γ (lookup L id) 
    → Γ , pc ⊦ ASSIGN v id exp [ P , L ]- [ ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ v ]

  SEQ : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {s₁ s₂ : StmId t} {P : Vec Pred t} {L : Vec SetVar t} {proofs₁ proofs₂ : List ProofOs}
    → Γ , pc ⊦ s₁ [ P , L ]- proofs₁
    → Γ , pc ⊦ s₂ [ P , L ]- proofs₂
    → Γ , pc ⊦ SEQ s₁ s₂ [ P , L ]- (proofs₁ ++ proofs₂)
    
  IF : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {τ : SLabel} {cond : Exp} {sT sF : StmId t} {P : Vec Pred t} {L : Vec SetVar t} {proofsT proofsF : List ProofOs}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ sT [ P , L ]- proofsT
    → Γ , (Join τ pc) ⊦ sF [ P , L ]- proofsF
    → Γ , pc ⊦ IF cond sT sF [ P , L ]- (proofsT ++ proofsF)

  WHILE : {t : ℕ} {Γ : TyEnv} {pc : SLabel} {τ : SLabel} {cond : Exp} {s : StmId t} {P : Vec Pred t} {L : Vec SetVar t} {proofs : List ProofOs}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ s [ P , L ]- proofs
    → Γ , pc ⊦ WHILE cond s [ P , L ]- proofs

-- Returns a type proof for the given expression.   
typeExp : (Γ : TyEnv) (exp : Exp) → Σ[ τ ∈ SLabel ] (Γ ⊦ exp - τ)
typeExp Γ (INTVAL _) = Level Low , CONST
typeExp Γ (VAR v) = findType Γ v , VAR
typeExp Γ (ADD e₁ e₂) = 
  let τ₁ , proof₁ = typeExp Γ e₁
      τ₂ , proof₂ = typeExp Γ e₂
   in Join τ₁ τ₂ , OP proof₁ proof₂


-- Returns a type proof for the given statement, if possible.
typeStm : {t : ℕ} (Γ : TyEnv) (pc : SLabel) (s : StmId t) (P : Vec Pred t) (L : Vec SetVar t)
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
record TypingProof : Set c where
  field
    typeEnv : TyEnv
    pc : SLabel
    t : ℕ
    stmId : StmId t
    predicates : Vec Pred t
    liveSets : Vec SetVar t
    proofObligations : List ProofOs
    proof : typeEnv , pc ⊦ stmId [ predicates , liveSets ]- proofObligations

-- Takes a bracketed program and a typing environment and returns the typing proof for it
-- after it is transformed to its non-bracketed version, if possible.
typeProgram : StmS → TyEnv → Maybe TypingProof
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

--------------------------------------------------------
-- Returns a type proof for the given expression.   
typeE : (Γ : TyEnv) (exp : Exp) → SLabel 
typeE Γ (INTVAL _) = Level Low 
typeE Γ (VAR v) = findType Γ v 
typeE Γ (ADD e₁ e₂) = Join (typeE Γ e₁) (typeE Γ e₂)



typeS : {t : ℕ} (s : StmId t) (Γ : TyEnv) (pc : SLabel) (P : Vec Pred t) (L : Vec SetVar t)
        → Maybe (List ProofOs)  
typeS SKIP _ _ _ _ = just []   

typeS (ASSIGN x id e) Γ pc P L 
  with (any (λ v → x ∈ (fvl (findType Γ v))) (lookup L id)) ≟ false
...          | yes x∉fvΓv = 
                let τ = typeE Γ e
                in just [ ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ x ] 
...         | no _ = nothing

typeS (SEQ s₁ s₂) Γ pc P L = typeS s₁ Γ pc P L >>=
                            λ proof₁ → typeS s₂ Γ pc P L >>=
                            λ proof₂  → just (proof₁ ++ proof₂) 
  
typeS (IF e sT sF) Γ pc P L =  let τ  = typeE Γ e
                               in typeS sT Γ (Join τ pc) P L >>=
                                  λ proofT → typeS sF Γ (Join τ pc) P L >>=
                                  λ proofF → just (proofT ++ proofF) 
      
typeS (WHILE e s) Γ pc P L =  let τ = typeE Γ e
                              in typeS s Γ (Join τ pc) P L >>=
                                   λ proof → just proof 



isTyped : StmS → TyEnv → Bool 
isTyped stm Γ =
  let stmT , A = transform stm
      stmId = identifyAss stmT
      predicates = generatePred stmId
      liveSets = livenessAnalysis stmId A Γ
   in maybe (λ proofs → all solve proofs) false
     (typeS stmId Γ (Level Low) predicates liveSets) 
      
