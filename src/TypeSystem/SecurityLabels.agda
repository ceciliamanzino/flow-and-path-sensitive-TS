module TypeSystem.SecurityLabels {n} where

open import Data.List.Base
  hiding (lookup)
open import Data.Nat
  hiding (_⊔_ ; _⊓_)
open import Data.Product
open import Data.Vec.Base
  hiding (_++_ ; [_])
open import Data.Bool

open import Transformation.AST {n}
open import Transformation.VariableSet {n}

-- SecL = SecurityLevel
data SecL : Set where
    Low : SecL
    High : SecL

_⊔_ : SecL → SecL → SecL
Low ⊔ ℓ = ℓ
High ⊔ ℓ = High

_⊓_ : SecL → SecL → SecL
Low ⊓ ℓ = Low
High ⊓ ℓ = ℓ


--
data _≲_ : SecL → SecL → Set where
     low≲ : { ℓ : SecL} → Low ≲ ℓ
     h≲h : { ℓ : SecL} → ℓ ≲ High
     

is≲ : SecL → SecL → Bool
is≲ Low st = true
is≲ High Low = false
is≲ High High = true

-- τ ::= l | e ? τ1 : τ2 | τ1 t τ2 | τ1 u τ2
-- SLabel = SecurityLabel
-- ExpTest = Cond
data SLabel : Set where
    Level : SecL → SLabel
    CondExp : ASTExp → SLabel → SLabel → SLabel
    Meet : SLabel → SLabel → SLabel
    Join : SLabel → SLabel → SLabel

-- return the higher the security label in all the cases of the condition
higher : SLabel → SecL
higher (Level Low) = Low
higher (Level High) = High
higher (CondExp e l l₁) = higher l ⊔ higher l₁
higher (Meet l l₁) = higher l ⊓ higher l₁
higher (Join l l₁) = higher l ⊔ higher l₁

-- return the lower the security label in all the cases of the condition
lower : SLabel → SecL
lower (Level Low) = Low
lower (Level High) = High
lower (CondExp e l l₁) = lower l ⊓ lower l₁
lower (Meet l l₁) = lower l ⊓ lower l₁
lower (Join l l₁) = lower l ⊔ lower l₁

--
is⊑ : SLabel → SLabel → Bool
is⊑ l₁ l₂ = is≲ (higher l₁) (lower l₂)


elem : ASTExp → List ASTExp → Bool
elem x [] = true
elem x (x₁ ∷ xs) = if x ==ₑ x₁ then true else elem x xs


-- given a label l and a list of expressions, replace in l
-- any ocurrence of the expressions of the list to True

replaceTrue : SLabel → List ASTExp → SLabel 
replaceTrue (Level x) xs = Level x
replaceTrue (CondExp x l l₁) xs = if (elem x xs) then replaceTrue l xs
                                  else CondExp x (replaceTrue l xs) (replaceTrue l₁ xs)
replaceTrue (Meet l l₁) xs = Meet (replaceTrue l xs) (replaceTrue l₁ xs)
replaceTrue (Join l l₁) xs = Join (replaceTrue l xs) (replaceTrue l₁ xs)

-- given a label l and a list of expressions, replace in l
-- any ocurrence of the expressions of the list to False

replaceFalse : SLabel → List ASTExp → SLabel 
replaceFalse (Level st) xs = Level st
replaceFalse (CondExp x l l₁) xs = if (elem x xs) then replaceFalse l₁ xs
                                  else CondExp x (replaceFalse l xs) (replaceFalse l₁ xs)
replaceFalse (Meet l l₁) xs = Meet (replaceFalse l xs) (replaceFalse l₁ xs)
replaceFalse (Join l l₁) xs = Join (replaceFalse l xs) (replaceFalse l₁ xs)


-- Returns all the free variables of a security label.
--labelVariables = fvl
fvl : SLabel → SetVar
fvl (Level _) =  ∅
fvl (CondExp exp l₁ l₂) =  ((fv exp) ∪ (fvl l₁)) ∪ (fvl l₂)
fvl (Meet l₁ l₂) = (fvl l₁) ∪ (fvl l₂)
fvl (Join l₁ l₂) = (fvl l₁) ∪ (fvl l₂)

-- A TypingEnvironment is a mapping from Vars to security labels.
TyEnv : Set _
TyEnv = Vec (List SLabel) n 

lookupLabel : List SLabel → ℕ → SLabel
lookupLabel [] _ = Level Low
lookupLabel (x ∷ xs) zero = x
lookupLabel (x ∷ xs) (suc n) = lookupLabel xs n

findType : TyEnv → Vars → SLabel
findType Γ (v , i) = lookupLabel (lookup Γ v) i
