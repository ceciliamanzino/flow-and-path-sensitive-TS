open import TypeSystem.SecurityTypes
open import Data.Nat

module TypeSystem.SecurityLabels {c ℓ₁ ℓ₂}
                      -- environment dimension
                      {n : ℕ}
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂)  where

open import Data.List.Base
  hiding (lookup)
open import Data.Product
open import Data.Vec.Base
  hiding (_++_ ; [_])
open import Data.Bool
  hiding (_∧_ ; _∨_)
open import Transformation.AST {n}
open import Transformation.VariableSet {n}
open import Relation.Nullary

open FinChnDecBoundedLattice FChDBL 
  renaming (Carrier to 𝕊; _≲?_ to _is≲_ ; ⊥ to Low ; ⊤ to High )


-- τ ::= l | e ? τ1 : τ2 | τ1 t τ2 | τ1 u τ2
data SLabel : Set c where
    Level : 𝕊 → SLabel
    CondExp : Exp → SLabel → SLabel → SLabel
    Meet : SLabel → SLabel → SLabel
    Join : SLabel → SLabel → SLabel


-- return the higher the security label in all the cases of the condition
higher : SLabel → 𝕊
higher (Level l) = l
higher (CondExp e l l₁) = (higher l) ∨ (higher l₁)
higher (Meet l l₁) =  (higher l) ∧ (higher l₁)
higher (Join l l₁) =  (higher l) ∨ (higher l₁)


-- return the lower the security label in all the cases of the condition
lower : SLabel → 𝕊
lower (Level l) = l 
lower (CondExp e l l₁) = (lower l) ∧ (lower l₁)
lower (Meet l l₁) = (lower l) ∨ (lower l₁)
lower (Join l l₁) = (lower l) ∨ (lower l₁)



-- given two labels l1 and l2 return the true
-- if the highest value that can have l1 is lower to the lowest value that can have l2
is⊑ : SLabel → SLabel → Bool
is⊑ l₁ l₂ with (higher l₁) is≲ (lower l₂) 
... | yes p = true
... | no p = false


elem : Exp → List Exp → Bool
elem e xs = any (λ x → e ==ₑ x) xs 

-- given a label l and a list of expressions that represent true expression,
-- eliminate the conditionals in l (choicing the true branch) that has as condition an expression of the
-- list

elimTrue : SLabel → List Exp → SLabel 
elimTrue (Level x) _ = Level x
elimTrue (CondExp e l l₁) xs = if (any (λ x → e ==ₑ x) xs) then elimTrue l xs
                               else CondExp e (elimTrue l xs) (elimTrue l₁ xs)
elimTrue (Meet l l₁) xs = Meet (elimTrue l xs) (elimTrue l₁ xs)
elimTrue (Join l l₁) xs = Join (elimTrue l xs) (elimTrue l₁ xs)

-- given a label l and a list of expressions, replace in l
-- any ocurrence of the expressions of the list to False


elimFalse : SLabel → List Exp → SLabel 
elimFalse (Level st) _ = Level st
elimFalse (CondExp e l l₁) xs = if (any (λ x → e ==ₑ x) xs) then elimFalse l₁ xs
                                else CondExp e (elimFalse l xs) (elimFalse l₁ xs)
elimFalse (Meet l l₁) xs = Meet (elimFalse l xs) (elimFalse l₁ xs)
elimFalse (Join l l₁) xs = Join (elimFalse l xs) (elimFalse l₁ xs)



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

