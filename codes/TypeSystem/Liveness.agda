open import TypeSystem.SecurityTypes
open import Data.Nat

module TypeSystem.Liveness {c ℓ₁ ℓ₂}
                      -- environment dimension
                      {n : ℕ}
                      -- lattice of security types
                      (FChDBL : FinChnDecBoundedLattice c ℓ₁ ℓ₂)  where

open import Data.Bool.Base
  hiding (_<_ ; _≤_ )
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
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin
  renaming (_≟_ to _==_)
  hiding (_≺_ ; _-_ ; _>_ ; _≤_ ; _<_ ; _+_)
open import Data.Nat.Induction
   using (<-wellFounded)  

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

--------- Inclution between variable sets
data _≼_ : SetVar → SetVar → Set where
  nil : ∀ {xs} → [] ≼ xs
  in₁  : ∀ {x xs ys} → xs ≼ ys → (x ∷ xs) ≼ (x ∷ ys)
  in₂  : ∀ {x xs ys} → xs ≼ ys → xs ≼ (x ∷ ys)

_≺_ : SetVar → SetVar → Set 
A ≺ B = A ≼ B × ¬ (B ≼ A)       

-----------------------------------------
--- Preperties of ≺ and ≼ --------------

refl-≼ : {A : SetVar} → A ≼ A
refl-≼ {[]} = nil
refl-≼ {x ∷ xs} = in₁ refl-≼  

trans-≼ : {A B C : SetVar} → A ≼ B → B ≼ C → A ≼ C  
trans-≼ nil q = nil
trans-≼ (in₁ p) (in₁ q) =  in₁ (trans-≼ p q)
trans-≼ (in₁ xs≼ys₁) (in₂ x:ys₁≼ys) = in₂ (trans-≼ (in₁ xs≼ys₁) x:ys₁≼ys) 
trans-≼ (in₂ p) (in₁ q) = in₂ (trans-≼ p q)
trans-≼ (in₂ xs≼ys₁) (in₂ x:ys₁≼ys) = in₂ (trans-≼ xs≼ys₁ (trans-≼ (in₂ refl-≼ ) x:ys₁≼ys))  


postulate antisym-≼ : ∀ {xs ys} → xs ≼ ys → ys ≼ xs → xs ≡ ys

prop : ∀ {x xs ys} → (x ∷ xs) ≼ (x ∷ ys) → xs ≼ ys
prop (in₁ xs≼ys) = xs≼ys
prop (in₂ x:xs≼ys) = trans-≼ (in₂ refl-≼) x:xs≼ys  

prop₂ :  ∀ {x y xs ys} → ¬ (x ≡ y) → (x ∷ xs) ≼ (y ∷ ys) → (x ∷ xs) ≼ ys
prop₂ {x} {.x}  ¬x≡y (in₁ p) = ⊥-elim (¬x≡y refl) 
prop₂ ¬x≡y (in₂ p) = p

is=? : ∀ (x y : Vars) → Dec (x ≡ y)
is=? (i , x) (j , y) with x ≟ y
... | no x≠y = no λ r → x≠y (cong proj₂ r)  
... | yes x=y with i == j 
...  | yes i=j = yes (cong₂ _,_ i=j x=y) 
...  | no i≠j  = no λ r → i≠j (cong proj₁ r) 

is≼? : ∀ x y → Dec (x ≼ y)
is≼? [] ys = yes nil
is≼? (x ∷ xs) [] = no λ () 
is≼? (x ∷ xs) (y ∷ ys) with is=? x y
is≼? (x ∷ xs) (y ∷ ys) | yes refl with is≼? xs ys
...   | yes xs≼ys = yes (in₁ xs≼ys)
...   | no ¬xs≼ys = no (λ q → ¬xs≼ys (prop q))  
is≼? (x ∷ xs) (y ∷ ys) | no x≠y with is≼? (x ∷ xs) ys
...   | yes p = yes (in₂ p) 
...   | no ¬p = no (λ q → ¬p (prop₂ x≠y q))


is≺? : ∀ x y → Dec (x ≺ y)
is≺? x y with is≼? x y
... | no ¬x=y = no λ { (x=y , _) → ¬x=y x=y }
... | yes x=y with is≼? y x
...   | yes q = no λ { (_ , ¬q) → ¬q q }
...   | no ¬q = yes (x=y , ¬q)

trans-≺ : {xs ys zs : SetVar} → xs ≺ ys → ys ≺ zs → xs ≺ zs  
trans-≺ (xs≼ys , ¬ys≼xs) (ys≼zs , ¬zs≼ys) = ( trans-≼ xs≼ys ys≼zs , λ zs≼xs → ¬zs≼ys (trans-≼ zs≼xs xs≼ys))

trans-≺₂ : {xs ys zs : SetVar} → xs ≼ ys → ys ≺ zs → xs ≺ zs  
trans-≺₂ xs≼ys (ys≼zs , ¬zs≼ys) =  ( trans-≼ xs≼ys ys≼zs , λ zs≼xs → ¬zs≼ys (trans-≼ zs≼xs xs≼ys) )

postulate x≼y∪x : {xs ys : SetVar} → xs ≼ (ys ∪ xs)

x≺[] : {x : SetVar} → x ≺ [] → ⊥
x≺[] (x≼[] , ¬[]≼x) = ¬[]≼x nil


≼∨≺ : {xs ys : SetVar} →  (xs ≼ ys) → (xs ≺ ys) ⊎ (xs ≡ ys)  
≼∨≺ {xs} {ys} xs≼ys with is≼? ys xs
... | no ¬ys≼xs = inj₁ (xs≼ys , ¬ys≼xs)
... | yes ys≼xs = inj₂ (antisym-≼ xs≼ys ys≼xs)

-------------------------------------------------------------------------
-- definitions over naturals

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

suc-pred : {x : ℕ} → x > 0 → suc (x - 1) ≡ x
suc-pred {zero} ()
suc-pred {suc x} _ = refl


-- bounded function
♯ : 𝒜 → SetVar → ℕ
♯ A [] = suc n  
♯ A ((i , z) ∷ xs) = ♯ A xs - 1  


postulate n+1+m-1≡n+m : ∀ n m → (suc n) + m - 1 ≡ n + m
postulate n-1<m+n : ∀ {n m} →  n - 1 < m + n


lemma-suma : {A : 𝒜} {xs : SetVar} →
            length xs + ♯ A xs ≡ suc n
lemma-suma {A} {[]} = refl
lemma-suma {A} {(i , z) ∷ xs} =
 let xs+#Axs≡1+n : length xs + ♯ A xs ≡ suc n
     xs+#Axs≡1+n = lemma-suma {A} {xs}
     p : suc (length (xs)) + (♯ A xs) - 1 ≡ suc n
     p = trans (n+1+m-1≡n+m (length (xs)) (♯ A xs)) xs+#Axs≡1+n  
 in p


x≡x+0 : ∀ {x} → x ≡ x + 0
x≡x+0 {zero} = refl
x≡x+0 {suc x} = cong suc (x≡x+0 {x})

trivial : ∀ {x y z} → y ≡ 0 → x + y ≡ z → x ≡ z
trivial refl x+y≡z = trans x≡x+0 x+y≡z

suc-n≰n : ∀ n → ¬ (suc n ≤ n)
suc-n≰n zero    ()
suc-n≰n (suc n) (s≤s p) = suc-n≰n n p


lema-len : {A : 𝒜}{xs : SetVar} → length xs ≤ n  → ♯ A xs > 0
lema-len {A} {xs} xs≤n with (♯ A xs) | inspect (♯ A) xs
... | zero | [ eq ] = let xs≡n+1 : length xs ≡ suc n
                          xs≡n+1 = trivial {length xs} {♯ A xs} {suc n} eq (lemma-suma {A} {xs})
                          suc≤n : suc n ≤ n
                          suc≤n = subst (λ k → k ≤ n) xs≡n+1 xs≤n 
                      in ⊥-elim (suc-n≰n n suc≤n) 

... | suc k | [ eq ] =   s≤s z≤n 

minus-1< : {x : ℕ} → x > 0 → x - 1 < x
minus-1< {suc x} x>0 = ≤-refl 

lema-1 : {A : 𝒜} {x : Vars} {xs : SetVar} → length xs ≤ n  → ♯ A (x ∷ xs) < ♯ A xs
lema-1 {A} {x} {xs} ♯xs≤n = minus-1< (lema-len {A} {xs} ♯xs≤n)  

suc<→<  : {x y : ℕ} → suc x < suc y → x < y 
suc<→< (s≤s p) = p

x<y→x-1<y-1 : {x y : ℕ} → x > 0 → x < y → x - 1 < y - 1
x<y→x-1<y-1 {zero} {suc y} () x<y
x<y→x-1<y-1 {suc x} {suc y} x>0 sx<sy = suc<→<  sx<sy


lema-2 : {A : 𝒜} {x : Vars} {xs : SetVar} → ♯ A (x ∷ xs) < suc n 
lema-2 {A} {x} {xs} = subst (λ k → ♯ A (x ∷ xs) < k) (lemma-suma {A} {xs}) (n-1<m+n {♯ A xs} {length xs})  


postulate length-xs≤n : {xs : SetVar} → length xs ≤ n


-- the bounded function is decreasing
decr : {xs ys : SetVar} {A : 𝒜} → xs ≺ ys → ♯ A ys < ♯ A xs   
decr {.[]} {[]} {A} (nil , ¬ys≼[]) = ⊥-elim (¬ys≼[] nil)
decr {.[]} {y ∷ ys} {A} (nil , ¬y∷ys≼[]) =  lema-2 {A} {y} {ys}

decr {x ∷ xs} {y ∷ ys} {A} (in₁ xs≼ys , ¬x∷xs≼y∷ys) = 
   let p : ♯ A ys < ♯ A xs
       p = decr {xs} {ys} {A} (xs≼ys , λ q → ¬x∷xs≼y∷ys (in₁ q))
   in x<y→x-1<y-1 {♯ A ys} {♯ A xs} (lema-len {A} {xs = ys}  (length-xs≤n {ys})) p   

decr {xs} {y ∷ ys} {A} (in₂ xs≼ys , ¬y∷ys≼xs) with ≼∨≺ xs≼ys
... | inj₁ xs≺ys = 
  let p : ♯ A (y ∷ ys) < ♯ A ys
      p = lema-1 {A} {y} {ys} (length-xs≤n {ys}) 
      q : ♯ A ys < ♯ A xs
      q = decr {xs} {ys} {A} xs≺ys 
  in  <-trans p q
... | inj₂ refl = let n=m : suc (♯ A xs - 1) ≡ ♯ A xs
                      n=m = suc-pred (lema-len {A} {xs = xs} (length-xs≤n {xs = xs}))   
                  in subst (λ z → suc (♯ A xs - 1) ≤ z) n=m ≤-refl 


-- relation used to probe termination of liveness analysis
least  : 𝒜 → SetVar →  SetVar  → Set
least A xs ys =  ♯ A xs < ♯ A ys


-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).

-- buscar <-wellFounded
wfNat : ∀ n → Acc _<_ n
wfNat = <-wellFounded
---- we probe well-founded of least using well founded of _<_
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
   liveAuxWF e body Γ A finalLiveIn liveOuts' (rs finalLiveIn (decr {A = A} li≺fi)) 
    where  liveIn' = (gen e Γ) ∪ liveIn
           finalLiveIn = (proj₁ (liveness body Γ A liveIn' liveOuts)) ∪ liveIn'
           liveOuts' = proj₂ (liveness body Γ A liveIn' liveOuts)
           li≼li' :  liveIn ≼ liveIn'
           li≼li' = x≼y∪x {liveIn} {gen e Γ} 
           li≺fi : liveIn ≺ finalLiveIn 
           li≺fi = trans-≺₂ li≼li' li'≺fi               
 
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
    liveAuxWF e s Γ A liveIn liveOuts (wfSetVar {A = A} liveIn)  



-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → StmId t → 𝒜 → TyEnv → Vec SetVar t
livenessAnalysis {t} s A Γ = 
  proj₂ (liveness s Γ A (from𝒜 A) (replicate {n = t} ∅))

