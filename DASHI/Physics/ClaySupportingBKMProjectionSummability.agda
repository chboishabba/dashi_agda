module DASHI.Physics.ClaySupportingBKMProjectionSummability where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; *-mono-≤; *-identityʳ; *-comm; *-assoc; +-mono-≤; m≤n⇒m≤1+n )
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong; cong₂; trans)
open import DASHI.Physics.ClaySupportingShellEnergyBudget using (sum) public
open import DASHI.Physics.ClaySupportingFiniteShellDissipation
  using (sum-mono; sum-*)

----------------------------------------------------------------------
-- §1  N ≥ 1 ⇒ (suc N)² ≥ 1
----------------------------------------------------------------------

sq≥1 : (N : Nat) → 1 ≤ (suc N) * (suc N)
sq≥1 N =
  let
    1≤sN : 1 ≤ suc N
    1≤sN = s≤s z≤n

    sN≤sq : suc N ≤ (suc N) * (suc N)
    sN≤sq = subst (λ z → z ≤ (suc N) * (suc N))
                  (*-identityʳ (suc N))
                  (*-mono-≤ (≤-refl {suc N}) 1≤sN)
  in
  ≤-trans 1≤sN sN≤sq

----------------------------------------------------------------------
-- §2  If a * (suc N)² ≤ C then a ≤ C
----------------------------------------------------------------------

termBound : (a N C : Nat) → a * ((suc N) * (suc N)) ≤ C → a ≤ C
termBound a N C bound =
  let a≤aN² : a ≤ a * ((suc N) * (suc N))
      a≤aN² = subst (λ z → z ≤ a * ((suc N) * (suc N)))
                    (*-identityʳ a)
                    (*-mono-≤ (≤-refl {a}) (sq≥1 N))
  in ≤-trans a≤aN² bound

----------------------------------------------------------------------
-- §3  sum (λ _ → 1) R = R + 1
----------------------------------------------------------------------

sumOne : (R : Nat) → sum (λ _ → 1) R ≡ R + 1
sumOne zero    = refl
sumOne (suc R) = cong (1 +_) (sumOne R)

----------------------------------------------------------------------
-- §4  sum of pointwise equal functions is equal
----------------------------------------------------------------------

sum-cong : (f g : Nat → Nat) (R : Nat) → (∀ N → f N ≡ g N) → sum f R ≡ sum g R
sum-cong f g zero h = h zero
sum-cong f g (suc R) h = cong₂ _+_ (h (suc R)) (sum-cong f g R h)

----------------------------------------------------------------------
-- §5  sum (λ _ → C) R = (R + 1) * C
----------------------------------------------------------------------

sumConst : (C R : Nat) → sum (λ _ → C) R ≡ (R + 1) * C
sumConst C R =
  let
    step0 : sum (λ N → C * 1) R ≡ sum (λ _ → C) R
    step0 = sum-cong (λ N → C * 1) (λ _ → C) R (λ _ → *-identityʳ C)

    step1 : sum (λ N → C * 1) R ≡ C * sum (λ _ → 1) R
    step1 = sum-* C (λ _ → 1) R

    step2 : C * sum (λ _ → 1) R ≡ C * (R + 1)
    step2 = cong (C *_) (sumOne R)

    step3 : C * (R + 1) ≡ (R + 1) * C
    step3 = *-comm C (R + 1)
  in
  trans (sym step0) (trans step1 (trans step2 step3))

----------------------------------------------------------------------
-- §6  Product reordering lemma for residence-form bound
----------------------------------------------------------------------

projectionTermFromResidence :
  (residenceMeasure threshold N C : Nat) →
  residenceMeasure * (threshold * (N * N)) ≤ C →
  (threshold * residenceMeasure) * (N * N) ≤ C
projectionTermFromResidence res th N C hyp =
  let
    -- (th * res) * (N*N) ≡ res * (th * (N*N))
    eq : (th * res) * (N * N) ≡ res * (th * (N * N))
    eq = trans (cong (λ z → z * (N * N)) (*-comm th res))
               (*-assoc res th (N * N))
  in
  subst (λ z → z ≤ C) (sym eq) hyp

----------------------------------------------------------------------
-- §7  Abstract record for N²-weighted summability
----------------------------------------------------------------------

record N2WeightedSummability (a : Nat → Nat) (R C Z₂ : Nat) : Set where
  field
    perShellN2Bound : (N : Nat) → N ≤ R → a (suc N) * ((suc N) * (suc N)) ≤ C
    groundBound     : a 0 ≤ C
    sumBound        : sum a R ≤ Z₂

----------------------------------------------------------------------
-- §8  Helper: pointwise domination from per-shell bounds
----------------------------------------------------------------------

pointwiseFromBounds :
  (a : Nat → Nat) (C : Nat) →
  ((N : Nat) → a (suc N) * ((suc N) * (suc N)) ≤ C) →
  (a 0 ≤ C) → (N : Nat) → a N ≤ C
pointwiseFromBounds a C perShellBound groundBound zero    = groundBound
pointwiseFromBounds a C perShellBound groundBound (suc N) =
  termBound (a (suc N)) N C (perShellBound N)

----------------------------------------------------------------------
-- §9  Concrete construction: each a_N ≤ C, so sum a R ≤ (R+1)*C
----------------------------------------------------------------------

n2WeightedSummabilityFromPerShellBounds :
  (a : Nat → Nat) → (R C : Nat) →
  ((N : Nat) → a (suc N) * ((suc N) * (suc N)) ≤ C) →
  (a 0 ≤ C) →
  N2WeightedSummability a R C ((R + 1) * C)
n2WeightedSummabilityFromPerShellBounds a R C perShellBound groundBound =
  record
    { perShellN2Bound = λ N _ → perShellBound N
    ; groundBound     = groundBound
    ; sumBound        =
        let
          pw : (N : Nat) → a N ≤ (λ _ → C) N
          pw = pointwiseFromBounds a C perShellBound groundBound

          mono : sum a R ≤ sum (λ _ → C) R
          mono = sum-mono a (λ _ → C) R pw

          eq : sum (λ _ → C) R ≡ (R + 1) * C
          eq = sumConst C R
        in
        subst (λ z → sum a R ≤ z) eq mono
    }

----------------------------------------------------------------------
-- §10  BKM budget: product factor and per-term coefficients
----------------------------------------------------------------------

record N2SummabilityBudget : Set where
  field
    productN2 : Nat
    productBound : productN2 ≤ 1
    termN2 : Nat → Nat
    termN2≥1 : (N : Nat) → 1 ≤ termN2 N

----------------------------------------------------------------------
-- §11  a (suc N) ≤ C derived from a(sucN)*((sucN)*(sucN)) ≤ C
----------------------------------------------------------------------

aLeCForSucN : (a C : Nat) (N : Nat) → a * ((suc N) * (suc N)) ≤ C → a ≤ C
aLeCForSucN a C N hyp =
  let a≤aN2 : a ≤ a * ((suc N) * (suc N))
      a≤aN2 = subst (λ z → z ≤ a * ((suc N) * (suc N)))
                    (*-identityʳ a)
                    (*-mono-≤ (≤-refl {a}) (sq≥1 N))
  in ≤-trans a≤aN2 hyp

----------------------------------------------------------------------
-- §11  Finite sum bound for BKM projections
----------------------------------------------------------------------

finiteProjectionSumFromResidence :
  (R : Nat) → (a : Nat → Nat) → (C : Nat) →
  ((N : Nat) → N ≤ R → a N * (N * N) ≤ C) →
  (groundBound : a 0 ≤ C) →
  (budget : N2SummabilityBudget) →
  sum (λ N → a N * (N2SummabilityBudget.productN2 budget)) R ≤
  C * sum (N2SummabilityBudget.termN2 budget) R
----------------------------------------------------------------------
-- §13  Bounded sum-mono: pointwise bound only for N ≤ R
----------------------------------------------------------------------

sum-mono-bounded : (f g : Nat → Nat) (R : Nat) → ((N : Nat) → N ≤ R → f N ≤ g N) → sum f R ≤ sum g R
sum-mono-bounded f g zero h = h zero z≤n
sum-mono-bounded f g (suc R) h =
  +-mono-≤ (h (suc R) (≤-refl {suc R}))
           (sum-mono-bounded f g R (λ N N≤R → h N (m≤n⇒m≤1+n N≤R)))

----------------------------------------------------------------------
-- §14  Finite sum bound for BKM projections
----------------------------------------------------------------------

finiteProjectionSumFromResidence R a C hyp groundBound budget =
  subst (λ z → sum (λ N → a N * pN2) R ≤ z)
        (sum-* C tN2 R)
        (sum-mono-bounded (λ N → a N * pN2) (λ N → C * tN2 N) R pointwise)
  where
    pN2 = N2SummabilityBudget.productN2 budget
    pBnd = N2SummabilityBudget.productBound budget
    tN2 = N2SummabilityBudget.termN2 budget
    tBnd = N2SummabilityBudget.termN2≥1 budget

    pointwise : (N : Nat) → N ≤ R → a N * pN2 ≤ C * tN2 N
    pointwise zero N≤R =
      let h : a 0 * pN2 ≤ C * 1
          h = *-mono-≤ groundBound pBnd
      in ≤-trans h (*-mono-≤ (≤-refl {C}) (tBnd zero))
    pointwise (suc N) N≤R =
      let
        hN2 : a (suc N) * ((suc N) * (suc N)) ≤ C
        hN2 = hyp (suc N) N≤R

        a≤C : a (suc N) ≤ C
        a≤C = aLeCForSucN (a (suc N)) C N hN2

        h : a (suc N) * pN2 ≤ C * 1
        h = *-mono-≤ a≤C pBnd
      in
      ≤-trans h (*-mono-≤ (≤-refl {C}) (tBnd (suc N)))
