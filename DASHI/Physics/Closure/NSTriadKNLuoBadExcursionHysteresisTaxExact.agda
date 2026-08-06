module DASHI.Physics.Closure.NSTriadKNLuoBadExcursionHysteresisTaxExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Author: Runlong Yu.
-- Title: "A Structural Audit of Navier-Stokes Obstruction Calculus".
-- DOI: 10.48550/arXiv.2606.25341.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- DASHI CONTRIBUTION
--
-- Round Twenty-One exposed the crossing charge in the bad-excursion theorem.
-- This module identifies the deterministic structure needed to produce such a
-- charge.  Re-entry at a single threshold has no positive crossing cost:
-- arbitrarily many oscillations may occur around that threshold.  A genuine
-- tax requires hysteresis, with lower and upper thresholds separated by a
-- positive gap h.
--
-- Every re-entry then has a positive-variation rise at least h.  If its entry
-- defect is the upper threshold delta, the division-free local estimate is
--
--   h * delta <= delta * rise.
--
-- Finite summation proves
--
--   h * total entry charge
--     <= delta * total positive crossing variation.
--
-- Thus a physical F6 theorem should be formulated with two thresholds and a
-- PDE bound on positive variation.  Merely naming connected components of
-- {A_q > delta} cannot control repeated entry charges.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record HystereticReentry : Set where
  constructor hystereticReentry
  field
    threshold gap positiveRise : ℚ
    thresholdNonnegative : 0ℚ ≤ threshold
    gapNonnegative : 0ℚ ≤ gap
    positiveRiseNonnegative : 0ℚ ≤ positiveRise
    gapPaidByRise : gap ≤ positiveRise

open HystereticReentry public

entryCharge : HystereticReentry → ℚ
entryCharge reentry = threshold reentry

crossingVariationCharge : HystereticReentry → ℚ
crossingVariationCharge reentry =
  threshold reentry * positiveRise reentry

scaledEntryCharge : HystereticReentry → ℚ
scaledEntryCharge reentry = gap reentry * entryCharge reentry

localHysteresisEntryTax :
  ∀ reentry →
  scaledEntryCharge reentry ≤ crossingVariationCharge reentry
localHysteresisEntryTax reentry =
  let
    scaled =
      ℚₚ.*-monoˡ-≤-nonNeg
        (threshold reentry)
        (gapPaidByRise reentry)
      where
      instance
        thresholdNN = nonNegative (thresholdNonnegative reentry)

    leftMeaning :
      threshold reentry * gap reentry
      ≡ scaledEntryCharge reentry
    leftMeaning =
      solve (threshold reentry ∷ gap reentry ∷ [])
  in
  subst
    (λ left → left ≤ crossingVariationCharge reentry)
    leftMeaning
    scaled

record UniformHysteresisFamily : Set where
  constructor uniformHysteresisFamily
  field
    commonThreshold commonGap : ℚ
    commonThresholdNonnegative : 0ℚ ≤ commonThreshold
    commonGapNonnegative : 0ℚ ≤ commonGap
    rises : List ℚ
    everyRisePaysGap :
      ListRiseCertificate commonGap rises

and data ListRiseCertificate (gap : ℚ) : List ℚ → Set where
  noRises : ListRiseCertificate gap []
  nextRise :
    ∀ {rise rises} →
    0ℚ ≤ rise →
    gap ≤ rise →
    ListRiseCertificate gap rises →
    ListRiseCertificate gap (rise ∷ rises)

open UniformHysteresisFamily public

numberWeightedBy : ℚ → List ℚ → ℚ
numberWeightedBy weight [] = 0ℚ
numberWeightedBy weight (_ ∷ rises) =
  weight + numberWeightedBy weight rises

totalRise : List ℚ → ℚ
totalRise [] = 0ℚ
totalRise (rise ∷ rises) = rise + totalRise rises

finiteGapCountBelowRise :
  ∀ gap rises →
  ListRiseCertificate gap rises →
  numberWeightedBy gap rises ≤ totalRise rises
finiteGapCountBelowRise gap [] noRises = ℚₚ.≤-refl
finiteGapCountBelowRise gap (rise ∷ rises)
  (nextRise riseNonnegative gapBelowRise tailCertificate) =
  ℚₚ.+-mono-≤
    gapBelowRise
    (finiteGapCountBelowRise gap rises tailCertificate)

uniformHysteresisEntryTax :
  ∀ family →
  commonGap family
    * numberWeightedBy (commonThreshold family) (rises family)
  ≤
  commonThreshold family * totalRise (rises family)
uniformHysteresisEntryTax family =
  let
    countBound =
      finiteGapCountBelowRise
        (commonGap family)
        (rises family)
        (everyRisePaysGap family)

    leftCount =
      numberWeightedBy (commonGap family) (rises family)

    leftCountNonnegative : 0ℚ ≤ leftCount
    leftCountNonnegative =
      let
        prove : ∀ rises → 0ℚ ≤ numberWeightedBy (commonGap family) rises
        prove [] = ℚₚ.≤-refl
        prove (_ ∷ tail) =
          L2.addNonnegative
            (commonGapNonnegative family)
            (prove tail)
      in
      prove (rises family)

    totalRiseNonnegative : 0ℚ ≤ totalRise (rises family)
    totalRiseNonnegative =
      let
        prove :
          ∀ rises →
          ListRiseCertificate (commonGap family) rises →
          0ℚ ≤ totalRise rises
        prove [] noRises = ℚₚ.≤-refl
        prove (rise ∷ tail)
          (nextRise riseNN gapBelow tailCertificate) =
          L2.addNonnegative riseNN (prove tail tailCertificate)
      in
      prove (rises family) (everyRisePaysGap family)

    multiplied =
      L2.nonnegativeProductMonotone
        (commonThresholdNonnegative family)
        leftCountNonnegative
        (commonThresholdNonnegative family)
        totalRiseNonnegative
        ℚₚ.≤-refl
        countBound

    leftMeaning :
      commonThreshold family * leftCount
      ≡
      commonGap family
        * numberWeightedBy (commonThreshold family) (rises family)
    leftMeaning =
      let
        count : ℚ
        count = numberWeightedBy 1 (rises family)

        thresholdCount :
          numberWeightedBy (commonThreshold family) (rises family)
          ≡ commonThreshold family * count
        thresholdCount = weightedCountFactor (commonThreshold family) (rises family)

        gapCount :
          numberWeightedBy (commonGap family) (rises family)
          ≡ commonGap family * count
        gapCount = weightedCountFactor (commonGap family) (rises family)
      in
      subst
        (λ thresholdWeighted →
          commonThreshold family * leftCount
          ≡ commonGap family * thresholdWeighted)
        (sym thresholdCount)
        (subst
          (λ gapWeighted →
            commonThreshold family * gapWeighted
            ≡ commonGap family * (commonThreshold family * count))
          (sym gapCount)
          (solve
            ( commonThreshold family
            ∷ commonGap family
            ∷ count
            ∷ [])))
  in
  subst
    (λ left → left ≤ commonThreshold family * totalRise (rises family))
    leftMeaning
    multiplied
  where
  weightedCountFactor :
    ∀ weight rises →
    numberWeightedBy weight rises
    ≡ weight * numberWeightedBy 1 rises
  weightedCountFactor weight [] = solve (weight ∷ [])
  weightedCountFactor weight (_ ∷ tail)
    rewrite weightedCountFactor weight tail =
    solve (weight ∷ numberWeightedBy 1 tail ∷ [])

zeroGapPaysNothing :
  ∀ threshold rise →
  0ℚ * threshold ≡ 0ℚ * rise
zeroGapPaysNothing threshold rise = solve (threshold ∷ rise ∷ [])

record HysteresisAuthorityBoundary : Set where
  constructor hysteresisAuthorityBoundary
  field
    localPositiveVariationTaxProved : Set
    finiteReentryTaxProved : Set
    zeroGapObstructionExposed : Set
    navierStokesPositiveVariationBoundProduced : Set
    scaleUniformThresholdCapProduced : Set

canonicalHysteresisAuthorityBoundary : HysteresisAuthorityBoundary
canonicalHysteresisAuthorityBoundary =
  hysteresisAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
