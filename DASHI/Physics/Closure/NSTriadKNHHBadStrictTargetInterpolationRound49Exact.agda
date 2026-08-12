module DASHI.Physics.Closure.NSTriadKNHHBadStrictTargetInterpolationRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Eliminate the conceptual division by (1-alpha).  Given
--
--   0 <= alpha < 1,
--   0 <= C0 < T,
--   beta < (1-alpha) T,
--
-- define the two positive raw slacks
--
--   s0 = T-C0,
--   sf = (1-alpha)T-beta,
--
-- and choose s=min(s0,sf).  Since 0 < 1-alpha <= 1,
--
--   C0 <= T-s,
--   beta <= (1-alpha)(T-s),
--   s>0.
--
-- Therefore M=T-s is a valid recurrence ceiling and M<T, with no quotient by
-- 1-alpha, no radicals, and no optimization theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

minQ : ℚ → ℚ → ℚ
minQ a b with a ≤? b
... | yes _ = a
... | no _ = b

minQBelowLeft : ∀ a b → minQ a b ≤ a
minQBelowLeft a b with a ≤? b
... | yes _ = ℚP.≤-refl
... | no notAB with ℚP.≤-total a b
...   | inj₁ a≤b = ⊥-elim (notAB a≤b)
...   | inj₂ b≤a = b≤a

minQBelowRight : ∀ a b → minQ a b ≤ b
minQBelowRight a b with a ≤? b
... | yes a≤b = a≤b
... | no _ = ℚP.≤-refl

minQPositive : ∀ {a b} → 0ℚ < a → 0ℚ < b → 0ℚ < minQ a b
minQPositive {a} {b} aPos bPos with a ≤? b
... | yes _ = aPos
... | no _ = bPos

record StrictHHBadTarget : Set where
  field
    base alpha beta target : ℚ
    baseNonnegative : 0ℚ ≤ base
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ
    baseStrict : base < target
    forcingStrict : beta < (1ℚ - alpha) * target

open StrictHHBadTarget public

baseSlack forcingSlack commonSlack : StrictHHBadTarget → ℚ
baseSlack data = target data - base data
forcingSlack data = (1ℚ - alpha data) * target data - beta data
commonSlack data = minQ (baseSlack data) (forcingSlack data)

baseSlackPositive : (data : StrictHHBadTarget) → 0ℚ < baseSlack data
baseSlackPositive data =
  let
    shifted = ℚP.+-monoʳ-< (- base data) (baseStrict data)
    leftMeaning : base data + (- base data) ≡ 0ℚ
    leftMeaning = solve (base data ∷ [])
    rightMeaning : target data + (- base data) ≡ baseSlack data
    rightMeaning = solve (target data ∷ base data ∷ [])
  in subst₂ _<_ leftMeaning rightMeaning shifted

forcingSlackPositive : (data : StrictHHBadTarget) → 0ℚ < forcingSlack data
forcingSlackPositive data =
  let
    shifted = ℚP.+-monoʳ-< (- beta data) (forcingStrict data)
    leftMeaning : beta data + (- beta data) ≡ 0ℚ
    leftMeaning = solve (beta data ∷ [])
    rightMeaning :
      (1ℚ - alpha data) * target data + (- beta data)
      ≡ forcingSlack data
    rightMeaning = solve (alpha data ∷ target data ∷ beta data ∷ [])
  in subst₂ _<_ leftMeaning rightMeaning shifted

commonSlackPositive : (data : StrictHHBadTarget) → 0ℚ < commonSlack data
commonSlackPositive data =
  minQPositive (baseSlackPositive data) (forcingSlackPositive data)

gapNonnegative : (data : StrictHHBadTarget) → 0ℚ ≤ 1ℚ - alpha data
gapNonnegative data = ℚP.<⇒≤ (gapPositive data)
  where
  gapPositive : 0ℚ < 1ℚ - alpha data
  gapPositive =
    let
      shifted = ℚP.+-monoʳ-< (- alpha data) (alphaStrict data)
      leftMeaning : alpha data + (- alpha data) ≡ 0ℚ
      leftMeaning = solve (alpha data ∷ [])
      rightMeaning : 1ℚ + (- alpha data) ≡ 1ℚ - alpha data
      rightMeaning = solve (alpha data ∷ [])
    in subst₂ _<_ leftMeaning rightMeaning shifted

gapBelowOne : (data : StrictHHBadTarget) → 1ℚ - alpha data ≤ 1ℚ
gapBelowOne data =
  let
    shifted = ℚP.+-monoʳ-≤ (1ℚ - alpha data) (alphaNonnegative data)
    leftMeaning : 0ℚ + (1ℚ - alpha data) ≡ 1ℚ - alpha data
    leftMeaning = solve (alpha data ∷ [])
    rightMeaning : alpha data + (1ℚ - alpha data) ≡ 1ℚ
    rightMeaning = solve (alpha data ∷ [])
  in subst₂ _≤_ leftMeaning rightMeaning shifted

derivedCeiling : StrictHHBadTarget → ℚ
derivedCeiling data = target data - commonSlack data

derivedCeilingStrict : (data : StrictHHBadTarget) → derivedCeiling data < target data
derivedCeilingStrict data =
  let
    shifted = ℚP.+-monoʳ-< (derivedCeiling data) (commonSlackPositive data)
    leftMeaning : 0ℚ + derivedCeiling data ≡ derivedCeiling data
    leftMeaning = solve (target data ∷ commonSlack data ∷ [])
    rightMeaning : commonSlack data + derivedCeiling data ≡ target data
    rightMeaning = solve (target data ∷ commonSlack data ∷ [])
  in subst₂ _<_ leftMeaning rightMeaning shifted

baseBelowDerivedCeiling : (data : StrictHHBadTarget) →
  base data ≤ derivedCeiling data
baseBelowDerivedCeiling data =
  let
    marginBelow = minQBelowLeft (baseSlack data) (forcingSlack data)
    summed : base data + commonSlack data ≤ base data + baseSlack data
    summed = ℚP.+-mono-≤ ℚP.≤-refl marginBelow
    toTarget : base data + commonSlack data ≤ target data
    toTarget = subst
      (λ upper → base data + commonSlack data ≤ upper)
      (solve (target data ∷ base data ∷ []))
      summed
    shifted :
      base data + commonSlack data
      ≤ derivedCeiling data + commonSlack data
    shifted = subst
      (λ upper → base data + commonSlack data ≤ upper)
      (sym (solve (target data ∷ commonSlack data ∷ [])))
      toTarget
  in ℚP.+-cancelʳ-≤ (commonSlack data) shifted

derivedCeilingNonnegative : (data : StrictHHBadTarget) →
  0ℚ ≤ derivedCeiling data
derivedCeilingNonnegative data =
  ℚP.≤-trans (baseNonnegative data) (baseBelowDerivedCeiling data)

forcingBelowDerivedCeiling : (data : StrictHHBadTarget) →
  beta data ≤ (1ℚ - alpha data) * derivedCeiling data
forcingBelowDerivedCeiling data =
  let
    gap = 1ℚ - alpha data
    marginNN = ℚP.<⇒≤ (commonSlackPositive data)

    gapTimesMarginBelowMargin :
      gap * commonSlack data ≤ 1ℚ * commonSlack data
    gapTimesMarginBelowMargin =
      L2.nonnegativeProductMonotone
        (gapNonnegative data)
        marginNN
        ℚP.0≤1
        marginNN
        (gapBelowOne data)
        ℚP.≤-refl

    marginBelowForcingSlack : commonSlack data ≤ forcingSlack data
    marginBelowForcingSlack =
      minQBelowRight (baseSlack data) (forcingSlack data)

    gapMarginBelowSlack : gap * commonSlack data ≤ forcingSlack data
    gapMarginBelowSlack =
      ℚP.≤-trans
        (subst
          (λ upper → gap * commonSlack data ≤ upper)
          (ℚP.*-identityˡ (commonSlack data))
          gapTimesMarginBelowMargin)
        marginBelowForcingSlack

    addBeta :
      beta data + gap * commonSlack data
      ≤ beta data + forcingSlack data
    addBeta = ℚP.+-mono-≤ ℚP.≤-refl gapMarginBelowSlack

    toGapTarget : beta data + gap * commonSlack data ≤ gap * target data
    toGapTarget = subst
      (λ upper → beta data + gap * commonSlack data ≤ upper)
      (solve (alpha data ∷ target data ∷ beta data ∷ []))
      addBeta

    targetMeaning :
      gap * derivedCeiling data + gap * commonSlack data
      ≡ gap * target data
    targetMeaning = solve (gap ∷ target data ∷ commonSlack data ∷ [])

    shifted :
      beta data + gap * commonSlack data
      ≤ gap * derivedCeiling data + gap * commonSlack data
    shifted = subst
      (λ upper → beta data + gap * commonSlack data ≤ upper)
      (sym targetMeaning)
      toGapTarget
  in ℚP.+-cancelʳ-≤ (gap * commonSlack data) shifted

strictTargetsInterpolateWithoutDivision : Bool
strictTargetsInterpolateWithoutDivision = true

strictTargetsInterpolateWithoutDivisionIsTrue :
  strictTargetsInterpolateWithoutDivision ≡ true
strictTargetsInterpolateWithoutDivisionIsTrue = refl
