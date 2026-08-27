module DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / INTERVAL REFERENCE
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- The previous Brillouin-box carrier hard-coded
--
--      lower = numeratorLower / denominatorUpper
--      upper = numeratorUpper / denominatorLower
--
-- for a strictly positive denominator interval.  Those endpoints are correct
-- only when the numerator interval is nonnegative.  Division by a positive
-- interval is monotone in the numerator but changes monotonicity in the
-- denominator with the SIGN of the numerator.
--
-- This file now does more than choose the correct endpoints.  Over exact
-- rationals it proves the full pointwise enclosure theorem for all three sign
-- cases:
--
--   nL >= 0:       [ nL/dU , nU/dL ]
--   nU <= 0:       [ nL/dL , nU/dU ]
--   nL <= 0 <= nU: [ nL/dL , nU/dL ].
--
-- Rational quotient notation is implemented explicitly as multiplication by
-- the positive reciprocal.  This avoids confusing Agda's rational constructor
-- `_/_` with division of two rationals and makes every nonzero denominator
-- obligation visible to the kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; 1/_; Positive; NonNegative; NonPositive; NonZero)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong; subst; subst₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data NumeratorSignCase (lower upper : ℚ) : Set where
  numeratorNonnegative : 0ℚ ≤ lower → NumeratorSignCase lower upper
  numeratorNonpositive : upper ≤ 0ℚ → NumeratorSignCase lower upper
  numeratorStraddlesZero :
    lower ≤ 0ℚ → 0ℚ ≤ upper → NumeratorSignCase lower upper

positiveReciprocal : (denominator : ℚ) → 0ℚ < denominator → ℚ
positiveReciprocal denominator denominatorPositive =
  let
    instance
      positiveDenominator : Positive denominator
      positiveDenominator = ℚ.positive denominatorPositive

      nonzeroDenominator : NonZero denominator
      nonzeroDenominator = ℚP.pos⇒nonZero denominator
  in
  1/ denominator

dividePositive : (numerator denominator : ℚ) → 0ℚ < denominator → ℚ
dividePositive numerator denominator denominatorPositive =
  numerator * positiveReciprocal denominator denominatorPositive

positiveReciprocalRightInverse :
  ∀ denominator (denominatorPositive : 0ℚ < denominator) →
  denominator * positiveReciprocal denominator denominatorPositive ≡ 1ℚ
positiveReciprocalRightInverse denominator denominatorPositive =
  let
    instance
      positiveDenominator : Positive denominator
      positiveDenominator = ℚ.positive denominatorPositive

      nonzeroDenominator : NonZero denominator
      nonzeroDenominator = ℚP.pos⇒nonZero denominator
  in
  ℚP.*-inverseʳ denominator

positiveReciprocalPositive :
  ∀ denominator (denominatorPositive : 0ℚ < denominator) →
  0ℚ < positiveReciprocal denominator denominatorPositive
positiveReciprocalPositive denominator denominatorPositive =
  let
    instance
      positiveDenominator : Positive denominator
      positiveDenominator = ℚ.positive denominatorPositive

      nonzeroDenominator : NonZero denominator
      nonzeroDenominator = ℚP.pos⇒nonZero denominator

      reciprocalPositive : Positive (1/ denominator)
      reciprocalPositive = ℚP.1/pos⇒pos denominator
  in
  ℚP.positive⁻¹ (1/ denominator)

positiveReciprocalNonnegative :
  ∀ denominator (denominatorPositive : 0ℚ < denominator) →
  NonNegative (positiveReciprocal denominator denominatorPositive)
positiveReciprocalNonnegative denominator denominatorPositive =
  ℚ.nonNegative
    (ℚP.<⇒≤ (positiveReciprocalPositive denominator denominatorPositive))

upperDenominatorPositive :
  ∀ lower upper → 0ℚ < lower → lower ≤ upper → 0ℚ < upper
upperDenominatorPositive lower upper lowerPositive lowerBelowUpper =
  ℚP.<-≤-trans lowerPositive lowerBelowUpper

reciprocalAntitonePositive :
  ∀ lower upper
    (lowerPositive : 0ℚ < lower)
    (upperPositive : 0ℚ < upper) →
  lower ≤ upper →
  positiveReciprocal upper upperPositive
  ≤ positiveReciprocal lower lowerPositive
reciprocalAntitonePositive lower upper lowerPositive upperPositive lowerBelowUpper =
  let
    lowerInverse = positiveReciprocal lower lowerPositive
    upperInverse = positiveReciprocal upper upperPositive
    scale = lower * upper

    instance
      lowerIsPositive : Positive lower
      lowerIsPositive = ℚ.positive lowerPositive

      upperIsPositive : Positive upper
      upperIsPositive = ℚ.positive upperPositive

      scaleIsPositive : Positive scale
      scaleIsPositive = ℚP.pos*pos⇒pos lower upper

    scaleUpperInverse : scale * upperInverse ≡ lower
    scaleUpperInverse =
      trans
        (ℚP.*-assoc lower upper upperInverse)
        (trans
          (cong (lower *_) (positiveReciprocalRightInverse upper upperPositive))
          (ℚP.*-identityʳ lower))

    scaleLowerInverse : scale * lowerInverse ≡ upper
    scaleLowerInverse =
      trans
        (cong (_* lowerInverse) (ℚP.*-comm lower upper))
        (trans
          (ℚP.*-assoc upper lower lowerInverse)
          (trans
            (cong (upper *_) (positiveReciprocalRightInverse lower lowerPositive))
            (ℚP.*-identityʳ upper)))

    scaled : scale * upperInverse ≤ scale * lowerInverse
    scaled = subst₂ _≤_
      (sym scaleUpperInverse)
      (sym scaleLowerInverse)
      lowerBelowUpper
  in
  ℚP.*-cancelˡ-≤-pos scale scaled

dividePositiveNumeratorMonotone :
  ∀ lower upper denominator
    (denominatorPositive : 0ℚ < denominator) →
  lower ≤ upper →
  dividePositive lower denominator denominatorPositive
  ≤ dividePositive upper denominator denominatorPositive
dividePositiveNumeratorMonotone lower upper denominator denominatorPositive lowerBelowUpper =
  let
    reciprocal = positiveReciprocal denominator denominatorPositive
    instance
      reciprocalNonnegative : NonNegative reciprocal
      reciprocalNonnegative =
        positiveReciprocalNonnegative denominator denominatorPositive
  in
  ℚP.*-monoʳ-≤-nonNeg reciprocal lowerBelowUpper

dividePositiveDenominatorAntitoneNonnegative :
  ∀ numerator lowerDenominator upperDenominator
    (numeratorAtLeastZero : 0ℚ ≤ numerator)
    (lowerPositive : 0ℚ < lowerDenominator)
    (upperPositive : 0ℚ < upperDenominator) →
  lowerDenominator ≤ upperDenominator →
  dividePositive numerator upperDenominator upperPositive
  ≤ dividePositive numerator lowerDenominator lowerPositive
dividePositiveDenominatorAntitoneNonnegative numerator lowerDenominator upperDenominator
    numeratorAtLeastZero lowerPositive upperPositive lowerBelowUpper =
  let
    instance
      numeratorIsNonnegative : NonNegative numerator
      numeratorIsNonnegative = ℚ.nonNegative numeratorAtLeastZero
  in
  ℚP.*-monoˡ-≤-nonNeg numerator
    (reciprocalAntitonePositive
      lowerDenominator upperDenominator
      lowerPositive upperPositive lowerBelowUpper)

dividePositiveDenominatorMonotoneNonpositive :
  ∀ numerator lowerDenominator upperDenominator
    (numeratorAtMostZero : numerator ≤ 0ℚ)
    (lowerPositive : 0ℚ < lowerDenominator)
    (upperPositive : 0ℚ < upperDenominator) →
  lowerDenominator ≤ upperDenominator →
  dividePositive numerator lowerDenominator lowerPositive
  ≤ dividePositive numerator upperDenominator upperPositive
dividePositiveDenominatorMonotoneNonpositive numerator lowerDenominator upperDenominator
    numeratorAtMostZero lowerPositive upperPositive lowerBelowUpper =
  let
    instance
      numeratorIsNonpositive : NonPositive numerator
      numeratorIsNonpositive = ℚ.nonPositive numeratorAtMostZero
  in
  ℚP.*-monoˡ-≤-nonPos numerator
    (reciprocalAntitonePositive
      lowerDenominator upperDenominator
      lowerPositive upperPositive lowerBelowUpper)

quotientLowerEndpoint :
  ∀ {numeratorLower numeratorUpper} →
  NumeratorSignCase numeratorLower numeratorUpper →
  (denominatorLower denominatorUpper : ℚ) →
  (denominatorLowerPositive : 0ℚ < denominatorLower) →
  denominatorLower ≤ denominatorUpper → ℚ
quotientLowerEndpoint {numeratorLower} {numeratorUpper} signCase
    denominatorLower denominatorUpper denominatorLowerPositive denominatorOrdered
  with signCase
... | numeratorNonnegative _ =
  dividePositive numeratorLower denominatorUpper
    (upperDenominatorPositive
      denominatorLower denominatorUpper denominatorLowerPositive denominatorOrdered)
... | numeratorNonpositive _ =
  dividePositive numeratorLower denominatorLower denominatorLowerPositive
... | numeratorStraddlesZero _ _ =
  dividePositive numeratorLower denominatorLower denominatorLowerPositive

quotientUpperEndpoint :
  ∀ {numeratorLower numeratorUpper} →
  NumeratorSignCase numeratorLower numeratorUpper →
  (denominatorLower denominatorUpper : ℚ) →
  (denominatorLowerPositive : 0ℚ < denominatorLower) →
  denominatorLower ≤ denominatorUpper → ℚ
quotientUpperEndpoint {numeratorLower} {numeratorUpper} signCase
    denominatorLower denominatorUpper denominatorLowerPositive denominatorOrdered
  with signCase
... | numeratorNonnegative _ =
  dividePositive numeratorUpper denominatorLower denominatorLowerPositive
... | numeratorNonpositive _ =
  dividePositive numeratorUpper denominatorUpper
    (upperDenominatorPositive
      denominatorLower denominatorUpper denominatorLowerPositive denominatorOrdered)
... | numeratorStraddlesZero _ _ =
  dividePositive numeratorUpper denominatorLower denominatorLowerPositive

record LiesBetween (lower value upper : ℚ) : Set where
  constructor liesBetween
  field
    lowerSound : lower ≤ value
    upperSound : value ≤ upper
open LiesBetween public

positiveDenominatorQuotientEnclosure :
  ∀ {numeratorLower numeratorUpper numerator
      denominatorLower denominatorUpper denominator}
    (signCase : NumeratorSignCase numeratorLower numeratorUpper)
    (denominatorLowerPositive : 0ℚ < denominatorLower)
    (denominatorOrdered : denominatorLower ≤ denominatorUpper)
    (numeratorLowerSound : numeratorLower ≤ numerator)
    (numeratorUpperSound : numerator ≤ numeratorUpper)
    (denominatorLowerSound : denominatorLower ≤ denominator)
    (denominatorUpperSound : denominator ≤ denominatorUpper) →
  LiesBetween
    (quotientLowerEndpoint signCase
      denominatorLower denominatorUpper
      denominatorLowerPositive denominatorOrdered)
    (dividePositive numerator denominator
      (ℚP.<-≤-trans denominatorLowerPositive denominatorLowerSound))
    (quotientUpperEndpoint signCase
      denominatorLower denominatorUpper
      denominatorLowerPositive denominatorOrdered)
positiveDenominatorQuotientEnclosure
    {numeratorLower} {numeratorUpper} {numerator}
    {denominatorLower} {denominatorUpper} {denominator}
    (numeratorNonnegative numeratorLowerNonnegative)
    denominatorLowerPositive denominatorOrdered
    numeratorLowerSound numeratorUpperSound
    denominatorLowerSound denominatorUpperSound =
  let
    denominatorPositive =
      ℚP.<-≤-trans denominatorLowerPositive denominatorLowerSound
    denominatorUpperPositive =
      upperDenominatorPositive
        denominatorLower denominatorUpper
        denominatorLowerPositive denominatorOrdered

    numeratorNonnegative =
      ℚP.≤-trans numeratorLowerNonnegative numeratorLowerSound
    numeratorUpperNonnegative =
      ℚP.≤-trans numeratorNonnegative numeratorUpperSound

    lowerByDenominator =
      dividePositiveDenominatorAntitoneNonnegative
        numeratorLower denominator denominatorUpper
        numeratorLowerNonnegative denominatorPositive denominatorUpperPositive
        denominatorUpperSound
    lowerByNumerator =
      dividePositiveNumeratorMonotone
        numeratorLower numerator denominator denominatorPositive
        numeratorLowerSound

    upperByNumerator =
      dividePositiveNumeratorMonotone
        numerator numeratorUpper denominator denominatorPositive
        numeratorUpperSound
    upperByDenominator =
      dividePositiveDenominatorAntitoneNonnegative
        numeratorUpper denominatorLower denominator
        numeratorUpperNonnegative denominatorLowerPositive denominatorPositive
        denominatorLowerSound
  in
  liesBetween
    (ℚP.≤-trans lowerByDenominator lowerByNumerator)
    (ℚP.≤-trans upperByNumerator upperByDenominator)
positiveDenominatorQuotientEnclosure
    {numeratorLower} {numeratorUpper} {numerator}
    {denominatorLower} {denominatorUpper} {denominator}
    (numeratorNonpositive numeratorUpperNonpositive)
    denominatorLowerPositive denominatorOrdered
    numeratorLowerSound numeratorUpperSound
    denominatorLowerSound denominatorUpperSound =
  let
    denominatorPositive =
      ℚP.<-≤-trans denominatorLowerPositive denominatorLowerSound
    denominatorUpperPositive =
      upperDenominatorPositive
        denominatorLower denominatorUpper
        denominatorLowerPositive denominatorOrdered

    numeratorNonpositive =
      ℚP.≤-trans numeratorUpperSound numeratorUpperNonpositive
    numeratorLowerNonpositive =
      ℚP.≤-trans numeratorLowerSound numeratorNonpositive

    lowerByDenominator =
      dividePositiveDenominatorMonotoneNonpositive
        numeratorLower denominatorLower denominator
        numeratorLowerNonpositive denominatorLowerPositive denominatorPositive
        denominatorLowerSound
    lowerByNumerator =
      dividePositiveNumeratorMonotone
        numeratorLower numerator denominator denominatorPositive
        numeratorLowerSound

    upperByNumerator =
      dividePositiveNumeratorMonotone
        numerator numeratorUpper denominator denominatorPositive
        numeratorUpperSound
    upperByDenominator =
      dividePositiveDenominatorMonotoneNonpositive
        numeratorUpper denominator denominatorUpper
        numeratorUpperNonpositive denominatorPositive denominatorUpperPositive
        denominatorUpperSound
  in
  liesBetween
    (ℚP.≤-trans lowerByDenominator lowerByNumerator)
    (ℚP.≤-trans upperByNumerator upperByDenominator)
positiveDenominatorQuotientEnclosure
    {numeratorLower} {numeratorUpper} {numerator}
    {denominatorLower} {denominatorUpper} {denominator}
    (numeratorStraddlesZero numeratorLowerNonpositive numeratorUpperNonnegative)
    denominatorLowerPositive denominatorOrdered
    numeratorLowerSound numeratorUpperSound
    denominatorLowerSound denominatorUpperSound =
  let
    denominatorPositive =
      ℚP.<-≤-trans denominatorLowerPositive denominatorLowerSound

    lowerByDenominator =
      dividePositiveDenominatorMonotoneNonpositive
        numeratorLower denominatorLower denominator
        numeratorLowerNonpositive denominatorLowerPositive denominatorPositive
        denominatorLowerSound
    lowerByNumerator =
      dividePositiveNumeratorMonotone
        numeratorLower numerator denominator denominatorPositive
        numeratorLowerSound

    upperByNumerator =
      dividePositiveNumeratorMonotone
        numerator numeratorUpper denominator denominatorPositive
        numeratorUpperSound
    upperByDenominator =
      dividePositiveDenominatorAntitoneNonnegative
        numeratorUpper denominatorLower denominator
        numeratorUpperNonnegative denominatorLowerPositive denominatorPositive
        denominatorLowerSound
  in
  liesBetween
    (ℚP.≤-trans lowerByDenominator lowerByNumerator)
    (ℚP.≤-trans upperByNumerator upperByDenominator)

positiveNumeratorLegacyLowerExact :
  ∀ numeratorLower numeratorUpper denominatorLower denominatorUpper
    (nonnegative : 0ℚ ≤ numeratorLower)
    (denominatorLowerPositive : 0ℚ < denominatorLower)
    (denominatorOrdered : denominatorLower ≤ denominatorUpper) →
  quotientLowerEndpoint
    (numeratorNonnegative {numeratorLower} {numeratorUpper} nonnegative)
    denominatorLower denominatorUpper denominatorLowerPositive denominatorOrdered
  ≡ dividePositive numeratorLower denominatorUpper
      (upperDenominatorPositive
        denominatorLower denominatorUpper
        denominatorLowerPositive denominatorOrdered)
positiveNumeratorLegacyLowerExact numeratorLower numeratorUpper
    denominatorLower denominatorUpper nonnegative
    denominatorLowerPositive denominatorOrdered = refl

positiveNumeratorLegacyUpperExact :
  ∀ numeratorLower numeratorUpper denominatorLower denominatorUpper
    (nonnegative : 0ℚ ≤ numeratorLower)
    (denominatorLowerPositive : 0ℚ < denominatorLower)
    (denominatorOrdered : denominatorLower ≤ denominatorUpper) →
  quotientUpperEndpoint
    (numeratorNonnegative {numeratorLower} {numeratorUpper} nonnegative)
    denominatorLower denominatorUpper denominatorLowerPositive denominatorOrdered
  ≡ dividePositive numeratorUpper denominatorLower denominatorLowerPositive
positiveNumeratorLegacyUpperExact numeratorLower numeratorUpper
    denominatorLower denominatorUpper nonnegative
    denominatorLowerPositive denominatorOrdered = refl

positiveDenominatorReciprocalAntitoneLevel : ProofLevel
positiveDenominatorReciprocalAntitoneLevel = machineChecked

positiveDenominatorQuotientEnclosureLevel : ProofLevel
positiveDenominatorQuotientEnclosureLevel = machineChecked

positiveDenominatorSignAwareEndpointSelectionLevel : ProofLevel
positiveDenominatorSignAwareEndpointSelectionLevel = machineChecked