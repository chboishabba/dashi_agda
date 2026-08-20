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
  (cong; subst₂; sym; trans)

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

    -- Agda 2.9 leaves proof arguments of `positiveReciprocal` visible to the
    -- reflective ring solver.  Prove the scaled reciprocal identities directly
    -- from associativity/commutativity and the explicit inverse law instead.
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
      reciprocalNonnegative = positiveReciprocalNonnegative denominator denominatorPositive
  in
  ℚP.*-monoˡ-≤-nonNeg reciprocal lowerBelowUpper

divideNonnegativeDenominatorAntitone :
  ∀ numerator lowerDenominator upperDenominator
    (numeratorNonnegative : 0ℚ ≤ numerator)
    (lowerPositive : 0ℚ < lowerDenominator)
    (upperPositive : 0ℚ < upperDenominator) →
  lowerDenominator ≤ upperDenominator →
  dividePositive numerator upperDenominator upperPositive
  ≤ dividePositive numerator lowerDenominator lowerPositive
divideNonnegativeDenominatorAntitone numerator lowerDenominator upperDenominator
    numeratorNonnegative lowerPositive upperPositive lowerBelowUpper =
  let
    instance
      numeratorNN : NonNegative numerator
      numeratorNN = ℚ.nonNegative numeratorNonnegative
  in
  ℚP.*-monoʳ-≤-nonNeg numerator
    (reciprocalAntitonePositive
      lowerDenominator upperDenominator lowerPositive upperPositive lowerBelowUpper)

divideNonpositiveDenominatorMonotone :
  ∀ numerator lowerDenominator upperDenominator
    (numeratorNonpositive : numerator ≤ 0ℚ)
    (lowerPositive : 0ℚ < lowerDenominator)
    (upperPositive : 0ℚ < upperDenominator) →
  lowerDenominator ≤ upperDenominator →
  dividePositive numerator lowerDenominator lowerPositive
  ≤ dividePositive numerator upperDenominator upperPositive
divideNonpositiveDenominatorMonotone numerator lowerDenominator upperDenominator
    numeratorNonpositive lowerPositive upperPositive lowerBelowUpper =
  let
    instance
      numeratorNP : NonPositive numerator
      numeratorNP = ℚ.nonPositive numeratorNonpositive
  in
  ℚP.*-monoʳ-≤-nonPos numerator
    (reciprocalAntitonePositive
      lowerDenominator upperDenominator lowerPositive upperPositive lowerBelowUpper)

record PositiveDenominatorInterval : Set where
  constructor positiveDenominatorInterval
  field
    lowerDenominator upperDenominator : ℚ
    denominatorOrdered : lowerDenominator ≤ upperDenominator
    lowerDenominatorPositive : 0ℚ < lowerDenominator
open PositiveDenominatorInterval public

upperDenominatorStrictlyPositive :
  (denominator : PositiveDenominatorInterval) →
  0ℚ < upperDenominator denominator
upperDenominatorStrictlyPositive denominator =
  upperDenominatorPositive
    (lowerDenominator denominator)
    (upperDenominator denominator)
    (lowerDenominatorPositive denominator)
    (denominatorOrdered denominator)

record NumeratorInterval : Set where
  constructor numeratorInterval
  field
    lowerNumerator upperNumerator : ℚ
    numeratorOrdered : lowerNumerator ≤ upperNumerator
open NumeratorInterval public

record QuotientInterval : Set where
  constructor quotientInterval
  field
    quotientLower quotientUpper : ℚ
    quotientOrdered : quotientLower ≤ quotientUpper
open QuotientInterval public

nonnegativeQuotientInterval :
  NumeratorInterval → PositiveDenominatorInterval →
  0ℚ ≤ lowerNumerator → QuotientInterval
nonnegativeQuotientInterval numerator denominator lowerNN =
  let
    dL = lowerDenominator denominator
    dU = upperDenominator denominator
    dLPositive = lowerDenominatorPositive denominator
    dUPositive = upperDenominatorStrictlyPositive denominator
    nL = lowerNumerator numerator
    nU = upperNumerator numerator

    lowerEndpoint = dividePositive nL dU dUPositive
    upperEndpoint = dividePositive nU dL dLPositive

    first : lowerEndpoint ≤ dividePositive nL dL dLPositive
    first = divideNonnegativeDenominatorAntitone
      nL dL dU lowerNN dLPositive dUPositive (denominatorOrdered denominator)

    second : dividePositive nL dL dLPositive ≤ upperEndpoint
    second = dividePositiveNumeratorMonotone
      nL nU dL dLPositive (numeratorOrdered numerator)
  in
  quotientInterval lowerEndpoint upperEndpoint (ℚP.≤-trans first second)

nonpositiveQuotientInterval :
  NumeratorInterval → PositiveDenominatorInterval →
  upperNumerator ≤ 0ℚ → QuotientInterval
nonpositiveQuotientInterval numerator denominator upperNP =
  let
    dL = lowerDenominator denominator
    dU = upperDenominator denominator
    dLPositive = lowerDenominatorPositive denominator
    dUPositive = upperDenominatorStrictlyPositive denominator
    nL = lowerNumerator numerator
    nU = upperNumerator numerator

    lowerEndpoint = dividePositive nL dL dLPositive
    upperEndpoint = dividePositive nU dU dUPositive

    nLNP : nL ≤ 0ℚ
    nLNP = ℚP.≤-trans (numeratorOrdered numerator) upperNP

    first : lowerEndpoint ≤ dividePositive nL dU dUPositive
    first = divideNonpositiveDenominatorMonotone
      nL dL dU nLNP dLPositive dUPositive (denominatorOrdered denominator)

    second : dividePositive nL dU dUPositive ≤ upperEndpoint
    second = dividePositiveNumeratorMonotone
      nL nU dU dUPositive (numeratorOrdered numerator)
  in
  quotientInterval lowerEndpoint upperEndpoint (ℚP.≤-trans first second)

straddlingQuotientInterval :
  NumeratorInterval → PositiveDenominatorInterval →
  lowerNumerator ≤ 0ℚ → 0ℚ ≤ upperNumerator → QuotientInterval
straddlingQuotientInterval numerator denominator lowerNP upperNN =
  let
    dL = lowerDenominator denominator
    dLPositive = lowerDenominatorPositive denominator
    nL = lowerNumerator numerator
    nU = upperNumerator numerator

    lowerEndpoint = dividePositive nL dL dLPositive
    upperEndpoint = dividePositive nU dL dLPositive
  in
  quotientInterval lowerEndpoint upperEndpoint
    (dividePositiveNumeratorMonotone
      nL nU dL dLPositive (numeratorOrdered numerator))

signAwarePositiveDenominatorQuotient :
  (numerator : NumeratorInterval) →
  (denominator : PositiveDenominatorInterval) →
  NumeratorSignCase (lowerNumerator numerator) (upperNumerator numerator) →
  QuotientInterval
signAwarePositiveDenominatorQuotient numerator denominator
    (numeratorNonnegative lowerNN) =
  nonnegativeQuotientInterval numerator denominator lowerNN
signAwarePositiveDenominatorQuotient numerator denominator
    (numeratorNonpositive upperNP) =
  nonpositiveQuotientInterval numerator denominator upperNP
signAwarePositiveDenominatorQuotient numerator denominator
    (numeratorStraddlesZero lowerNP upperNN) =
  straddlingQuotientInterval numerator denominator lowerNP upperNN

------------------------------------------------------------------------
-- Pointwise soundness of the three endpoint formulas.
------------------------------------------------------------------------

record PointInsideNumerator
    (value : ℚ) (numerator : NumeratorInterval) : Set where
  constructor pointInsideNumerator
  field
    numeratorLowerSound : lowerNumerator numerator ≤ value
    numeratorUpperSound : value ≤ upperNumerator numerator
open PointInsideNumerator public

record PointInsidePositiveDenominator
    (value : ℚ) (denominator : PositiveDenominatorInterval) : Set where
  constructor pointInsidePositiveDenominator
  field
    denominatorLowerSound : lowerDenominator denominator ≤ value
    denominatorUpperSound : value ≤ upperDenominator denominator
open PointInsidePositiveDenominator public

denominatorPointPositive :
  ∀ {value denominator} →
  PointInsidePositiveDenominator value denominator → 0ℚ < value
denominatorPointPositive {denominator = denominator} inside =
  ℚP.<-≤-trans
    (lowerDenominatorPositive denominator)
    (denominatorLowerSound inside)

record PointInsideQuotient
    (value : ℚ) (interval : QuotientInterval) : Set where
  constructor pointInsideQuotient
  field
    quotientLowerSound : quotientLower interval ≤ value
    quotientUpperSound : value ≤ quotientUpper interval
open PointInsideQuotient public

nonnegativeQuotientSound :
  ∀ numerator denominator numeratorValue denominatorValue
    (lowerNN : 0ℚ ≤ lowerNumerator numerator)
    (numeratorInside : PointInsideNumerator numeratorValue numerator)
    (denominatorInside : PointInsidePositiveDenominator denominatorValue denominator) →
  PointInsideQuotient
    (dividePositive numeratorValue denominatorValue
      (denominatorPointPositive denominatorInside))
    (nonnegativeQuotientInterval numerator denominator lowerNN)
nonnegativeQuotientSound numerator denominator numeratorValue denominatorValue lowerNN numeratorInside denominatorInside =
  let
    dL = lowerDenominator denominator
    dU = upperDenominator denominator
    dVPositive = denominatorPointPositive denominatorInside
    nL = lowerNumerator numerator
    nU = upperNumerator numerator

    nVNN : 0ℚ ≤ numeratorValue
    nVNN = ℚP.≤-trans lowerNN (numeratorLowerSound numeratorInside)

    lowerViaDenominator :
      dividePositive nL dU (upperDenominatorStrictlyPositive denominator)
      ≤ dividePositive nL denominatorValue dVPositive
    lowerViaDenominator = divideNonnegativeDenominatorAntitone
      nL denominatorValue dU lowerNN dVPositive
      (upperDenominatorStrictlyPositive denominator)
      (denominatorUpperSound denominatorInside)

    lowerViaNumerator :
      dividePositive nL denominatorValue dVPositive
      ≤ dividePositive numeratorValue denominatorValue dVPositive
    lowerViaNumerator = dividePositiveNumeratorMonotone
      nL numeratorValue denominatorValue dVPositive
      (numeratorLowerSound numeratorInside)

    upperViaDenominator :
      dividePositive numeratorValue denominatorValue dVPositive
      ≤ dividePositive numeratorValue dL (lowerDenominatorPositive denominator)
    upperViaDenominator = divideNonnegativeDenominatorAntitone
      numeratorValue dL denominatorValue nVNN
      (lowerDenominatorPositive denominator) dVPositive
      (denominatorLowerSound denominatorInside)

    upperViaNumerator :
      dividePositive numeratorValue dL (lowerDenominatorPositive denominator)
      ≤ dividePositive nU dL (lowerDenominatorPositive denominator)
    upperViaNumerator = dividePositiveNumeratorMonotone
      numeratorValue nU dL (lowerDenominatorPositive denominator)
      (numeratorUpperSound numeratorInside)
  in
  pointInsideQuotient
    (ℚP.≤-trans lowerViaDenominator lowerViaNumerator)
    (ℚP.≤-trans upperViaDenominator upperViaNumerator)

nonpositiveQuotientSound :
  ∀ numerator denominator numeratorValue denominatorValue
    (upperNP : upperNumerator numerator ≤ 0ℚ)
    (numeratorInside : PointInsideNumerator numeratorValue numerator)
    (denominatorInside : PointInsidePositiveDenominator denominatorValue denominator) →
  PointInsideQuotient
    (dividePositive numeratorValue denominatorValue
      (denominatorPointPositive denominatorInside))
    (nonpositiveQuotientInterval numerator denominator upperNP)
nonpositiveQuotientSound numerator denominator numeratorValue denominatorValue upperNP numeratorInside denominatorInside =
  let
    dL = lowerDenominator denominator
    dU = upperDenominator denominator
    dVPositive = denominatorPointPositive denominatorInside
    nL = lowerNumerator numerator
    nU = upperNumerator numerator

    nVNP : numeratorValue ≤ 0ℚ
    nVNP = ℚP.≤-trans (numeratorUpperSound numeratorInside) upperNP
    nLNP : nL ≤ 0ℚ
    nLNP = ℚP.≤-trans (numeratorOrdered numerator) upperNP

    lowerViaDenominator :
      dividePositive nL dL (lowerDenominatorPositive denominator)
      ≤ dividePositive nL denominatorValue dVPositive
    lowerViaDenominator = divideNonpositiveDenominatorMonotone
      nL dL denominatorValue nLNP
      (lowerDenominatorPositive denominator) dVPositive
      (denominatorLowerSound denominatorInside)

    lowerViaNumerator :
      dividePositive nL denominatorValue dVPositive
      ≤ dividePositive numeratorValue denominatorValue dVPositive
    lowerViaNumerator = dividePositiveNumeratorMonotone
      nL numeratorValue denominatorValue dVPositive
      (numeratorLowerSound numeratorInside)

    upperViaDenominator :
      dividePositive numeratorValue denominatorValue dVPositive
      ≤ dividePositive numeratorValue dU (upperDenominatorStrictlyPositive denominator)
    upperViaDenominator = divideNonpositiveDenominatorMonotone
      numeratorValue denominatorValue dU nVNP dVPositive
      (upperDenominatorStrictlyPositive denominator)
      (denominatorUpperSound denominatorInside)

    upperViaNumerator :
      dividePositive numeratorValue dU (upperDenominatorStrictlyPositive denominator)
      ≤ dividePositive nU dU (upperDenominatorStrictlyPositive denominator)
    upperViaNumerator = dividePositiveNumeratorMonotone
      numeratorValue nU dU (upperDenominatorStrictlyPositive denominator)
      (numeratorUpperSound numeratorInside)
  in
  pointInsideQuotient
    (ℚP.≤-trans lowerViaDenominator lowerViaNumerator)
    (ℚP.≤-trans upperViaDenominator upperViaNumerator)

straddlingQuotientSound :
  ∀ numerator denominator numeratorValue denominatorValue
    (lowerNP : lowerNumerator numerator ≤ 0ℚ)
    (upperNN : 0ℚ ≤ upperNumerator numerator)
    (numeratorInside : PointInsideNumerator numeratorValue numerator)
    (denominatorInside : PointInsidePositiveDenominator denominatorValue denominator) →
  PointInsideQuotient
    (dividePositive numeratorValue denominatorValue
      (denominatorPointPositive denominatorInside))
    (straddlingQuotientInterval numerator denominator lowerNP upperNN)
straddlingQuotientSound numerator denominator numeratorValue denominatorValue lowerNP upperNN numeratorInside denominatorInside =
  let
    dL = lowerDenominator denominator
    dVPositive = denominatorPointPositive denominatorInside
    nL = lowerNumerator numerator
    nU = upperNumerator numerator

    lowerViaDenominator :
      dividePositive nL dL (lowerDenominatorPositive denominator)
      ≤ dividePositive nL denominatorValue dVPositive
    lowerViaDenominator = divideNonpositiveDenominatorMonotone
      nL dL denominatorValue lowerNP
      (lowerDenominatorPositive denominator) dVPositive
      (denominatorLowerSound denominatorInside)

    lowerViaNumerator :
      dividePositive nL denominatorValue dVPositive
      ≤ dividePositive numeratorValue denominatorValue dVPositive
    lowerViaNumerator = dividePositiveNumeratorMonotone
      nL numeratorValue denominatorValue dVPositive
      (numeratorLowerSound numeratorInside)

    upperViaNumerator :
      dividePositive numeratorValue denominatorValue dVPositive
      ≤ dividePositive nU denominatorValue dVPositive
    upperViaNumerator = dividePositiveNumeratorMonotone
      numeratorValue nU denominatorValue dVPositive
      (numeratorUpperSound numeratorInside)

    upperViaDenominator :
      dividePositive nU denominatorValue dVPositive
      ≤ dividePositive nU dL (lowerDenominatorPositive denominator)
    upperViaDenominator = divideNonnegativeDenominatorAntitone
      nU dL denominatorValue upperNN
      (lowerDenominatorPositive denominator) dVPositive
      (denominatorLowerSound denominatorInside)
  in
  pointInsideQuotient
    (ℚP.≤-trans lowerViaDenominator lowerViaNumerator)
    (ℚP.≤-trans upperViaNumerator upperViaDenominator)

positiveDenominatorQuotientEndpointLevel : ProofLevel
positiveDenominatorQuotientEndpointLevel = machineChecked

positiveDenominatorQuotientPointwiseSoundLevel : ProofLevel
positiveDenominatorQuotientPointwiseSoundLevel = machineChecked
