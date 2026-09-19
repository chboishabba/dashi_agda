module DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondOrderEnvelopeExact where

------------------------------------------------------------------------
-- POST-CANCELLATION SECOND-ORDER ENVELOPE FOR THE CENTERED RESOLVENT SYMBOL
--
-- From the exact opposite-shift identity
--
--   Delta_h^2 J_a(s)
--     = -2 h^2
--         inv(a+s) inv(a+s+h) inv(a+s-h),
--
-- assume only
--
--   a > 0,
--   s >= 0,
--   s+h >= 0,
--   s-h >= 0.
--
-- Every shifted denominator is therefore at least a, so reciprocal
-- antitonicity gives
--
--   |Delta_h^2 J_a(s)| <= 2 h^2 inv(a)^3.
--
-- This is the literal quadratic multiplier-curvature estimate needed by the
-- existing paired second-moment compiler.  It is cutoff independent and has
-- no fibre-cardinality factor.  Absolute value appears only AFTER the exact
-- opposite-shift cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _-_; _*_; -_; _≤_; _<_; ∣_∣;
   positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNCenteredResolventKernelEnvelopeExact as Kernel
import DASHI.Physics.Closure.NSTriadKNCenteredResolventOppositeShiftSecondOrderExact as Resolvent
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

two : ℚ
two = 1ℚ + 1ℚ

twoNonnegative : 0ℚ ≤ two
twoNonnegative =
  Rational.addNonnegative
    (Rational.squareNonnegative 1ℚ)
    (Rational.squareNonnegative 1ℚ)

safeInvPositive :
  (x : ℚ) → (xPositive : 0ℚ < x) →
  0ℚ < Resolvent.inv x
safeInvPositive x xPositive =
  let
    exact =
      R449.safeReciprocalIsPositiveReciprocal x xPositive
    positiveReciprocal =
      Quotient.positiveReciprocalPositive x xPositive
  in
  subst
    (0ℚ <_)
    (sym exact)
    positiveReciprocal

safeInvNonnegative :
  (x : ℚ) → (xPositive : 0ℚ < x) →
  0ℚ ≤ Resolvent.inv x
safeInvNonnegative x xPositive =
  ℚP.<⇒≤ (safeInvPositive x xPositive)

safeInvAntitone :
  (lower upper : ℚ) →
  (lowerPositive : 0ℚ < lower) →
  (upperPositive : 0ℚ < upper) →
  lower ≤ upper →
  Resolvent.inv upper ≤ Resolvent.inv lower
safeInvAntitone lower upper lowerPositive upperPositive lowerBelowUpper
  rewrite R449.safeReciprocalIsPositiveReciprocal upper upperPositive
        | R449.safeReciprocalIsPositiveReciprocal lower lowerPositive =
  Quotient.reciprocalAntitonePositive
    lower upper lowerPositive upperPositive lowerBelowUpper

shiftedDenominatorAboveBase :
  (a residual : ℚ) →
  0ℚ ≤ residual →
  a ≤ a + residual
shiftedDenominatorAboveBase a residual residualNN =
  Kernel.baseBelowBasePlusDefect residualNN

tripleInverseBound :
  (a x y z : ℚ) →
  (aPositive : 0ℚ < a) →
  (xPositive : 0ℚ < x) →
  (yPositive : 0ℚ < y) →
  (zPositive : 0ℚ < z) →
  a ≤ x → a ≤ y → a ≤ z →
  Resolvent.inv x * Resolvent.inv y * Resolvent.inv z
  ≤
  Resolvent.inv a * Resolvent.inv a * Resolvent.inv a
tripleInverseBound
    a x y z aPositive xPositive yPositive zPositive
    aBelowX aBelowY aBelowZ =
  let
    ia = Resolvent.inv a
    ix = Resolvent.inv x
    iy = Resolvent.inv y
    iz = Resolvent.inv z

    iaNN = safeInvNonnegative a aPositive
    ixNN = safeInvNonnegative x xPositive
    iyNN = safeInvNonnegative y yPositive
    izNN = safeInvNonnegative z zPositive

    xBound : ix ≤ ia
    xBound = safeInvAntitone a x aPositive xPositive aBelowX

    yBound : iy ≤ ia
    yBound = safeInvAntitone a y aPositive yPositive aBelowY

    zBound : iz ≤ ia
    zBound = safeInvAntitone a z aPositive zPositive aBelowZ

    pairBound : ix * iy ≤ ia * ia
    pairBound =
      Moment.multiplyBounds
        ixNN iaNN iyNN iaNN xBound yBound

    pairNN : 0ℚ ≤ ix * iy
    pairNN =
      Moment.productNonnegative ix iy ixNN iyNN

    pairUpperNN : 0ℚ ≤ ia * ia
    pairUpperNN =
      Moment.productNonnegative ia ia iaNN iaNN
  in
  Moment.multiplyBounds
    pairNN pairUpperNN izNN iaNN pairBound zBound

centeredResolventSecondOrderMagnitudeEnvelope :
  (a s h : ℚ) →
  (aPositive : 0ℚ < a) →
  (centerResidualNN : 0ℚ ≤ s) →
  (plusResidualNN : 0ℚ ≤ s + h) →
  (minusResidualNN : 0ℚ ≤ s - h) →
  ∣ Resolvent.centeredSecondDifference a s h ∣
  ≤
  two * h * h
    * Resolvent.inv a * Resolvent.inv a * Resolvent.inv a
centeredResolventSecondOrderMagnitudeEnvelope
    a s h aPositive centerResidualNN plusResidualNN minusResidualNN =
  let
    x = a + s
    xp = a + (s + h)
    xm = a + (s - h)

    xPositive = Kernel.positivePlusNonnegative aPositive centerResidualNN
    xpPositive = Kernel.positivePlusNonnegative aPositive plusResidualNN
    xmPositive = Kernel.positivePlusNonnegative aPositive minusResidualNN

    xPositiveI : Positive x
    xPositiveI = positive xPositive
    xpPositiveI : Positive xp
    xpPositiveI = positive xpPositive
    xmPositiveI : Positive xm
    xmPositiveI = positive xmPositive
    aPositiveI : Positive a
    aPositiveI = positive aPositive

    ix = Resolvent.inv x
    ip = Resolvent.inv xp
    im = Resolvent.inv xm
    ia = Resolvent.inv a

    ixNN = safeInvNonnegative x xPositive
    ipNN = safeInvNonnegative xp xpPositive
    imNN = safeInvNonnegative xm xmPositive

    hSquareNN : 0ℚ ≤ h * h
    hSquareNN = Rational.squareNonnegative h

    twoHSquareNN : 0ℚ ≤ two * h * h
    twoHSquareNN =
      subst
        (0ℚ ≤_)
        (solve (two ∷ h ∷ []))
        (Moment.productNonnegative two (h * h) twoNonnegative hSquareNN)

    tripleNN :
      0ℚ ≤ ix * ip * im
    tripleNN =
      Moment.productNonnegative
        (ix * ip) im
        (Moment.productNonnegative ix ip ixNN ipNN)
        imNN

    coefficientNN :
      0ℚ ≤ two * h * h * ix * ip * im
    coefficientNN =
      subst
        (0ℚ ≤_)
        (solve (two ∷ h ∷ ix ∷ ip ∷ im ∷ []))
        (Moment.productNonnegative
          (two * h * h) (ix * ip * im)
          twoHSquareNN tripleNN)

    exactSecondOrder :
      Resolvent.centeredSecondDifference a s h
      ≡ 0ℚ - two * h * h * ix * ip * im
    exactSecondOrder =
      Resolvent.oppositeShiftCenteredResolventSecondOrder
        a s h aPositiveI xPositiveI xpPositiveI xmPositiveI

    absoluteExact :
      ∣ Resolvent.centeredSecondDifference a s h ∣
      ≡ two * h * h * ix * ip * im
    absoluteExact =
      trans
        (cong ∣_∣ exactSecondOrder)
        (trans
          (cong ∣_∣
            (solve
              (two ∷ h ∷ ix ∷ ip ∷ im ∷ [])))
          (trans
            (ℚP.∣-p∣≡∣p∣
              (two * h * h * ix * ip * im))
            (ℚP.0≤p⇒∣p∣≡p coefficientNN)))

    tripleBound :
      ix * ip * im ≤ ia * ia * ia
    tripleBound =
      tripleInverseBound
        a x xp xm
        aPositive xPositive xpPositive xmPositive
        (shiftedDenominatorAboveBase a s centerResidualNN)
        (shiftedDenominatorAboveBase a (s + h) plusResidualNN)
        (shiftedDenominatorAboveBase a (s - h) minusResidualNN)

    scaledBound :
      two * h * h * (ix * ip * im)
      ≤ two * h * h * (ia * ia * ia)
    scaledBound =
      let
        instance
          scaleNNI : NonNegative (two * h * h)
          scaleNNI = nonNegative twoHSquareNN
      in
      ℚP.*-monoˡ-≤-nonNeg (two * h * h) tripleBound

    targetBound :
      two * h * h * ix * ip * im
      ≤ two * h * h * ia * ia * ia
    targetBound =
      subst
        (λ rhs → two * h * h * ix * ip * im ≤ rhs)
        (solve (two ∷ h ∷ ia ∷ []))
        (subst
          (λ lhs → lhs ≤ two * h * h * (ia * ia * ia))
          (solve (two ∷ h ∷ ix ∷ ip ∷ im ∷ []))
          scaledBound)
  in
  subst
    (λ lhs → lhs ≤ two * h * h * ia * ia * ia)
    (sym absoluteExact)
    targetBound

resolventTransportCurvature :
  (a : ℚ) → ℚ
resolventTransportCurvature a =
  two * Resolvent.inv a * Resolvent.inv a * Resolvent.inv a

centeredResolventSecondOrderEnvelopeClosed : Bool
centeredResolventSecondOrderEnvelopeClosed = true

absoluteValueAppliedOnlyAfterPairedCancellation : Bool
absoluteValueAppliedOnlyAfterPairedCancellation = true

transportCurvatureHasNoCutoffParameter : Bool
transportCurvatureHasNoCutoffParameter = true

transportCurvatureHasNoFibreCardinality : Bool
transportCurvatureHasNoFibreCardinality = true

stateDerivativeEnvelopeClosedHere : Bool
stateDerivativeEnvelopeClosedHere = false

cutoffUniformPhysicalSecondMomentClosedHere : Bool
cutoffUniformPhysicalSecondMomentClosedHere = false

clayPromotion : Bool
clayPromotion = false

centeredResolventSecondOrderEnvelopeClosedIsTrue :
  centeredResolventSecondOrderEnvelopeClosed ≡ true
centeredResolventSecondOrderEnvelopeClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
