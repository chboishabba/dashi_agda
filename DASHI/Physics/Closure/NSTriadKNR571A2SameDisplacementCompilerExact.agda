module DASHI.Physics.Closure.NSTriadKNR571A2SameDisplacementCompilerExact where

------------------------------------------------------------------------
-- PERIODIC B / R571 A2 SAME-DISPLACEMENT COMPILER
--
-- The existing centered physical geometry proves
--
--   r_k * excess <= 4 * |y|^2.
--
-- If the centre radius is at least one and the centered excess is
-- nonnegative, then
--
--   excess <= 4 * |y|^2.
--
-- If the chosen second-moment displacement d satisfies
--
--   |y|^2 <= d^2,
--
-- then the exact Gate-A shape follows:
--
--   |minusRemainder| <= d^2 * 4.
--
-- This owner performs the missing ordered transport into
-- R571PreferredRadialCurvatureSample.  It deliberately keeps the two
-- physically meaningful hypotheses visible: nonnegative centered excess and
-- the centre unit-radius floor.  No Lean receipt or postulate is consumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialDenominatorOrderExact as Order
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialProductBridgeExact as Product
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact as Boundary
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor

four : ℚ
four = Product.four

fourNonnegative : 0ℚ ≤ four
fourNonnegative =
  Rational.productNonnegative
    (Rational.addNonnegative Rational.oneNonnegative Rational.oneNonnegative)
    (Rational.addNonnegative Rational.oneNonnegative Rational.oneNonnegative)

dropCenterRadius :
  ∀ {r excess upper : ℚ} →
  1ℚ ≤ r →
  0ℚ ≤ excess →
  r * excess ≤ upper →
  excess ≤ upper
dropCenterRadius {r} {excess} {upper} oneBelowR excessNN productBound =
  let
    instance excessNNI = nonNegative excessNN
    raised : 1ℚ * excess ≤ r * excess
    raised = ℚP.*-monoʳ-≤-nonNeg excess oneBelowR
  in
  ℚP.≤-trans
    (subst (excess ≤_) (ℚP.*-identityˡ excess) raised)
    productBound

inflateFour :
  ∀ {small large : ℚ} →
  0ℚ ≤ small →
  small ≤ large →
  four * small ≤ four * large
inflateFour smallNN smallBelowLarge =
  let instance fourNNI = nonNegative fourNonnegative
  in ℚP.*-monoˡ-≤-nonNeg four smallBelowLarge

record A2SameDisplacementData
    (E : C3.IntegerEmbedding GateA.Weld.F)
    (I : C3.ModeInverseSquare GateA.Weld.F E)
    (S : Helical.HelicalModeScalars GateA.Weld.F)
    (sign : R311.HelicitySign)
    (center displacement : GateA.Z3.FourierMode)
    (stepMagnitude : ℚ) : Set₁ where
  field
    physical :
      Product.CenteredRadialA2Data E I S center displacement

    centerRadiusAtLeastOne :
      1ℚ ≤ Helical.modeNorm S center

    centeredExcessNonnegative :
      0ℚ ≤
      Order.centeredExcess
        (Helical.modeNorm S (Product.CenteredShift.plusMode center displacement))
        (Helical.modeNorm S (Product.CenteredShift.minusMode center displacement))
        (Helical.modeNorm S center)

    stepMagnitudeNonnegative : 0ℚ ≤ stepMagnitude

    displacementSquareBelowStepSquare :
      C3.normSquared I displacement
      ≤ stepMagnitude * stepMagnitude

    minusRemainderIsCenteredExcess :
      ∣ Taylor.minusRemainder
          (GateA.preferredRadialTaylorPair
            sign S center
            (Product.CenteredShift.plusMode center displacement)
            (Product.CenteredShift.minusMode center displacement)) ∣
      ≡
      Order.centeredExcess
        (Helical.modeNorm S (Product.CenteredShift.plusMode center displacement))
        (Helical.modeNorm S (Product.CenteredShift.minusMode center displacement))
        (Helical.modeNorm S center)

open A2SameDisplacementData public

a2SameDisplacementBound :
  ∀ {E I S sign center displacement stepMagnitude} →
  (D : A2SameDisplacementData
    E I S sign center displacement stepMagnitude) →
  ∣ Taylor.minusRemainder
      (GateA.preferredRadialTaylorPair
        sign S center
        (Product.CenteredShift.plusMode center displacement)
        (Product.CenteredShift.minusMode center displacement)) ∣
  ≤ stepMagnitude * stepMagnitude * four
a2SameDisplacementBound
    {I = I} {S = S} {center = center}
    {displacement = displacement} {stepMagnitude = stepMagnitude} D =
  let
    p = Product.CenteredShift.plusMode center displacement
    q = Product.CenteredShift.minusMode center displacement
    excess =
      Order.centeredExcess
        (Helical.modeNorm S p)
        (Helical.modeNorm S q)
        (Helical.modeNorm S center)

    weighted :
      Helical.modeNorm S center * excess
      ≤ four * C3.normSquared I displacement
    weighted = Product.centeredRadialCurvaturePayment (physical D)

    unweighted :
      excess ≤ four * C3.normSquared I displacement
    unweighted =
      dropCenterRadius
        (centerRadiusAtLeastOne D)
        (centeredExcessNonnegative D)
        weighted

    inflated :
      four * C3.normSquared I displacement
      ≤ four * (stepMagnitude * stepMagnitude)
    inflated =
      inflateFour
        (Product.centeredFourDisplacementSquareNonnegative
          {E = E} {I = I} displacement)
        (displacementSquareBelowStepSquare D)

    target :
      four * (stepMagnitude * stepMagnitude)
      ≡ stepMagnitude * stepMagnitude * four
    target = solve (stepMagnitude ∷ four ∷ [])
  in
  subst
    (_≤ stepMagnitude * stepMagnitude * four)
    target
    (subst
      (λ lower → lower ≤ four * (stepMagnitude * stepMagnitude))
      (sym (minusRemainderIsCenteredExcess D))
      (ℚP.≤-trans unweighted inflated))

compileA2SameDisplacementSample :
  ∀ {E I S sign center displacement stepMagnitude} →
  (D : A2SameDisplacementData
    E I S sign center displacement stepMagnitude) →
  Boundary.R571PreferredRadialCurvatureSample
compileA2SameDisplacementSample
    {S = S} {sign = sign} {center = center}
    {displacement = displacement} {stepMagnitude = stepMagnitude} D = record
  { Boundary.sign = sign
  ; Boundary.scalars = S
  ; Boundary.center = center
  ; Boundary.plus = Product.CenteredShift.plusMode center displacement
  ; Boundary.minus = Product.CenteredShift.minusMode center displacement
  ; Boundary.stepMagnitude = stepMagnitude
  ; Boundary.transportCurvature = four
  ; Boundary.stepMagnitudeNonnegative = stepMagnitudeNonnegative D
  ; Boundary.transportCurvatureNonnegative = fourNonnegative
  ; Boundary.minusRemainderCurvatureBound = a2SameDisplacementBound D
  }

r571A2OrderedTransportToGateASampleClosed : Bool
r571A2OrderedTransportToGateASampleClosed = true

r571A2StillNeedsPhysicalExcessAndCenterFloorInstantiation : Bool
r571A2StillNeedsPhysicalExcessAndCenterFloorInstantiation = true

clayPromotion : Bool
clayPromotion = false

r571A2OrderedTransportToGateASampleClosedIsTrue :
  r571A2OrderedTransportToGateASampleClosed ≡ true
r571A2OrderedTransportToGateASampleClosedIsTrue = refl
