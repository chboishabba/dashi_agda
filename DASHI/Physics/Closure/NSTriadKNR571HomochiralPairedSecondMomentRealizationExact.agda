module DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact where

------------------------------------------------------------------------
-- TIMESTAMP
-- 2026-09-14 11:00 AEST (UTC+10)
--
-- PUBLICATION-ORIENTED LOCAL SPLICE
--
-- Reuse, without duplicating, the existing theorem carriers:
--
--   R571 homochiral physical multiplier difference
--     -> R571/R311/Round27 radial same-object weld
--     -> Aug-5 MultiplierTaylorPair
--     -> old centered PairedCommutatorSample
--     -> old second-order PairedCommutatorSample
--     -> old PairedSecondMomentSample quantitative carrier.
--
-- This owner closes the IDENTITY/REPRESENTATION part of that splice.  It
-- constructs the exact opposite-shift Taylor carrier from literal radial
-- multiplier values and proves the old centered and second-order paired
-- carriers agree on that data.
--
-- It deliberately does NOT claim the four physical envelope inequalities
-- required by the second-moment compiler, an inner-fibre summed gain, R568, or
-- a Clay endpoint.
--
-- BIDI / ABANDONED ROUTE PROVENANCE
-- PR #890 exposed that fixed-output incidence geometry alone need not determine
-- the physical slot observable; the later collision tranche made that
-- many-to-one warning explicit.  Therefore this module does not resurrect an
-- incidence-only radial/Pluecker coercivity claim.  The failed route is retained
-- as a negative control: the live route is state/multiplier dependent and must
-- pay its magnitude envelopes explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor
import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Centered
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondOrderExact as SecondOrder
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

------------------------------------------------------------------------
-- 1. Literal radial multiplier and canonical opposite-shift Taylor carrier.
------------------------------------------------------------------------

radialSymbol :
  R311.HelicitySign →
  Helical.HelicalModeScalars Weld.F →
  Z3.FourierMode → ℚ
radialSymbol sign S mode =
  R27.multiplierSymbol (Weld.radialMultiplier sign S) mode

radialTaylorPair :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode : Z3.FourierMode) →
  (linearModel : ℚ) →
  Taylor.MultiplierTaylorPair
radialTaylorPair sign S centerMode plusMode minusMode linearModel =
  Taylor.multiplier-taylor-pair
    (radialSymbol sign S centerMode)
    linearModel
    (radialSymbol sign S plusMode
      - radialSymbol sign S centerMode
      - linearModel)
    (radialSymbol sign S minusMode
      - radialSymbol sign S centerMode
      + linearModel)

radialTaylorPlusValueExact :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode : Z3.FourierMode) →
  (linearModel : ℚ) →
  Taylor.plusValue
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
  ≡ radialSymbol sign S plusMode
radialTaylorPlusValueExact sign S centerMode plusMode minusMode linearModel =
  solve
    ( radialSymbol sign S centerMode
    ∷ radialSymbol sign S plusMode
    ∷ linearModel
    ∷ [])

radialTaylorMinusValueExact :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode : Z3.FourierMode) →
  (linearModel : ℚ) →
  Taylor.minusValue
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
  ≡ radialSymbol sign S minusMode
radialTaylorMinusValueExact sign S centerMode plusMode minusMode linearModel =
  solve
    ( radialSymbol sign S centerMode
    ∷ radialSymbol sign S minusMode
    ∷ linearModel
    ∷ [])

radialTaylorCenteredSecondDifferenceExact :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode : Z3.FourierMode) →
  (linearModel : ℚ) →
  Taylor.centeredSecondDifference
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
  ≡
  Taylor.plusRemainder
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
  + Taylor.minusRemainder
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
radialTaylorCenteredSecondDifferenceExact sign S centerMode plusMode minusMode linearModel =
  Taylor.centeredSecondDifferenceCancelsLinearSymbol
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)

------------------------------------------------------------------------
-- 2. Round27 signed multiplier difference is exactly the Taylor one-sided
--    increment whenever the Fourier shift lands on the selected center mode.
------------------------------------------------------------------------

round27PlusDifferenceIsTaylorOneSided :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (shift centerMode plusMode minusMode : Z3.FourierMode) →
  (linearModel : ℚ) →
  R27.shiftedMode shift plusMode ≡ centerMode →
  R27.multiplierSymbol
    (R27.multiplierDifference
      (Weld.radialMultiplier sign S)
      (R27.translateMultiplierSymbol shift (Weld.radialMultiplier sign S)))
    plusMode
  ≡
  Taylor.oneSidedDifference
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
round27PlusDifferenceIsTaylorOneSided
  sign S shift centerMode plusMode minusMode linearModel shiftedIsCenter
  rewrite shiftedIsCenter =
  solve
    ( radialSymbol sign S centerMode
    ∷ radialSymbol sign S plusMode
    ∷ linearModel
    ∷ [])

oppositeTaylorDifference : Taylor.MultiplierTaylorPair → ℚ
oppositeTaylorDifference sample =
  Taylor.minusValue sample - Taylor.center sample

round27MinusDifferenceIsTaylorOpposite :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (shift centerMode plusMode minusMode : Z3.FourierMode) →
  (linearModel : ℚ) →
  R27.shiftedMode shift minusMode ≡ centerMode →
  R27.multiplierSymbol
    (R27.multiplierDifference
      (Weld.radialMultiplier sign S)
      (R27.translateMultiplierSymbol shift (Weld.radialMultiplier sign S)))
    minusMode
  ≡
  oppositeTaylorDifference
    (radialTaylorPair sign S centerMode plusMode minusMode linearModel)
round27MinusDifferenceIsTaylorOpposite
  sign S shift centerMode plusMode minusMode linearModel shiftedIsCenter
  rewrite shiftedIsCenter =
  solve
    ( radialSymbol sign S centerMode
    ∷ radialSymbol sign S minusMode
    ∷ linearModel
    ∷ [])

------------------------------------------------------------------------
-- 3. Literal Round27 scalar on the already-proved R571 homochiral radial route.
------------------------------------------------------------------------

r571Round27Scalar :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (shift : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (output : Z3.FourierMode) → ℚ
r571Round27Scalar sign S shift state output =
  R27.stateCoefficient
    (R27.translationMultiplierCommutator
      (Weld.radialMultiplier sign S) shift state)
    output

------------------------------------------------------------------------
-- 4. Same-object scalarization into the EXISTING centered paired carrier.
--    The exact physical scalarization equation remains explicit as a field;
--    no incidence-only separation is fabricated.
------------------------------------------------------------------------

record R571PairedTaylorRealization : Set₁ where
  field
    sign : R311.HelicitySign
    scalars : Helical.HelicalModeScalars Weld.F
    shift : Z3.FourierMode
    state : R27.FourierStateCarrier
    output : Z3.FourierMode

    taylorPair : Taylor.MultiplierTaylorPair
    pairedSample : Centered.PairedCommutatorSample

    pairedCenterIsTaylorCenter :
      Centered.aCenter pairedSample ≡ Taylor.center taylorPair
    pairedPlusIsTaylorPlus :
      Centered.aPlus pairedSample ≡ Taylor.plusValue taylorPair
    pairedMinusIsTaylorMinus :
      Centered.aMinus pairedSample ≡ Taylor.minusValue taylorPair

    round27ScalarIsWeightedRawPair :
      r571Round27Scalar sign scalars shift state output
      ≡ Centered.weightedRawPair pairedSample

open R571PairedTaylorRealization public

r571PairedCenteredIdentity :
  (realization : R571PairedTaylorRealization) →
  r571Round27Scalar
      (sign realization)
      (scalars realization)
      (shift realization)
      (state realization)
      (output realization)
  ≡ Centered.weightedCenteredBranch (pairedSample realization)
    + Centered.weightedHighDifferenceBranch (pairedSample realization)
r571PairedCenteredIdentity realization =
  trans
    (round27ScalarIsWeightedRawPair realization)
    (Centered.weightedPairedCommutatorIdentity (pairedSample realization))

------------------------------------------------------------------------
-- 5. The same Taylor data also inhabits the old second-order paired carrier.
------------------------------------------------------------------------

secondOrderSampleFromTaylor :
  (sample : Taylor.MultiplierTaylorPair) →
  (weight plusDerivative minusDerivative : ℚ) →
  SecondOrder.PairedCommutatorSample
secondOrderSampleFromTaylor sample weight plusDerivative minusDerivative =
  SecondOrder.paired-commutator-sample
    weight
    (Taylor.center sample)
    (Taylor.linearIncrement sample)
    (Taylor.plusRemainder sample)
    (Taylor.minusRemainder sample)
    plusDerivative
    minusDerivative

secondOrderPlusTransportIsTaylorPlusValue :
  (sample : Taylor.MultiplierTaylorPair) →
  (weight plusDerivative minusDerivative : ℚ) →
  SecondOrder.plusTransport
    (secondOrderSampleFromTaylor
      sample weight plusDerivative minusDerivative)
  ≡ Taylor.plusValue sample
secondOrderPlusTransportIsTaylorPlusValue sample weight plusDerivative minusDerivative = refl

secondOrderMinusTransportIsTaylorMinusValue :
  (sample : Taylor.MultiplierTaylorPair) →
  (weight plusDerivative minusDerivative : ℚ) →
  SecondOrder.minusTransport
    (secondOrderSampleFromTaylor
      sample weight plusDerivative minusDerivative)
  ≡ Taylor.minusValue sample
secondOrderMinusTransportIsTaylorMinusValue sample weight plusDerivative minusDerivative = refl

existingSecondOrderIdentityOnTaylor :
  (sample : Taylor.MultiplierTaylorPair) →
  (weight plusDerivative minusDerivative : ℚ) →
  SecondOrder.pairedCommutator
    (secondOrderSampleFromTaylor
      sample weight plusDerivative minusDerivative)
  ≡
  SecondOrder.pairedSecondOrderDefect
    (secondOrderSampleFromTaylor
      sample weight plusDerivative minusDerivative)
existingSecondOrderIdentityOnTaylor sample weight plusDerivative minusDerivative =
  SecondOrder.pairedCommutatorSecondOrderIdentity
    (secondOrderSampleFromTaylor
      sample weight plusDerivative minusDerivative)

centeredAndSecondOrderCarriersAgree :
  (realization : R571PairedTaylorRealization) →
  Centered.weightedRawPair (pairedSample realization)
  ≡
  SecondOrder.pairedCommutator
    (secondOrderSampleFromTaylor
      (taylorPair realization)
      (Centered.kernelWeight (pairedSample realization))
      (Centered.gPlus (pairedSample realization))
      (Centered.gMinus (pairedSample realization)))
centeredAndSecondOrderCarriersAgree realization
  rewrite pairedCenterIsTaylorCenter realization
        | pairedPlusIsTaylorPlus realization
        | pairedMinusIsTaylorMinus realization =
  solve
    ( Centered.kernelWeight (pairedSample realization)
    ∷ Taylor.center (taylorPair realization)
    ∷ Taylor.linearIncrement (taylorPair realization)
    ∷ Taylor.plusRemainder (taylorPair realization)
    ∷ Taylor.minusRemainder (taylorPair realization)
    ∷ Centered.gMinus (pairedSample realization)
    ∷ Centered.gPlus (pairedSample realization)
    ∷ [])

r571ScalarIsExistingSecondOrderDefect :
  (realization : R571PairedTaylorRealization) →
  r571Round27Scalar
      (sign realization)
      (scalars realization)
      (shift realization)
      (state realization)
      (output realization)
  ≡
  SecondOrder.pairedSecondOrderDefect
    (secondOrderSampleFromTaylor
      (taylorPair realization)
      (Centered.kernelWeight (pairedSample realization))
      (Centered.gPlus (pairedSample realization))
      (Centered.gMinus (pairedSample realization)))
r571ScalarIsExistingSecondOrderDefect realization =
  trans
    (round27ScalarIsWeightedRawPair realization)
    (trans
      (centeredAndSecondOrderCarriersAgree realization)
      (existingSecondOrderIdentityOnTaylor
        (taylorPair realization)
        (Centered.kernelWeight (pairedSample realization))
        (Centered.gPlus (pairedSample realization))
        (Centered.gMinus (pairedSample realization))))

------------------------------------------------------------------------
-- 6. Quantitative scalar carrier.  A physical realization supplies a
--    nonnegative old PairedSecondMomentSample dominating the exact signed
--    second-order defect.  The old pointwise compiler is then reused verbatim.
------------------------------------------------------------------------

record R571PairedSecondMomentRealization : Set₁ where
  field
    taylor : R571PairedTaylorRealization
    secondMomentSample : Moment.PairedSecondMomentSample

    secondOrderDefectBelowPairedMagnitude :
      SecondOrder.pairedSecondOrderDefect
        (secondOrderSampleFromTaylor
          (taylorPair taylor)
          (Centered.kernelWeight (pairedSample taylor))
          (Centered.gPlus (pairedSample taylor))
          (Centered.gMinus (pairedSample taylor)))
      ≤ Moment.pairedMagnitude secondMomentSample

open R571PairedSecondMomentRealization public

r571ScalarBelowPairedMagnitude :
  (realization : R571PairedSecondMomentRealization) →
  r571Round27Scalar
      (sign (taylor realization))
      (scalars (taylor realization))
      (shift (taylor realization))
      (state (taylor realization))
      (output (taylor realization))
  ≤ Moment.pairedMagnitude (secondMomentSample realization)
r571ScalarBelowPairedMagnitude realization =
  let
    exactIdentity = r571ScalarIsExistingSecondOrderDefect (taylor realization)
  in
  subst
    (λ value → value ≤ Moment.pairedMagnitude (secondMomentSample realization))
    exactIdentity
    (secondOrderDefectBelowPairedMagnitude realization)

r571PointwiseSecondMomentBound :
  (realization : R571PairedSecondMomentRealization) →
  (budget : Moment.PairedSecondMomentBudget) →
  r571Round27Scalar
      (sign (taylor realization))
      (scalars (taylor realization))
      (shift (taylor realization))
      (state (taylor realization))
      (output (taylor realization))
  ≤ Moment.weightedSecondMoment (secondMomentSample realization)
      * Moment.secondMomentCoefficient budget
r571PointwiseSecondMomentBound realization budget =
  ℚP.≤-trans
    (r571ScalarBelowPairedMagnitude realization)
    (Moment.pointwisePairedSecondMomentBound budget
      (secondMomentSample realization))

------------------------------------------------------------------------
-- 7. Publication-facing status / firewalls.
------------------------------------------------------------------------

r571PairedCommutatorCarrierReused : Bool
r571PairedCommutatorCarrierReused = true

r571PairedSecondMomentCarrierReused : Bool
r571PairedSecondMomentCarrierReused = true

r571Round27SameObjectRouteRetained : Bool
r571Round27SameObjectRouteRetained = true

r571HomochiralPairedTaylorCarrierClosed : Bool
r571HomochiralPairedTaylorCarrierClosed = true

r571ExistingPairedSecondOrderIdentityReused : Bool
r571ExistingPairedSecondOrderIdentityReused = true

r571ExistingPairedSecondMomentCompilerReused : Bool
r571ExistingPairedSecondMomentCompilerReused = true

r571PhysicalPairedTaylorSampleClosed : Bool
r571PhysicalPairedTaylorSampleClosed = false

r571PhysicalSecondMomentEnvelopeBudgetClosed : Bool
r571PhysicalSecondMomentEnvelopeBudgetClosed = false

r571FourEnvelopeInequalitiesClosed : Bool
r571FourEnvelopeInequalitiesClosed = false

r571InnerFibreSummedGainClosed : Bool
r571InnerFibreSummedGainClosed = false

r571IncidenceOnlySeparationRouteRetained : Bool
r571IncidenceOnlySeparationRouteRetained = false

r571R568SpacetimeBudgetClosedHere : Bool
r571R568SpacetimeBudgetClosedHere = false

r571ClayPromotion : Bool
r571ClayPromotion = false

r571HomochiralPairedTaylorCarrierClosedIsTrue :
  r571HomochiralPairedTaylorCarrierClosed ≡ true
r571HomochiralPairedTaylorCarrierClosedIsTrue = refl

r571ExistingPairedSecondOrderIdentityReusedIsTrue :
  r571ExistingPairedSecondOrderIdentityReused ≡ true
r571ExistingPairedSecondOrderIdentityReusedIsTrue = refl

r571ExistingPairedSecondMomentCompilerReusedIsTrue :
  r571ExistingPairedSecondMomentCompilerReused ≡ true
r571ExistingPairedSecondMomentCompilerReusedIsTrue = refl

r571PhysicalSecondMomentEnvelopeBudgetClosedIsFalse :
  r571PhysicalSecondMomentEnvelopeBudgetClosed ≡ false
r571PhysicalSecondMomentEnvelopeBudgetClosedIsFalse = refl

r571IncidenceOnlySeparationRouteRetainedIsFalse :
  r571IncidenceOnlySeparationRouteRetained ≡ false
r571IncidenceOnlySeparationRouteRetainedIsFalse = refl

r571R568SpacetimeBudgetClosedHereIsFalse :
  r571R568SpacetimeBudgetClosedHere ≡ false
r571R568SpacetimeBudgetClosedHereIsFalse = refl
