module DASHI.Physics.Closure.NSTriadKNR571OppositeShiftSecondMomentRealizationExact where

------------------------------------------------------------------------
-- EXACT TWO-SHIFT R571 -> AUG-5 SECOND-ORDER -> ABSOLUTE-MAGNITUDE SPLICE
--
-- This owner uses the physically correct two-shift Round27 scalar from the
-- opposite-shift owner, identifies it with the old paired second-order defect,
-- and then applies the generic absolute-magnitude bridge.
--
-- The only quantitative input introduced here is a nonnegative scalar
-- displacement magnitude.  The four Taylor/derivative envelope inequalities
-- remain external in the existing PairedSecondMomentBudget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as Legacy
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorExact as Opp
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor
import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Centered
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondOrderExact as Second
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNLuoPairedSecondOrderAbsoluteMagnitudeBridgeExact as Abs

oppositeShiftTaylorPair :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement center : Z3.FourierMode) →
  (linearModel : ℚ) →
  Taylor.MultiplierTaylorPair
oppositeShiftTaylorPair sign S displacement center linearModel =
  Legacy.radialTaylorPair
    sign S center
    (Opp.plusMode center displacement)
    (Opp.minusMode center displacement)
    linearModel

oppositeShiftSecondOrderSample :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  (linearModel : ℚ) →
  Second.PairedCommutatorSample
oppositeShiftSecondOrderSample
  weight sign S displacement state center linearModel =
  Legacy.secondOrderSampleFromTaylor
    (oppositeShiftTaylorPair sign S displacement center linearModel)
    weight
    (R27.stateCoefficient state (Opp.plusMode center displacement))
    (R27.stateCoefficient state (Opp.minusMode center displacement))

centeredRawPairIsSecondOrderPaired :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  (linearModel : ℚ) →
  Centered.weightedRawPair
    (Opp.oppositeShiftPairedSample weight sign S displacement state center)
  ≡
  Second.pairedCommutator
    (oppositeShiftSecondOrderSample
      weight sign S displacement state center linearModel)
centeredRawPairIsSecondOrderPaired
  weight sign S displacement state center linearModel
  rewrite Legacy.radialTaylorPlusValueExact
    sign S center
      (Opp.plusMode center displacement)
      (Opp.minusMode center displacement)
      linearModel
        | Legacy.radialTaylorMinusValueExact
    sign S center
      (Opp.plusMode center displacement)
      (Opp.minusMode center displacement)
      linearModel =
  solve
    ( weight
    ∷ Opp.radialSymbol sign S center
    ∷ Opp.radialSymbol sign S (Opp.plusMode center displacement)
    ∷ Opp.radialSymbol sign S (Opp.minusMode center displacement)
    ∷ R27.stateCoefficient state (Opp.plusMode center displacement)
    ∷ R27.stateCoefficient state (Opp.minusMode center displacement)
    ∷ linearModel
    ∷ [])

oppositeShiftScalarIsSecondOrderDefect :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  (linearModel : ℚ) →
  Opp.oppositeShiftRound27Scalar weight sign S displacement state center
  ≡
  Second.pairedSecondOrderDefect
    (oppositeShiftSecondOrderSample
      weight sign S displacement state center linearModel)
oppositeShiftScalarIsSecondOrderDefect
  weight sign S displacement state center linearModel =
  trans
    (Opp.oppositeShiftRound27ScalarIsWeightedRawPair
      weight sign S displacement state center)
    (trans
      (centeredRawPairIsSecondOrderPaired
        weight sign S displacement state center linearModel)
      (Second.pairedCommutatorSecondOrderIdentity
        (oppositeShiftSecondOrderSample
          weight sign S displacement state center linearModel)))

oppositeShiftAbsoluteMagnitudeSample :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  (linearModel stepMagnitude : ℚ) →
  0ℚ ≤ stepMagnitude →
  Moment.PairedSecondMomentSample
oppositeShiftAbsoluteMagnitudeSample
  weight sign S displacement state center linearModel stepMagnitude stepNN =
  Abs.absoluteMagnitudeSample
    stepMagnitude stepNN
    (oppositeShiftSecondOrderSample
      weight sign S displacement state center linearModel)

oppositeShiftScalarBelowAbsoluteMagnitude :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  (linearModel stepMagnitude : ℚ) →
  (stepNN : 0ℚ ≤ stepMagnitude) →
  Opp.oppositeShiftRound27Scalar weight sign S displacement state center
  ≤
  Moment.pairedMagnitude
    (oppositeShiftAbsoluteMagnitudeSample
      weight sign S displacement state center linearModel stepMagnitude stepNN)
oppositeShiftScalarBelowAbsoluteMagnitude
  weight sign S displacement state center linearModel stepMagnitude stepNN
  rewrite oppositeShiftScalarIsSecondOrderDefect
    weight sign S displacement state center linearModel =
  Abs.signedSecondOrderDefectBelowAbsoluteMagnitude
    stepMagnitude stepNN
    (oppositeShiftSecondOrderSample
      weight sign S displacement state center linearModel)

oppositeShiftPointwiseSecondMomentBound :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  (linearModel stepMagnitude : ℚ) →
  (stepNN : 0ℚ ≤ stepMagnitude) →
  (budget : Moment.PairedSecondMomentBudget) →
  Opp.oppositeShiftRound27Scalar weight sign S displacement state center
  ≤
  Moment.weightedSecondMoment
    (oppositeShiftAbsoluteMagnitudeSample
      weight sign S displacement state center linearModel stepMagnitude stepNN)
    * Moment.secondMomentCoefficient budget
oppositeShiftPointwiseSecondMomentBound
  weight sign S displacement state center linearModel stepMagnitude stepNN budget =
  Data.Rational.Properties.≤-trans
    (oppositeShiftScalarBelowAbsoluteMagnitude
      weight sign S displacement state center linearModel stepMagnitude stepNN)
    (Moment.pointwisePairedSecondMomentBound budget
      (oppositeShiftAbsoluteMagnitudeSample
        weight sign S displacement state center linearModel stepMagnitude stepNN))

r571OppositeShiftSecondOrderIdentityClosed : Bool
r571OppositeShiftSecondOrderIdentityClosed = true

r571OppositeShiftAbsoluteMagnitudeBridgeClosed : Bool
r571OppositeShiftAbsoluteMagnitudeBridgeClosed = true

r571OppositeShiftPhysicalEnvelopeBudgetClosed : Bool
r571OppositeShiftPhysicalEnvelopeBudgetClosed = false

r571OppositeShiftSecondMomentClosesR568 : Bool
r571OppositeShiftSecondMomentClosesR568 = false
