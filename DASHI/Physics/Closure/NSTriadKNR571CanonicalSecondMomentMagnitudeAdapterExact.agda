module DASHI.Physics.Closure.NSTriadKNR571CanonicalSecondMomentMagnitudeAdapterExact where

------------------------------------------------------------------------
-- THIN CONSTRUCTOR INTO THE EXISTING R571 SECOND-MOMENT RECORD.
--
-- The signed R571 scalar is already identified with the old Aug-5 second-order
-- defect.  The generic absolute-magnitude bridge now supplies the nonnegative
-- PairedSecondMomentSample canonically.  Therefore downstream code no longer
-- needs to assume `secondOrderDefectBelowPairedMagnitude` independently.
--
-- The displacement and its nonnegativity remain explicit; the four physical
-- Taylor/envelope inequalities remain exactly where they belong in the old
-- PairedSecondMomentBudget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Centered
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondOrderExact as Second
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNLuoPairedSecondOrderAbsoluteMagnitudeBridgeExact as Abs
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R

r571SecondOrderSample :
  R.R571PairedTaylorRealization → Second.PairedCommutatorSample
r571SecondOrderSample realization =
  R.secondOrderSampleFromTaylor
    (R.taylorPair realization)
    (Centered.kernelWeight (R.pairedSample realization))
    (Centered.gPlus (R.pairedSample realization))
    (Centered.gMinus (R.pairedSample realization))

canonicalR571SecondMomentSample :
  (realization : R.R571PairedTaylorRealization) →
  (displacement : ℚ) →
  0ℚ ≤ displacement →
  Moment.PairedSecondMomentSample
canonicalR571SecondMomentSample realization displacement displacementNN =
  Abs.absoluteMagnitudeSample
    displacement displacementNN (r571SecondOrderSample realization)

canonicalR571SecondMomentRealization :
  (realization : R.R571PairedTaylorRealization) →
  (displacement : ℚ) →
  (displacementNN : 0ℚ ≤ displacement) →
  R.R571PairedSecondMomentRealization
canonicalR571SecondMomentRealization realization displacement displacementNN =
  record
    { taylor = realization
    ; secondMomentSample =
        canonicalR571SecondMomentSample realization displacement displacementNN
    ; secondOrderDefectBelowPairedMagnitude =
        Abs.signedSecondOrderDefectBelowAbsoluteMagnitude
          displacement displacementNN (r571SecondOrderSample realization)
    }

canonicalR571PointwiseSecondMomentBound :
  (realization : R.R571PairedTaylorRealization) →
  (displacement : ℚ) →
  (displacementNN : 0ℚ ≤ displacement) →
  (budget : Moment.PairedSecondMomentBudget) →
  R.r571Round27Scalar
      (R.sign realization)
      (R.scalars realization)
      (R.shift realization)
      (R.state realization)
      (R.output realization)
  ≤ Moment.weightedSecondMoment
      (canonicalR571SecondMomentSample realization displacement displacementNN)
      * Moment.secondMomentCoefficient budget
canonicalR571PointwiseSecondMomentBound
  realization displacement displacementNN budget =
  R.r571PointwiseSecondMomentBound
    (canonicalR571SecondMomentRealization
      realization displacement displacementNN)
    budget

r571CanonicalSecondMomentMagnitudeConstructorClosed : Bool
r571CanonicalSecondMomentMagnitudeConstructorClosed = true

r571CanonicalAdapterIntroducesPhysicalEnvelopeEstimate : Bool
r571CanonicalAdapterIntroducesPhysicalEnvelopeEstimate = false

r571CanonicalAdapterClosesR568 : Bool
r571CanonicalAdapterClosesR568 = false
