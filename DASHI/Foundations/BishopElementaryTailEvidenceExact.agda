module DASHI.Foundations.BishopElementaryTailEvidenceExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary

------------------------------------------------------------------------
-- Evidence-bearing completion of the Bishop elementary-tail interface.
--
-- The pre-existing `BishopConfiguredElementaryTailProofs` record fixes the
-- proposition families to be proved, but its fields have codomain `Set`; it
-- does not contain inhabitants of those propositions. This sibling record is
-- the actual proof object consumed by physical trigonometric estimates.
------------------------------------------------------------------------

record BishopConfiguredElementaryTailEvidence
    {dataSet : Elementary.BishopElementaryPowerSeriesData}
    (configuration : Elementary.BishopConfiguredElementaryTailProofs dataSet)
    : Set₁ where
  field
    sineTermMagnitudeDecreasingEvidence :
      (point : Bishop.Bishopℝ) (index : Nat) →
      Elementary.InConfiguredRadius configuration point →
      Elementary.sineTermMagnitudeDecreasing
        configuration point index
        (λ proof → proof)

    cosineTermMagnitudeDecreasingEvidence :
      (point : Bishop.Bishopℝ) (index : Nat) →
      Elementary.InConfiguredRadius configuration point →
      Elementary.cosineTermMagnitudeDecreasing
        configuration point index
        (λ proof → proof)

    sineCubicSignedRemainderEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.sineCubicSignedRemainder configuration point inside

    sineQuinticSignedRemainderEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.sineQuinticSignedRemainder configuration point inside

    cosineQuadraticSignedRemainderEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.cosineQuadraticSignedRemainder configuration point inside

    cosineQuarticSignedRemainderEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.cosineQuarticSignedRemainder configuration point inside

    sineCubicFirstOmittedBoundEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.sineCubicFirstOmittedBound configuration point inside

    sineQuinticFirstOmittedBoundEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.sineQuinticFirstOmittedBound configuration point inside

    cosineQuadraticFirstOmittedBoundEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.cosineQuadraticFirstOmittedBound configuration point inside

    cosineQuarticFirstOmittedBoundEvidence :
      (point : Bishop.Bishopℝ) →
      (inside : Elementary.InConfiguredRadius configuration point) →
      Elementary.cosineQuarticFirstOmittedBound configuration point inside

    negativeLogOneMinusBoundEvidence :
      (point : Bishop.Bishopℝ) →
      (inUnit : Elementary.InOpenUnitInterval dataSet point) →
      Elementary.negativeLogOneMinusBound configuration point inUnit

    positiveExponentialTailEvidence :
      (point : Bishop.Bishopℝ) →
      Elementary.positiveExponentialTail configuration point

    logarithmMonotoneOnPositiveEvidence :
      Elementary.logarithmMonotoneOnPositive configuration

    logarithmExponentialInverseEvidence :
      Elementary.logarithmExponentialInverse configuration

open BishopConfiguredElementaryTailEvidence public

bishopElementaryTailEvidenceInterfaceLevel : ProofLevel
bishopElementaryTailEvidenceInterfaceLevel = machineChecked

physicalBishopElementaryTailEvidenceInputsLevel : ProofLevel
physicalBishopElementaryTailEvidenceInputsLevel = conditional
