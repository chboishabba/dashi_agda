module DASHI.Governance.SituatedCortisolAssayGluingExact where

-- Original DASHI finite gluing condition: different assay readouts must
-- have a common physiological-history witness under known kernels.
-- Not a computed sheaf cohomology class or diagnosis of contamination.
-- Hair incorporation, urine excretion, saliva delay and calibration need
-- specific measurement kernels as in SituatedCortisolScaleIndexedAssayExact.
open import DASHI.Core.Prelude
import DASHI.Governance.SituatedCortisolScaleIndexedAssayExact as Scale

data TwoPointHistory : Set where
  earlyPulse latePulse noPulse : TwoPointHistory

earlyReadout : TwoPointHistory → Nat
earlyReadout earlyPulse = 2
earlyReadout latePulse = 0
earlyReadout noPulse = 0

lateReadout : TwoPointHistory → Nat
lateReadout earlyPulse = 0
lateReadout latePulse = 2
lateReadout noPulse = 0

integratedReadout : TwoPointHistory → Nat
integratedReadout h = earlyReadout h + lateReadout h

record JointAssayExplanation (saliva hair : Nat) : Set where
  constructor joint-assay-explanation
  field
    selectedHistory : TwoPointHistory
    salivaCorrespondence : earlyReadout selectedHistory ≡ saliva
    integratedCorrespondence : integratedReadout selectedHistory ≡ hair
open JointAssayExplanation public

consistentEarlyPulse : JointAssayExplanation 2 2
consistentEarlyPulse = joint-assay-explanation earlyPulse refl refl

-- Under this exact calibrated two-point toy forward operator, an early
-- saliva reading of 2 cannot be glued to a zero integrated reading.
-- Without the real operator/lag/error model, a disagreement is only an
-- unresolved residual, NOT evidence of assay fraud, steroid use or disease.
noCommonHistoryForContradictoryReadings :
  JointAssayExplanation 2 0 → ⊥
noCommonHistoryForContradictoryReadings
  (joint-assay-explanation earlyPulse refl ())
noCommonHistoryForContradictoryReadings
  (joint-assay-explanation latePulse () _)
noCommonHistoryForContradictoryReadings
  (joint-assay-explanation noPulse () _)

-- Same integrated readout, different point readout. A cross-scale
-- projection from integrated readings to acute points cannot be inferred.
sameLongWindowDifferentPoint :
  integratedReadout earlyPulse ≡ integratedReadout latePulse
  × (earlyReadout earlyPulse ≡ earlyReadout latePulse → ⊥)
sameLongWindowDifferentPoint = refl , (λ ())

record EmpiricalCrossScaleWeld : Set₁ where
  field
    salivaProtocolSourceVerified : Set
    hairProtocolSourceVerified : Set
    individualSegmentGrowthValidated : Set
    temporalLagAndWeightsValidated : Set
    matrixConversionValidated : Set
    uncertaintyAndContaminationAlternativesReviewed : Set
    commonPersonAndSamplingPeriodVerified : Set

-- The above record deliberately has no canonical inhabitant. A shared
-- history that fits two *toy* readings does not instantiate this receipt.
