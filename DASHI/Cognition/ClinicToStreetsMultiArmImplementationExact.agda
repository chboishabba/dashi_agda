module DASHI.Cognition.ClinicToStreetsMultiArmImplementationExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.ClinicToStreetsFormulationExperimentExact as Base
import DASHI.Cognition.ClinicToStreetsConsumerCrosswalkExact as Crosswalk
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust

------------------------------------------------------------------------
-- MULTI-ARM + IMPLEMENTATION-FIDELITY CONTINUATION
--
-- The two-arm formulation discriminator is extended only to separate distinct
-- hypotheses: generic extra information, relational/family context, structural
-- context, and patient-authored relevance.  This is an experiment-design
-- surface, not evidence that any arm is clinically superior.
------------------------------------------------------------------------

data FormulationArm : Set where
  symptomIntrapsychicOnly : FormulationArm
  relationalFamilyContext : FormulationArm
  independentlyEvidencedStructuralContext : FormulationArm
  patientAuthoredStructuralRelevance : FormulationArm

arms : List FormulationArm
arms =
  symptomIntrapsychicOnly ∷
  relationalFamilyContext ∷
  independentlyEvidencedStructuralContext ∷
  patientAuthoredStructuralRelevance ∷ []

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

armCount : Nat
armCount = length arms

------------------------------------------------------------------------
-- Implementation is a separate consumer family from representational adequacy.
------------------------------------------------------------------------

data ImplementationConsumer : Set where
  uptakeConsumer : ImplementationConsumer
  fidelityConsumer : ImplementationConsumer
  clinicianBurdenConsumer : ImplementationConsumer
  trainingUseConsumer : ImplementationConsumer
  selectiveUseConsumer : ImplementationConsumer
  documentationUseConsumer : ImplementationConsumer
  implementationContaminationConsumer : ImplementationConsumer

implementationConsumers : List ImplementationConsumer
implementationConsumers =
  uptakeConsumer ∷
  fidelityConsumer ∷
  clinicianBurdenConsumer ∷
  trainingUseConsumer ∷
  selectiveUseConsumer ∷
  documentationUseConsumer ∷
  implementationContaminationConsumer ∷ []

implementationConsumerCount : Nat
implementationConsumerCount = length implementationConsumers

------------------------------------------------------------------------
-- Study layers remain distinct.
------------------------------------------------------------------------

data StudyLayer : Set where
  representationLayer : StudyLayer
  decisionLayer : StudyLayer
  implementationLayer : StudyLayer
  patientOutcomeLayer : StudyLayer
  institutionalPoliticalLayer : StudyLayer

data PromotionRelation : StudyLayer → StudyLayer → Set where
  measuredTransition : ∀ {a b} → PromotionRelation a b

-- No canonical inhabitant is manufactured.  Each promotion requires external
-- evidence appropriate to the target layer.

------------------------------------------------------------------------
-- Factorial discrimination questions.
------------------------------------------------------------------------

data ArmContrast : Set where
  genericContextContrast : ArmContrast
  relationalVsStructuralContrast : ArmContrast
  structuralVsPatientAuthoredContrast : ArmContrast
  structuralIrrelevanceNegativeControl : ArmContrast

contrastQuestion : ArmContrast → String
contrastQuestion genericContextContrast =
  "does adding any contextual information alter the declared consumer relative to symptom/intrapsychic information alone?"
contrastQuestion relationalVsStructuralContrast =
  "holding case facts fixed, do independently evidenced structural coordinates change decisions beyond relational/family context alone?"
contrastQuestion structuralVsPatientAuthoredContrast =
  "does patient-authored relevance change the effect of structural information relative to expert-selected structural context?"
contrastQuestion structuralIrrelevanceNegativeControl =
  "on held-out cases where the structural coordinate is genuinely irrelevant, does contextualisation cease to systematically alter the declared consumer?"

------------------------------------------------------------------------
-- Implementation plan: based on the empirical fact that tool availability and
-- clinical utility do not imply organization-wide uptake or faithful use.
------------------------------------------------------------------------

record ImplementationProtocol : Set where
  constructor implementation-protocol
  field
    denominatorAllEligibleIntakesDeclared : Bool
    uptakeMeasured : Bool
    fidelityInstrumentOrEquivalentDeclared : Bool
    clinicianTrainingExposureMeasured : Bool
    clinicianBurdenAndTimeMeasured : Bool
    selectiveUseByPatientOrClinicianCharacteristicsAudited : Bool
    documentationWithoutDecisionUseAudited : Bool
    crossArmContaminationAudited : Bool
    patientAuthoredRelevanceCapturedSeparately : Bool
    participantAndClinicianAcceptabilitySeparated : Bool
    implementationMeasureCreatesOutcomeBenefit : Bool
    highUptakeCreatesTruth : Bool
    highFidelityCreatesTruth : Bool

open ImplementationProtocol public

canonicalImplementationProtocol : ImplementationProtocol
canonicalImplementationProtocol =
  implementation-protocol
    true true true true true true true true true true
    false false false

------------------------------------------------------------------------
-- Outcome escalation gate.
------------------------------------------------------------------------

record EscalationGate : Set where
  constructor escalation-gate
  field
    decisionEffectMeasuredBeforePatientOutcomePromotion : Bool
    implementationFidelityMeasuredBeforeServiceOutcomePromotion : Bool
    representedActionSeparatedFromActualBehaviour : Bool
    patientDefinedOutcomeRequired : Bool
    materialOutcomeSeparatelyMeasured : Bool
    institutionalIntentRequiresIndependentEvidence : Bool
    counterinsurgencyRequiresIndependentSameObjectEvidence : Bool

canonicalEscalationGate : EscalationGate
canonicalEscalationGate =
  escalation-gate true true true true true true true

------------------------------------------------------------------------
-- Existing experiment owner remains upstream.
------------------------------------------------------------------------

baseExperiment : Base.FormulationExperimentSpec
baseExperiment = Base.canonicalFormulationExperiment

crosswalkBoundary : Crosswalk.ClinicConsumerCrosswalkBoundary
crosswalkBoundary = Crosswalk.canonicalConsumerCrosswalkBoundary

robustFrontierBoundary : Robust.RobustExperimentFrontierBoundary
robustFrontierBoundary = Robust.canonicalRobustExperimentFrontierBoundary

record MultiArmImplementationBoundary : Set where
  constructor multi-arm-implementation-boundary
  field
    baseTwoArmExperimentReused : Bool
    consumerCrosswalkReused : Bool
    robustExperimentBoundaryReused : Bool
    moreContextAutomaticallyBetter : Bool
    patientAuthoredRelevanceCreatesTruth : Bool
    highImplementationFidelityCreatesPatientBenefit : Bool
    structuralLanguageShiftCreatesMaterialAccess : Bool
    treatmentRecommendationShiftCreatesActualBehaviour : Bool
    implementationSuccessCreatesComparativeEfficacy : Bool
    patientDefinedRelevanceReplacesIndependentFactChecking : Bool
    institutionalEffectCreatesIntentFinding : Bool

open MultiArmImplementationBoundary public

canonicalMultiArmImplementationBoundary : MultiArmImplementationBoundary
canonicalMultiArmImplementationBoundary =
  multi-arm-implementation-boundary
    true true true
    false false false false false false false false

------------------------------------------------------------------------
-- Explicit bad-promotion propositions.
------------------------------------------------------------------------

data MoreContextProvesBetter : Set where
data PatientAuthorshipProvesTruth : Set where
data FidelityProvesOutcomeBenefit : Set where
data StructuralLanguageProvesMaterialAccess : Set where

moreContextDoesNotProveBetter : MoreContextProvesBetter → ⊥
moreContextDoesNotProveBetter ()

patientAuthorshipDoesNotProveTruth : PatientAuthorshipProvesTruth → ⊥
patientAuthorshipDoesNotProveTruth ()

fidelityDoesNotProveOutcomeBenefit : FidelityProvesOutcomeBenefit → ⊥
fidelityDoesNotProveOutcomeBenefit ()

structuralLanguageDoesNotProveMaterialAccess : StructuralLanguageProvesMaterialAccess → ⊥
structuralLanguageDoesNotProveMaterialAccess ()
