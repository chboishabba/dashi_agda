module DASHI.Governance.MedicalCannabisContaminantSemanticEpistemicExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.SemanticEpistemicInterpretationExact as SemEpi
import DASHI.Governance.SituatedDissentDeceptionAssayExact as GovernanceAssay

------------------------------------------------------------------------
-- CONDITIONAL MEDICAL-CANNABIS CONTAMINANT FIXTURE
--
-- This module does not assert that any particular medical-cannabis product is
-- contaminated.  It asks what follows GIVEN a validated contaminant detection
-- in a released medical-cannabis batch.
--
-- The local observation licenses questions/candidate meanings at several
-- scales.  It does not identify a unique system cause, and in particular does
-- not by itself prove a claim about capitalism or any other political economy.
------------------------------------------------------------------------

data CannabisObservation : Set where
  validatedReleasedBatchContaminantDetection : CannabisObservation

data CannabisMeaning : Set where
  localProductSafetyMeaning
  possibleProductionControlFailure
  possibleTestingOrReleaseControlFailure
  possibleRegulatoryOversightGap
  possibleEnforcementCapacityGap
  possiblePrivateIncentiveMisalignment
  possibleExternalityShiftToPatient
  possibleStructuralCapitalistContribution
  : CannabisMeaning

meaningScale : CannabisMeaning → SemEpi.InterpretationScale
meaningScale localProductSafetyMeaning = SemEpi.localObservationScale
meaningScale possibleProductionControlFailure = SemEpi.operationalProcessScale
meaningScale possibleTestingOrReleaseControlFailure = SemEpi.operationalProcessScale
meaningScale possibleRegulatoryOversightGap = SemEpi.institutionalGovernanceScale
meaningScale possibleEnforcementCapacityGap = SemEpi.institutionalGovernanceScale
meaningScale possiblePrivateIncentiveMisalignment = SemEpi.incentiveStructureScale
meaningScale possibleExternalityShiftToPatient = SemEpi.incentiveStructureScale
meaningScale possibleStructuralCapitalistContribution = SemEpi.politicalEconomyScale

------------------------------------------------------------------------
-- Forward candidate licence.  Detection licenses investigation of these
-- meanings; it does not establish them as causes.
------------------------------------------------------------------------

data DetectionCandidate : CannabisObservation → CannabisMeaning → Set where
  localSafetyCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      localProductSafetyMeaning
  productionControlCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possibleProductionControlFailure
  releaseControlCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possibleTestingOrReleaseControlFailure
  oversightCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possibleRegulatoryOversightGap
  enforcementCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possibleEnforcementCapacityGap
  incentiveCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possiblePrivateIncentiveMisalignment
  externalityCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possibleExternalityShiftToPatient
  capitalismCandidate :
    DetectionCandidate
      validatedReleasedBatchContaminantDetection
      possibleStructuralCapitalistContribution

------------------------------------------------------------------------
-- Backward evidential obligations.  Stronger interpretations require richer
-- evidence.  Structural political-economy attribution requires evidence about
-- recurrence, mediation, institutional comparison and market/ownership form;
-- one contaminated batch is not enough.
------------------------------------------------------------------------

data Requires : CannabisMeaning → SemEpi.SystemEvidenceDemand → Set where
  localNeedsAssayValidation :
    Requires localProductSafetyMeaning SemEpi.assayValidationDemand

  productionNeedsTraceability :
    Requires possibleProductionControlFailure SemEpi.processTraceabilityDemand
  productionNeedsRecurrenceOrProcessEvidence :
    Requires possibleProductionControlFailure SemEpi.recurrenceDemand

  releaseNeedsAssayValidation :
    Requires possibleTestingOrReleaseControlFailure SemEpi.assayValidationDemand
  releaseNeedsReleaseControl :
    Requires possibleTestingOrReleaseControlFailure SemEpi.releaseControlDemand

  oversightNeedsRule :
    Requires possibleRegulatoryOversightGap SemEpi.regulatoryRuleDemand
  oversightNeedsEnforcementPractice :
    Requires possibleRegulatoryOversightGap SemEpi.enforcementPracticeDemand
  oversightNeedsRecurrence :
    Requires possibleRegulatoryOversightGap SemEpi.recurrenceDemand

  enforcementNeedsPractice :
    Requires possibleEnforcementCapacityGap SemEpi.enforcementPracticeDemand
  enforcementNeedsRecurrence :
    Requires possibleEnforcementCapacityGap SemEpi.recurrenceDemand

  incentiveNeedsStructure :
    Requires possiblePrivateIncentiveMisalignment SemEpi.incentiveStructureDemand
  incentiveNeedsMediation :
    Requires possiblePrivateIncentiveMisalignment SemEpi.causalMediationDemand
  incentiveNeedsRecurrence :
    Requires possiblePrivateIncentiveMisalignment SemEpi.recurrenceDemand

  externalityNeedsAllocation :
    Requires possibleExternalityShiftToPatient SemEpi.externalityAllocationDemand
  externalityNeedsMediation :
    Requires possibleExternalityShiftToPatient SemEpi.causalMediationDemand

  capitalismNeedsRecurrence :
    Requires possibleStructuralCapitalistContribution SemEpi.recurrenceDemand
  capitalismNeedsIncentiveStructure :
    Requires possibleStructuralCapitalistContribution SemEpi.incentiveStructureDemand
  capitalismNeedsOwnershipMarketStructure :
    Requires possibleStructuralCapitalistContribution SemEpi.ownershipMarketStructureDemand
  capitalismNeedsExternalityAllocation :
    Requires possibleStructuralCapitalistContribution SemEpi.externalityAllocationDemand
  capitalismNeedsCausalMediation :
    Requires possibleStructuralCapitalistContribution SemEpi.causalMediationDemand
  capitalismNeedsComparativeInstitutions :
    Requires possibleStructuralCapitalistContribution SemEpi.comparativeInstitutionalDemand
  capitalismNeedsCounterfactualInstitutions :
    Requires possibleStructuralCapitalistContribution SemEpi.counterfactualInstitutionalDemand
  capitalismNeedsGovernanceEvidence :
    Requires possibleStructuralCapitalistContribution SemEpi.enforcementPracticeDemand

problem : SemEpi.SemanticEpistemicProblem
problem = SemEpi.semanticEpistemicProblem
  CannabisObservation
  CannabisMeaning
  DetectionCandidate
  meaningScale
  Requires
  (λ _ → "conditional validated contaminant detection in a released medical-cannabis batch")
  (λ
    { localProductSafetyMeaning → "local product-safety interpretation"
    ; possibleProductionControlFailure → "candidate production/process control failure"
    ; possibleTestingOrReleaseControlFailure → "candidate testing/release-control failure"
    ; possibleRegulatoryOversightGap → "candidate regulatory oversight gap"
    ; possibleEnforcementCapacityGap → "candidate enforcement-capacity gap"
    ; possiblePrivateIncentiveMisalignment → "candidate private incentive misalignment"
    ; possibleExternalityShiftToPatient → "candidate cost/risk externalisation toward patient"
    ; possibleStructuralCapitalistContribution → "candidate structural capitalist political-economy contribution"
    })
  "candidate system meaning is not system-causal proof; stronger levels require their backward evidence demands"

canonicalForwardMeanings :
  List (SemEpi.CandidateSystemMeaning problem validatedReleasedBatchContaminantDetection)
canonicalForwardMeanings =
    SemEpi.candidateSystemMeaning localProductSafetyMeaning localSafetyCandidate
      "direct local safety meaning" "does not identify upstream system cause"
  ∷ SemEpi.candidateSystemMeaning possibleProductionControlFailure productionControlCandidate
      "process-control hypothesis" "candidate only"
  ∷ SemEpi.candidateSystemMeaning possibleTestingOrReleaseControlFailure releaseControlCandidate
      "release-control hypothesis" "candidate only"
  ∷ SemEpi.candidateSystemMeaning possibleRegulatoryOversightGap oversightCandidate
      "governance hypothesis" "candidate only"
  ∷ SemEpi.candidateSystemMeaning possibleEnforcementCapacityGap enforcementCandidate
      "enforcement hypothesis" "candidate only"
  ∷ SemEpi.candidateSystemMeaning possiblePrivateIncentiveMisalignment incentiveCandidate
      "incentive hypothesis" "candidate only"
  ∷ SemEpi.candidateSystemMeaning possibleExternalityShiftToPatient externalityCandidate
      "externality hypothesis" "candidate only"
  ∷ SemEpi.candidateSystemMeaning possibleStructuralCapitalistContribution capitalismCandidate
      "political-economy hypothesis" "requires structural/comparative evidence"
  ∷ []

capitalismBackwardDemands : List SemEpi.SystemEvidenceDemand
capitalismBackwardDemands =
    SemEpi.recurrenceDemand
  ∷ SemEpi.incentiveStructureDemand
  ∷ SemEpi.ownershipMarketStructureDemand
  ∷ SemEpi.externalityAllocationDemand
  ∷ SemEpi.causalMediationDemand
  ∷ SemEpi.enforcementPracticeDemand
  ∷ SemEpi.comparativeInstitutionalDemand
  ∷ SemEpi.counterfactualInstitutionalDemand
  ∷ []

------------------------------------------------------------------------
-- Nonfactorability: the same contamination observation can coexist with
-- different fine-grained system causes.  Therefore the observation alone
-- cannot recover the governance/political-economy explanation.
------------------------------------------------------------------------

data FineSystemState : Set where
  isolatedProducerDeviation
  weakOversightAndEnforcement
  incentiveExternalisationPattern
  : FineSystemState

data CoarseContaminationSurface : Set where
  sameValidatedDetection : CoarseContaminationSurface

data FineSystemExplanation : Set where
  producerLocalExplanation
  governanceCapacityExplanation
  marketIncentiveExplanation
  : FineSystemExplanation

coarseObservation : FineSystemState → CoarseContaminationSurface
coarseObservation _ = sameValidatedDetection

fineExplanation : FineSystemState → FineSystemExplanation
fineExplanation isolatedProducerDeviation = producerLocalExplanation
fineExplanation weakOversightAndEnforcement = governanceCapacityExplanation
fineExplanation incentiveExternalisationPattern = marketIncentiveExplanation

sameObservationDifferentSystemExplanation :
  INF.NonFactorabilityWitness coarseObservation fineExplanation
sameObservationDifferentSystemExplanation =
  INF.nonFactorabilityWitness
    isolatedProducerDeviation
    incentiveExternalisationPattern
    refl
    (λ ())

contaminationObservationCannotRecoverSystemCause :
  INF.FactorsThrough coarseObservation fineExplanation → ⊥
contaminationObservationCannotRecoverSystemCause =
  INF.witnessRulesOutEveryFlatFactorisation
    sameObservationDifferentSystemExplanation

------------------------------------------------------------------------
-- Existing governance assay is retained as an independent structural boundary:
-- a visible surface does not automatically recover decision/system integrity.
------------------------------------------------------------------------

governanceBoundary : GovernanceAssay.SituatedDissentDeceptionBoundary
governanceBoundary = GovernanceAssay.canonicalSituatedDissentDeceptionBoundary

record MedicalCannabisSemanticEpistemicBoundary : Set where
  constructor medicalCannabisSemanticEpistemicBoundary
  field
    validatedDetectionCanRaiseGovernanceQuestions : Bool
    validatedDetectionCanRaiseGovernanceQuestionsIsTrue :
      validatedDetectionCanRaiseGovernanceQuestions ≡ true
    validatedDetectionProvesCapitalistCausation : Bool
    validatedDetectionProvesCapitalistCausationIsFalse :
      validatedDetectionProvesCapitalistCausation ≡ false
    sameContaminationObservationCanHideDifferentSystemCauses : Bool
    sameContaminationObservationCanHideDifferentSystemCausesIsTrue :
      sameContaminationObservationCanHideDifferentSystemCauses ≡ true
    politicalEconomyInterpretationRequiresComparativeEvidence : Bool
    politicalEconomyInterpretationRequiresComparativeEvidenceIsTrue :
      politicalEconomyInterpretationRequiresComparativeEvidence ≡ true
    politicalEconomyInterpretationRequiresCausalMediationEvidence : Bool
    politicalEconomyInterpretationRequiresCausalMediationEvidenceIsTrue :
      politicalEconomyInterpretationRequiresCausalMediationEvidence ≡ true

canonicalMedicalCannabisSemanticEpistemicBoundary :
  MedicalCannabisSemanticEpistemicBoundary
canonicalMedicalCannabisSemanticEpistemicBoundary =
  medicalCannabisSemanticEpistemicBoundary
    true refl
    false refl
    true refl
    true refl
    true refl
