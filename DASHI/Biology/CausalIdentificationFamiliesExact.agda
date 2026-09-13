module DASHI.Biology.CausalIdentificationFamiliesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.MultiscaleCausalProvenanceProofSearchRouterExact as Router
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Evidence

------------------------------------------------------------------------
-- CAUSAL IDENTIFICATION FAMILIES
--
-- Reusable obligation-relative schemas for common causal-identification routes.
-- These are not a universal hierarchy of study designs and none manufactures a
-- causal effect by itself.  Each schema states which design-specific receipts
-- must be paid before the generic multiscale causal router may use that family
-- as its IdentificationAssumption.
------------------------------------------------------------------------

data CausalIdentificationFamily : Set where
  randomisedPerturbation : CausalIdentificationFamily
  adjustedObservationalComparison : CausalIdentificationFamily
  longitudinalBeforeAfter : CausalIdentificationFamily
  mechanisticMediation : CausalIdentificationFamily
  lineageGeneticPerturbation : CausalIdentificationFamily
  neuralPerturbationReadout : CausalIdentificationFamily

------------------------------------------------------------------------
-- Randomised perturbation.
------------------------------------------------------------------------

record RandomisedPerturbationReceipt : Set where
  constructor randomised-perturbation-receipt
  field
    allocationReference comparatorReference fidelityReference : String
    outcomeMeasurementReference interferenceReference : String

    sourceAssignmentRandomised : Bool
    sourceAssignmentRandomisedIsTrue : sourceAssignmentRandomised ≡ true
    comparatorDeclared : Bool
    comparatorDeclaredIsTrue : comparatorDeclared ≡ true
    implementationFidelityTracked : Bool
    implementationFidelityTrackedIsTrue : implementationFidelityTracked ≡ true
    interferenceOrSpilloverHandled : Bool
    interferenceOrSpilloverHandledIsTrue : interferenceOrSpilloverHandled ≡ true

open RandomisedPerturbationReceipt public

------------------------------------------------------------------------
-- Adjusted observational comparison.
--
-- Measured-covariate adjustment is explicit, but residual/unmeasured
-- confounding is not declared absent merely because adjustment was performed.
------------------------------------------------------------------------

record AdjustedObservationalReceipt : Set where
  constructor adjusted-observational-receipt
  field
    exposureReference outcomeReference covariateReference : String
    adjustmentModelReference sensitivityReference : String

    temporalOrderingDeclared : Bool
    temporalOrderingDeclaredIsTrue : temporalOrderingDeclared ≡ true
    measuredCovariateSetPrespecified : Bool
    measuredCovariateSetPrespecifiedIsTrue : measuredCovariateSetPrespecified ≡ true
    adjustmentProcedureSpecified : Bool
    adjustmentProcedureSpecifiedIsTrue : adjustmentProcedureSpecified ≡ true
    residualConfoundingAcknowledged : Bool
    residualConfoundingAcknowledgedIsTrue : residualConfoundingAcknowledged ≡ true

open AdjustedObservationalReceipt public

------------------------------------------------------------------------
-- Longitudinal before/after.
--
-- Repeated observation pays chronology and within-lineage/subject continuity,
-- not causation by temporal order alone.
------------------------------------------------------------------------

record LongitudinalBeforeAfterReceipt : Set where
  constructor longitudinal-before-after-receipt
  field
    subjectOrLineageReference baselineReference followupReference : String
    attritionReference timeVaryingConfounderReference : String

    sameUnitTracked : Bool
    sameUnitTrackedIsTrue : sameUnitTracked ≡ true
    baselinePrecedesFollowup : Bool
    baselinePrecedesFollowupIsTrue : baselinePrecedesFollowup ≡ true
    attritionHandled : Bool
    attritionHandledIsTrue : attritionHandled ≡ true
    timeVaryingConfoundingHandled : Bool
    timeVaryingConfoundingHandledIsTrue : timeVaryingConfoundingHandled ≡ true

open LongitudinalBeforeAfterReceipt public

------------------------------------------------------------------------
-- Mechanistic mediation.
--
-- Source->mediator and mediator->target must be separately supported; a mediator
-- correlated with both endpoints is not automatically a causal mechanism.
------------------------------------------------------------------------

record MechanisticMediationReceipt : Set where
  constructor mechanistic-mediation-receipt
  field
    mediatorReference sourceMediatorReference mediatorTargetReference : String
    directPathReference alternativePathReference : String

    mediatorMeasured : Bool
    mediatorMeasuredIsTrue : mediatorMeasured ≡ true
    sourceToMediatorSupported : Bool
    sourceToMediatorSupportedIsTrue : sourceToMediatorSupported ≡ true
    mediatorToTargetSupported : Bool
    mediatorToTargetSupportedIsTrue : mediatorToTargetSupported ≡ true
    directAndAlternativePathsAudited : Bool
    directAndAlternativePathsAuditedIsTrue : directAndAlternativePathsAudited ≡ true

open MechanisticMediationReceipt public

------------------------------------------------------------------------
-- Lineage / genetic perturbation.
------------------------------------------------------------------------

record LineageGeneticPerturbationReceipt : Set where
  constructor lineage-genetic-perturbation-receipt
  field
    molecularPerturbationReference genotypeVerificationReference : String
    lineageProvenanceReference offTargetReference phenotypeReference : String

    perturbationMolecularlyVerified : Bool
    perturbationMolecularlyVerifiedIsTrue : perturbationMolecularlyVerified ≡ true
    lineageProvenanceTracked : Bool
    lineageProvenanceTrackedIsTrue : lineageProvenanceTracked ≡ true
    offTargetOrBackgroundHandled : Bool
    offTargetOrBackgroundHandledIsTrue : offTargetOrBackgroundHandled ≡ true
    phenotypeMeasuredSeparately : Bool
    phenotypeMeasuredSeparatelyIsTrue : phenotypeMeasuredSeparately ≡ true

open LineageGeneticPerturbationReceipt public

------------------------------------------------------------------------
-- Neural perturbation plus behavioural/memory readout.
--
-- Neural manipulation, observation modality, effector/body path and cognitive
-- readout are retained as separate coordinates.  No neural measurement is
-- promoted to thought/intent identity.
------------------------------------------------------------------------

record NeuralPerturbationReadoutReceipt : Set where
  constructor neural-perturbation-readout-receipt
  field
    neuralPerturbationReference neuralMeasurementReference : String
    effectorOrBehaviourReference cognitiveReadoutReference : String
    specificityReference : String

    perturbationSpecificityTracked : Bool
    perturbationSpecificityTrackedIsTrue : perturbationSpecificityTracked ≡ true
    neuralReadoutCalibrated : Bool
    neuralReadoutCalibratedIsTrue : neuralReadoutCalibrated ≡ true
    effectorOrBehaviourPathReceipted : Bool
    effectorOrBehaviourPathReceiptedIsTrue : effectorOrBehaviourPathReceipted ≡ true
    cognitiveOutcomeMeasuredSeparately : Bool
    cognitiveOutcomeMeasuredSeparatelyIsTrue : cognitiveOutcomeMeasuredSeparately ≡ true

open NeuralPerturbationReadoutReceipt public

------------------------------------------------------------------------
-- Family-indexed identification receipt.
------------------------------------------------------------------------

data IdentificationFamilyReceipt : CausalIdentificationFamily → Set where
  randomisedReceipt :
    RandomisedPerturbationReceipt →
    IdentificationFamilyReceipt randomisedPerturbation

  adjustedReceipt :
    AdjustedObservationalReceipt →
    IdentificationFamilyReceipt adjustedObservationalComparison

  longitudinalReceipt :
    LongitudinalBeforeAfterReceipt →
    IdentificationFamilyReceipt longitudinalBeforeAfter

  mediationReceipt :
    MechanisticMediationReceipt →
    IdentificationFamilyReceipt mechanisticMediation

  geneticReceipt :
    LineageGeneticPerturbationReceipt →
    IdentificationFamilyReceipt lineageGeneticPerturbation

  neuralReceipt :
    NeuralPerturbationReadoutReceipt →
    IdentificationFamilyReceipt neuralPerturbationReadout

------------------------------------------------------------------------
-- Evidence-design gate.
--
-- A family receipt must also be admissible for the exact assertion obligation.
-- This reuses the canonical relational evidence-admissibility owner rather than
-- defining a universal ranking among families.
------------------------------------------------------------------------

record IdentificationEvidenceGate
    (family : CausalIdentificationFamily) : Set where
  constructor identification-evidence-gate
  field
    familyReceipt : IdentificationFamilyReceipt family
    evidenceForObligation : Evidence.EvidenceForObligation
    promotionAdmissible :
      Evidence.AdmissibleForPromotion
        (Evidence.finding evidenceForObligation)
    causalQuestionAffordanceReference : String

open IdentificationEvidenceGate public

------------------------------------------------------------------------
-- Installation into one generic causal design.
--
-- The design's abstract IdentificationAssumption is required to be exactly the
-- selected family receipt type.  Thus downstream code cannot silently relabel
-- an observational receipt as randomisation, mediation, genetic perturbation,
-- etc.
------------------------------------------------------------------------

record CrossLevelIdentificationInstallation
    {Value : Set}
    {claim : Router.CrossLevelCausalClaim Value}
    (causalDesign : Router.CrossLevelCausalDesign claim) : Set₁ where
  constructor cross-level-identification-installation
  field
    family : CausalIdentificationFamily
    gate : IdentificationEvidenceGate family

    assumptionMatchesFamily :
      Router.IdentificationAssumption causalDesign
      ≡ IdentificationFamilyReceipt family

    installedFamilyReceipt :
      IdentificationFamilyReceipt family

    installedReceiptMatchesDesignReceipt :
      subst (λ Assumption → Assumption)
        assumptionMatchesFamily
        (Router.identificationReceipt causalDesign)
      ≡ installedFamilyReceipt

    installationReference : String

open CrossLevelIdentificationInstallation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RandomisationMeansUniversalTransportPermission : Set where

data AdjustmentMeansNoUnmeasuredConfoundingPermission : Set where

data LongitudinalMeansCausationPermission : Set where

data MediationAssociationMeansMechanismPermission : Set where

data GeneticPerturbationMeansUniqueMechanismPermission : Set where

data NeuralPerturbationMeansThoughtIdentityPermission : Set where

data IdentificationFamilyAutomaticallyProvesCausalEffectPermission : Set where

data UniversalIdentificationHierarchyPermission : Set where

randomisationDoesNotByItselfProveUniversalTransport :
  RandomisationMeansUniversalTransportPermission → ⊥
randomisationDoesNotByItselfProveUniversalTransport ()

adjustmentDoesNotEraseUnmeasuredConfounding :
  AdjustmentMeansNoUnmeasuredConfoundingPermission → ⊥
adjustmentDoesNotEraseUnmeasuredConfounding ()

longitudinalOrderDoesNotByItselfIdentifyCause :
  LongitudinalMeansCausationPermission → ⊥
longitudinalOrderDoesNotByItselfIdentifyCause ()

mediatorAssociationDoesNotByItselfIdentifyMechanism :
  MediationAssociationMeansMechanismPermission → ⊥
mediatorAssociationDoesNotByItselfIdentifyMechanism ()

geneticPerturbationDoesNotByItselfProveUniqueMechanism :
  GeneticPerturbationMeansUniqueMechanismPermission → ⊥
geneticPerturbationDoesNotByItselfProveUniqueMechanism ()

neuralPerturbationDoesNotIdentifyThought :
  NeuralPerturbationMeansThoughtIdentityPermission → ⊥
neuralPerturbationDoesNotIdentifyThought ()

identificationFamilyDoesNotAutomaticallyProveCausalEffect :
  IdentificationFamilyAutomaticallyProvesCausalEffectPermission → ⊥
identificationFamilyDoesNotAutomaticallyProveCausalEffect ()

noUniversalIdentificationHierarchy :
  UniversalIdentificationHierarchyPermission → ⊥
noUniversalIdentificationHierarchy ()

record CausalIdentificationFamiliesBoundary : Set where
  constructor causal-identification-families-boundary
  field
    identificationIsObligationRelative : Bool
    randomisationAndTransportRemainDistinct : Bool
    adjustmentAndNoResidualConfoundingRemainDistinct : Bool
    longitudinalAndCausationRemainDistinct : Bool
    mediationNeedsSeparatePathReceipts : Bool
    geneticPerturbationKeepsOffTargetBackgroundExplicit : Bool
    neuralPerturbationKeepsCognitiveReadoutSeparate : Bool
    familyReceiptAutomaticallyProvesCausalEffect : Bool
    oneUniversalDesignHierarchy : Bool

canonicalCausalIdentificationFamiliesBoundary :
  CausalIdentificationFamiliesBoundary
canonicalCausalIdentificationFamiliesBoundary =
  causal-identification-families-boundary
    true true true true true true true false false
