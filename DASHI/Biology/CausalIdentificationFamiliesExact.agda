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
-- causal effect by itself. Each schema states which design-specific receipts
-- must be paid before the generic multiscale causal router may use that family
-- as its IdentificationAssumption.
------------------------------------------------------------------------

data CausalIdentificationFamily : Set where
  randomisedPerturbation : CausalIdentificationFamily
  adjustedObservationalComparison : CausalIdentificationFamily
  longitudinalBeforeAfter : CausalIdentificationFamily
  instrumentalNaturalExperiment : CausalIdentificationFamily
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
-- Instrumental-variable / natural-experiment family.
--
-- A naturally varying instrument may identify a bounded causal contrast only
-- when relevance, exogeneity/as-if-random variation and exclusion are all
-- explicitly argued, with spillover/interference and scope retained rather than
-- silently erased. This owner does not claim that any proposed instrument pays
-- those obligations merely because it precedes the exposure or predicts it.
------------------------------------------------------------------------

record InstrumentalNaturalExperimentReceipt : Set where
  constructor instrumental-natural-experiment-receipt
  field
    instrumentReference exposureReference outcomeReference : String
    relevanceReference exogeneityReference exclusionReference : String
    spilloverReference scopeReference : String

    instrumentRelevanceSupported : Bool
    instrumentRelevanceSupportedIsTrue : instrumentRelevanceSupported ≡ true
    exogeneityOrAsIfRandomVariationArgued : Bool
    exogeneityOrAsIfRandomVariationArguedIsTrue :
      exogeneityOrAsIfRandomVariationArgued ≡ true
    exclusionRestrictionArgued : Bool
    exclusionRestrictionArguedIsTrue : exclusionRestrictionArgued ≡ true
    spilloverOrInterferenceAudited : Bool
    spilloverOrInterferenceAuditedIsTrue : spilloverOrInterferenceAudited ≡ true
    estimandScopeDeclared : Bool
    estimandScopeDeclaredIsTrue : estimandScopeDeclared ≡ true

open InstrumentalNaturalExperimentReceipt public

------------------------------------------------------------------------
-- Mechanistic mediation.
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

  instrumentalNaturalExperimentReceipt :
    InstrumentalNaturalExperimentReceipt →
    IdentificationFamilyReceipt instrumentalNaturalExperiment

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

data InstrumentRelevanceMeansValidIVPermission : Set where

data InstrumentMeansUniversalEffectPermission : Set where

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

instrumentRelevanceDoesNotByItselfValidateIV :
  InstrumentRelevanceMeansValidIVPermission → ⊥
instrumentRelevanceDoesNotByItselfValidateIV ()

instrumentDoesNotAutomaticallyTransportEffect :
  InstrumentMeansUniversalEffectPermission → ⊥
instrumentDoesNotAutomaticallyTransportEffect ()

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
    instrumentalRelevanceAndValidityRemainDistinct : Bool
    instrumentalEffectAndUniversalTransportRemainDistinct : Bool
    mediationNeedsSeparatePathReceipts : Bool
    geneticPerturbationKeepsOffTargetBackgroundExplicit : Bool
    neuralPerturbationKeepsCognitiveReadoutSeparate : Bool
    familyReceiptAutomaticallyProvesCausalEffect : Bool
    oneUniversalDesignHierarchy : Bool

canonicalCausalIdentificationFamiliesBoundary :
  CausalIdentificationFamiliesBoundary
canonicalCausalIdentificationFamiliesBoundary =
  causal-identification-families-boundary
    true true true true true true true true true false false
