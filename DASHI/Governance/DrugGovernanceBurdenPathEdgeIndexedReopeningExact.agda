module DASHI.Governance.DrugGovernanceBurdenPathEdgeIndexedReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Governance.DrugGovernanceHistoricalBurdenPathExact as Path

------------------------------------------------------------------------
-- EDGE-INDEXED REOPENING FOR HISTORICAL BURDEN FLOW
--
-- Reopening is driven by proof of actual edge occurrence / dependency, not by
-- broad domain similarity.  Clinical/chemistry consumers remain independent
-- unless a separate dependency edge is supplied.
------------------------------------------------------------------------

data BurdenEdgeInstance : Set where
  punitiveExternalisationEdge
  therapeuticReopeningEdge
  commercialCaptureEdge
  repairAcknowledgementEdge
  repairDischargeEdge
  : BurdenEdgeInstance

data BurdenConsequence : Set where
  materialBenefitConsequence
  historicalRepairConsequence
  classificationLegitimacyConsequence
  clinicalEfficacyConsequence
  chemistryIdentityConsequence
  : BurdenConsequence

data EdgeOccurs : BurdenEdgeInstance → BurdenConsequence → Set where
  punitiveOccursInHistoricalRepair :
    EdgeOccurs punitiveExternalisationEdge historicalRepairConsequence
  punitiveOccursInLegitimacy :
    EdgeOccurs punitiveExternalisationEdge classificationLegitimacyConsequence

  therapeuticOccursInHistoricalRepair :
    EdgeOccurs therapeuticReopeningEdge historicalRepairConsequence

  commercialOccursInMaterialBenefit :
    EdgeOccurs commercialCaptureEdge materialBenefitConsequence
  commercialOccursInHistoricalRepair :
    EdgeOccurs commercialCaptureEdge historicalRepairConsequence
  commercialOccursInLegitimacy :
    EdgeOccurs commercialCaptureEdge classificationLegitimacyConsequence

  acknowledgementOccursInHistoricalRepair :
    EdgeOccurs repairAcknowledgementEdge historicalRepairConsequence
  dischargeOccursInHistoricalRepair :
    EdgeOccurs repairDischargeEdge historicalRepairConsequence

------------------------------------------------------------------------
-- Reverse-dependency graph.
------------------------------------------------------------------------

data BurdenIndexedArtifact : Set where
  edgeArtifact : BurdenEdgeInstance → BurdenIndexedArtifact
  consequenceArtifact : BurdenConsequence → BurdenIndexedArtifact
  consumerArtifact : BurdenConsequence → BurdenIndexedArtifact

data Depends : BurdenIndexedArtifact → BurdenIndexedArtifact → Set where
  occurrenceCreatesDependency :
    ∀ {edge consequence} →
    EdgeOccurs edge consequence →
    Depends (edgeArtifact edge) (consequenceArtifact consequence)
  consequenceFeedsConsumer :
    ∀ {consequence} →
    Depends (consequenceArtifact consequence) (consumerArtifact consequence)

edgeOccurrenceCreatesReopening :
  ∀ {edge consequence} →
  EdgeOccurs edge consequence →
  Affected.ReopeningObligation
    Depends (edgeArtifact edge) (consumerArtifact consequence)
edgeOccurrenceCreatesReopening occurrence =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation
      (occurrenceCreatesDependency occurrence))
    (Affected.oneEdgeCreatesReopeningObligation consequenceFeedsConsumer)

commercialCaptureReopensMaterialBenefit :
  Affected.ReopeningObligation
    Depends
    (edgeArtifact commercialCaptureEdge)
    (consumerArtifact materialBenefitConsequence)
commercialCaptureReopensMaterialBenefit =
  edgeOccurrenceCreatesReopening commercialOccursInMaterialBenefit

commercialCaptureReopensHistoricalRepair :
  Affected.ReopeningObligation
    Depends
    (edgeArtifact commercialCaptureEdge)
    (consumerArtifact historicalRepairConsequence)
commercialCaptureReopensHistoricalRepair =
  edgeOccurrenceCreatesReopening commercialOccursInHistoricalRepair

punitiveExternalisationReopensLegitimacy :
  Affected.ReopeningObligation
    Depends
    (edgeArtifact punitiveExternalisationEdge)
    (consumerArtifact classificationLegitimacyConsequence)
punitiveExternalisationReopensLegitimacy =
  edgeOccurrenceCreatesReopening punitiveOccursInLegitimacy

------------------------------------------------------------------------
-- Weld actual path occurrence to reopening.
------------------------------------------------------------------------

commercialPathOccurrenceReopensMaterial :
  Path.ContainsCommercialCapture Path.canonicalCommercialRepairPath →
  Affected.ReopeningObligation
    Depends
    (edgeArtifact commercialCaptureEdge)
    (consumerArtifact materialBenefitConsequence)
commercialPathOccurrenceReopensMaterial _ = commercialCaptureReopensMaterialBenefit

commercialPathOccurrenceReopensRepair :
  Path.ContainsCommercialCapture Path.canonicalCommercialRepairPath →
  Affected.ReopeningObligation
    Depends
    (edgeArtifact commercialCaptureEdge)
    (consumerArtifact historicalRepairConsequence)
commercialPathOccurrenceReopensRepair _ = commercialCaptureReopensHistoricalRepair

------------------------------------------------------------------------
-- Selectivity: the burden-edge language itself supplies no clinical/chemistry
-- occurrence.  A separate theorem would be required to create such a path.
------------------------------------------------------------------------

commercialCaptureDoesNotOccurInClinicalEfficacy :
  EdgeOccurs commercialCaptureEdge clinicalEfficacyConsequence → ⊥
commercialCaptureDoesNotOccurInClinicalEfficacy ()

commercialCaptureDoesNotOccurInChemistryIdentity :
  EdgeOccurs commercialCaptureEdge chemistryIdentityConsequence → ⊥
commercialCaptureDoesNotOccurInChemistryIdentity ()

punitiveExternalisationDoesNotOccurInChemistryIdentity :
  EdgeOccurs punitiveExternalisationEdge chemistryIdentityConsequence → ⊥
punitiveExternalisationDoesNotOccurInChemistryIdentity ()

record BurdenPathEdgeIndexedReopeningBoundary : Set where
  constructor burdenPathEdgeIndexedReopeningBoundary
  field
    actualEdgeOccurrenceCanReopenDependentConsumer : Bool
    actualEdgeOccurrenceCanReopenDependentConsumerIsTrue :
      actualEdgeOccurrenceCanReopenDependentConsumer ≡ true
    sameDrugPolicyDomainForcesGlobalReopening : Bool
    sameDrugPolicyDomainForcesGlobalReopeningIsFalse :
      sameDrugPolicyDomainForcesGlobalReopening ≡ false
    commercialCaptureAutomaticallyInvalidatesClinicalEfficacy : Bool
    commercialCaptureAutomaticallyInvalidatesClinicalEfficacyIsFalse :
      commercialCaptureAutomaticallyInvalidatesClinicalEfficacy ≡ false
    chemistryIdentityAutomaticallyDependsOnBurdenHistory : Bool
    chemistryIdentityAutomaticallyDependsOnBurdenHistoryIsFalse :
      chemistryIdentityAutomaticallyDependsOnBurdenHistory ≡ false

canonicalBurdenPathEdgeIndexedReopeningBoundary :
  BurdenPathEdgeIndexedReopeningBoundary
canonicalBurdenPathEdgeIndexedReopeningBoundary =
  burdenPathEdgeIndexedReopeningBoundary
    true refl false refl false refl false refl
