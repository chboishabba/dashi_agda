module DASHI.Governance.EmpiricalProducerRound5Regression where

open import DASHI.Core.Prelude

import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC
import DASHI.Governance.BCDecriminalizationSourceRegistryExact as BCSources

------------------------------------------------------------------------
-- Palantir: generic capability is now evidenced, deployment-specific subject
-- data/decision/contestability remains deliberately uninstalled.
------------------------------------------------------------------------

palantirObjectGraphCapabilityInstalled :
  Palantir.PalantirCapabilityBoundary.objectLinkGraphCapabilityInstalled
    Palantir.canonicalPalantirCapabilityBoundary
  ≡ true
palantirObjectGraphCapabilityInstalled = refl

palantirOperationalWorkflowCapabilityInstalled :
  Palantir.PalantirCapabilityBoundary.operationalWorkflowCapabilityInstalled
    Palantir.canonicalPalantirCapabilityBoundary
  ≡ true
palantirOperationalWorkflowCapabilityInstalled = refl

palantirDeploymentSubjectDataStillMissing :
  Palantir.PalantirCapabilityBoundary.deploymentSubjectDataReceiptInstalled
    Palantir.canonicalPalantirCapabilityBoundary
  ≡ false
palantirDeploymentSubjectDataStillMissing = refl

palantirDeploymentDecisionUseStillMissing :
  Palantir.PalantirCapabilityBoundary.deploymentDecisionUseReceiptInstalled
    Palantir.canonicalPalantirCapabilityBoundary
  ≡ false
palantirDeploymentDecisionUseStillMissing = refl

palantirSubjectContestabilityStillMissing :
  Palantir.PalantirCapabilityBoundary.subjectInspectionCorrectionAppealInstalled
    Palantir.canonicalPalantirCapabilityBoundary
  ≡ false
palantirSubjectContestabilityStillMissing = refl

------------------------------------------------------------------------
-- BC: the intervention is now a phase-indexed bundle rather than one binary
-- decriminalization label.
------------------------------------------------------------------------

bcLabelAndBundleSeparated :
  BC.BCBundleBoundary.policyLabelAndImplementationBundleSeparated
    BC.canonicalBCBundleBoundary
  ≡ true
bcLabelAndBundleSeparated = refl

bcAmendmentChangesTreatmentDefinition :
  BC.BCBundleBoundary.amendmentChangesTreatmentDefinition
    BC.canonicalBCBundleBoundary
  ≡ true
bcAmendmentChangesTreatmentDefinition = refl

bcDedicatedSupportConstrained :
  BC.BCBundleBoundary.dedicatedFundingAndTrainingConstrained
    BC.canonicalBCBundleBoundary
  ≡ true
bcDedicatedSupportConstrained = refl

bcHousingPovertyBundleNotCommensuratelyInstalled :
  BC.BCBundleBoundary.housingAndPovertyInfrastructureCommensuratelyInstalled
    BC.canonicalBCBundleBoundary
  ≡ false
bcHousingPovertyBundleNotCommensuratelyInstalled = refl

bcInitialJusticeReductionObserved :
  BC.BCBundleBoundary.initialJusticeReductionObserved
    BC.canonicalBCBundleBoundary
  ≡ true
bcInitialJusticeReductionObserved = refl

bcPilotDoesNotEqualFullyProvisionedReform :
  BC.BCBundleBoundary.underprovisionedPilotEqualsFullyProvisionedReform
    BC.canonicalBCBundleBoundary
  ≡ false
bcPilotDoesNotEqualFullyProvisionedReform = refl

bcPilotOutcomeDoesNotInstallLegalReformCausality :
  BC.BCBundleBoundary.pilotOutcomeAloneEstablishesDecriminalizationCausality
    BC.canonicalBCBundleBoundary
  ≡ false
bcPilotOutcomeDoesNotInstallLegalReformCausality = refl

bcExactScholarlyMetadataInstalled :
  BCSources.RegistryBoundary.fullAuthorMetadataInstalled
    BCSources.canonicalRegistryBoundary
  ≡ true
bcExactScholarlyMetadataInstalled = refl
