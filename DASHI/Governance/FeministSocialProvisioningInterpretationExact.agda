module DASHI.Governance.FeministSocialProvisioningInterpretationExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustProvisioningCapabilityFunctioningBridgeExact as SafeJust
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- POWER 2004: FEMINIST SOCIAL-PROVISIONING INTERPRETATION
--
-- Marilyn Power, "Social Provisioning as a Starting Point for Feminist
-- Economics", Feminist Economics 10(3):3-19 (2004).
-- DOI: 10.1080/1354570042000267608.
--
-- Power states five methodological components.  DASHI represents them through
-- six formal interpretation roles because her third component -- analysis of
-- economic, political and social processes and power relations -- is split into
-- `economicPoliticalSocialProcess` and `powerRelations`.  That split is a DASHI
-- formal convenience, not a claim that Power stated six components or supplied
-- this carrier.
------------------------------------------------------------------------

data SocialProvisioningRole : Set where
  careAndUnpaidLabour
  wellbeingCriterion
  economicPoliticalSocialProcess
  powerRelations
  ethicalGoalsAndValues
  intersectionalDifference
  : SocialProvisioningRole

data DashiInterpretiveTarget : Set where
  provisioningActivity
  functioningOrNeedOutcome
  institutionalAuthorityContext
  explicitNormativeClaimRole
  situatedIntersectionalCoordinates
  : DashiInterpretiveTarget

interpretRole : SocialProvisioningRole → DashiInterpretiveTarget
interpretRole careAndUnpaidLabour = provisioningActivity
interpretRole wellbeingCriterion = functioningOrNeedOutcome
interpretRole economicPoliticalSocialProcess = institutionalAuthorityContext
interpretRole powerRelations = institutionalAuthorityContext
interpretRole ethicalGoalsAndValues = explicitNormativeClaimRole
interpretRole intersectionalDifference = situatedIntersectionalCoordinates

record SocialProvisioningCalibrationReceipt : Set where
  constructor socialProvisioningCalibrationReceipt
  field
    careMapped : interpretRole careAndUnpaidLabour ≡ provisioningActivity
    wellbeingMapped : interpretRole wellbeingCriterion ≡ functioningOrNeedOutcome
    processMapped : interpretRole economicPoliticalSocialProcess ≡ institutionalAuthorityContext
    powerMapped : interpretRole powerRelations ≡ institutionalAuthorityContext
    ethicsMapped : interpretRole ethicalGoalsAndValues ≡ explicitNormativeClaimRole
    differenceMapped : interpretRole intersectionalDifference ≡ situatedIntersectionalCoordinates

canonicalSocialProvisioningCalibration : SocialProvisioningCalibrationReceipt
canonicalSocialProvisioningCalibration =
  socialProvisioningCalibrationReceipt refl refl refl refl refl refl

-- Existing #625 witness remains a DASHI construction: changing resource input
-- without changing the provisioning context need not expand capability.
resourceOnlyStillDoesNotExpandCapability :
  SafeJust.capability SafeJust.baseline ≡ SafeJust.capability SafeJust.resourceOnly
resourceOnlyStillDoesNotExpandCapability = SafeJust.resourceOnlyCapabilityUnchanged

source : Sources.SourceReference
source = Sources.power2004

record FeministSocialProvisioningBoundary : Set where
  constructor feministSocialProvisioningBoundary
  field
    marketExchangeExhaustsProvisioning : Bool
    marketExchangeExhaustsProvisioningIsFalse : marketExchangeExhaustsProvisioning ≡ false
    caringAndUnpaidLabourAreOutsideEconomicInquiryByDefinition : Bool
    caringAndUnpaidLabourAreOutsideEconomicInquiryByDefinitionIsFalse :
      caringAndUnpaidLabourAreOutsideEconomicInquiryByDefinition ≡ false
    dashiProvisioningRecordIsPowerMethodology : Bool
    dashiProvisioningRecordIsPowerMethodologyIsFalse :
      dashiProvisioningRecordIsPowerMethodology ≡ false
    boundedInterpretationTransfersSourceTheoremAuthorship : Bool
    boundedInterpretationTransfersSourceTheoremAuthorshipIsFalse :
      boundedInterpretationTransfersSourceTheoremAuthorship ≡ false

canonicalFeministSocialProvisioningBoundary : FeministSocialProvisioningBoundary
canonicalFeministSocialProvisioningBoundary =
  feministSocialProvisioningBoundary false refl false refl false refl false refl
