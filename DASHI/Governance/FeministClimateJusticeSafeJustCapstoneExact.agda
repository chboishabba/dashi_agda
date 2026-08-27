module DASHI.Governance.FeministClimateJusticeSafeJustCapstoneExact where

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.WaringProductionBoundaryNonfactorabilityExact as Waring
import DASHI.Governance.FeministSocialProvisioningInterpretationExact as Power
import DASHI.Governance.MacGregorPostPoliticalAuthorityBoundaryExact as MacGregor
import DASHI.Governance.SultanaClimateColonialityResidualExact as Sultana
import DASHI.Governance.PacificWomenNegotiationContributionNonDescentExact as Pacific
import DASHI.Governance.VanuatuGenderedRecoveryObserverBoundaryExact as Vanuatu
import DASHI.Governance.YusoffGeologicCategoryAuthorityBoundaryExact as Yusoff
import DASHI.Governance.MaathaiSituatedProvisioningAuthorityExact as Maathai
import DASHI.Governance.FeministClimateJusticeResidualBundleExact as Residual
import DASHI.Governance.FeministClimateQualifiedPromotionExact as Promotion
import DASHI.Governance.SafeJustSocialIndicatorJusticeBoundaryExact as Justice

------------------------------------------------------------------------
-- FEMINIST CLIMATE-JUSTICE / SAFE-AND-JUST CAPSTONE
--
-- The safe-and-just empirical state space remains useful.  These bridges state
-- why it is nevertheless situated, lossy, relational, historically produced
-- and normatively incomplete for consumers that require those coordinates.
------------------------------------------------------------------------

unpaidProvisioningDoesNotDescendThroughAccounting :
  Consumer.FactorsThrough Waring.accountObserver Waring.provisioningContribution → ⊥
unpaidProvisioningDoesNotDescendThroughAccounting =
  Waring.provisioningDoesNotDescendThroughAccountingBoundary

powerSocialProvisioningCalibration : Power.SocialProvisioningCalibrationReceipt
powerSocialProvisioningCalibration = Power.canonicalSocialProvisioningCalibration

qualifiedTechnicalSynthesisDoesNotSupplyDepoliticizedMandate :
  MacGregor.DepoliticizedAdministrativeMandate → ⊥
qualifiedTechnicalSynthesisDoesNotSupplyDepoliticizedMandate =
  MacGregor.qualifiedSynthesisDoesNotSupplyDepoliticizedMandate

aggregateDoesNotDetermineClimateResponsibility :
  Consumer.FactorsThrough
    (DASHI.Core.ResponsibilityBurdenNonfactorabilityExact.aggregateObserver
      Sultana.climateJusticeGeometry)
    (DASHI.Core.ResponsibilityBurdenNonfactorabilityExact.contribution
      Sultana.climateJusticeGeometry) → ⊥
aggregateDoesNotDetermineClimateResponsibility =
  Sultana.aggregateDoesNotRecoverResponsibility

visibleRolePlusContributionStrictlyRefinesVisibleRole :
  Observer.StrictRefinement
    Pacific.visibleRole
    (Observer.pairObserver Pacific.visibleRole Pacific.contribution)
visibleRolePlusContributionStrictlyRefinesVisibleRole =
  Pacific.joinedObserverStrictlyRefinesVisibleRole

sameEventStatusDoesNotDetermineSituatedRecovery :
  Consumer.FactorsThrough Vanuatu.eventStatus Vanuatu.recoveryFunctioning → ⊥
sameEventStatusDoesNotDetermineSituatedRecovery =
  Vanuatu.recoveryDoesNotDescendThroughEventStatus

technicalCategoryUseDoesNotSupplyHistoricalNeutrality :
  Yusoff.GenesisAccountedFor Yusoff.anthropoceneCategory → ⊥
technicalCategoryUseDoesNotSupplyHistoricalNeutrality =
  Yusoff.technicalUseDoesNotSupplyGenesisAccounting

maathaiPositiveSituatedAuthorityPath : Maathai.SituatedProvisioningAuthorityPath
maathaiPositiveSituatedAuthorityPath = Maathai.canonicalMaathaiPath

fiveAxisResidualCarriage :
  DASHI.Core.MultiaxialResidualBundleExact.ResidualCarriageReceipt
    Residual.researchSynthesisResidualContract
    Residual.canonicalClimateJusticeResiduals
fiveAxisResidualCarriage = Residual.canonicalResidualCarriage

qualifiedPromotionWithOpenResidualVector : Promotion.FeministClimateQualifiedPromotion
qualifiedPromotionWithOpenResidualVector =
  Promotion.canonicalFeministClimateQualifiedPromotion

allMeasuredThresholdsStillDoNotSupplyParticipatoryJustice :
  Justice.ParticipatoryJusticeCertificate → ⊥
allMeasuredThresholdsStillDoNotSupplyParticipatoryJustice =
  Justice.allMeasuredThresholdsDoNotSupplyParticipatoryJustice

record FeministClimateSafeJustBoundary : Set where
  constructor feministClimateSafeJustBoundary
  field
    countedResourceEqualsProvisioningContribution : Bool
    countedResourceEqualsProvisioningContributionIsFalse :
      countedResourceEqualsProvisioningContribution ≡ false
    technicalAdequacyEqualsPoliticalContestability : Bool
    technicalAdequacyEqualsPoliticalContestabilityIsFalse :
      technicalAdequacyEqualsPoliticalContestability ≡ false
    aggregateOvershootEqualsResponsibilityDistribution : Bool
    aggregateOvershootEqualsResponsibilityDistributionIsFalse :
      aggregateOvershootEqualsResponsibilityDistribution ≡ false
    visibleAuthorityEqualsSubstantiveContribution : Bool
    visibleAuthorityEqualsSubstantiveContributionIsFalse :
      visibleAuthorityEqualsSubstantiveContribution ≡ false
    eventSuccessEqualsSituatedRecovery : Bool
    eventSuccessEqualsSituatedRecoveryIsFalse :
      eventSuccessEqualsSituatedRecovery ≡ false
    technicalCategoryAdequacyEqualsHistoricalNeutrality : Bool
    technicalCategoryAdequacyEqualsHistoricalNeutralityIsFalse :
      technicalCategoryAdequacyEqualsHistoricalNeutrality ≡ false
    ecologicalFunctioningEqualsPoliticalAuthority : Bool
    ecologicalFunctioningEqualsPoliticalAuthorityIsFalse :
      ecologicalFunctioningEqualsPoliticalAuthority ≡ false
    safeJustIndicatorClosureEqualsJusticeClosure : Bool
    safeJustIndicatorClosureEqualsJusticeClosureIsFalse :
      safeJustIndicatorClosureEqualsJusticeClosure ≡ false
    qualifiedPromotionEqualsResidualClosure : Bool
    qualifiedPromotionEqualsResidualClosureIsFalse :
      qualifiedPromotionEqualsResidualClosure ≡ false

canonicalFeministClimateSafeJustBoundary : FeministClimateSafeJustBoundary
canonicalFeministClimateSafeJustBoundary =
  feministClimateSafeJustBoundary
    false refl false refl false refl false refl false refl
    false refl false refl false refl false refl
