module DASHI.Cognition.PNF.SensibLawMaboLandBackAuditedCausalEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackCausalCapstoneExact as Previous
import DASHI.Cognition.PNF.SensibLawMaboLandBackAttributionAuditV02Exact as Audit
import DASHI.Cognition.PNF.SensibLawMaboDawsonCrownDerivationHingeClosureExact as Dawson
import DASHI.Cognition.PNF.SensibLawLandBackModeratorAttributionCorrectionExact as CPI
import DASHI.Cognition.PNF.SensibLawLandBackEvidenceDesignCorrectionExact as Design
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as CarbonProjection
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueComparabilityExact as Carbon
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source
import DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact as Income
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Recognition

------------------------------------------------------------------------
-- Audited capstone. This is the preferred downstream surface after the source-
-- attribution review. Historical owners remain available for audit/replay.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Dawson: the missing internal premise is now recovered for one consumer.
------------------------------------------------------------------------

dawsonInternalLogicClosed :
  Dawson.consumerClosure Dawson.reconstructDawsonInternalLogic ≡ Dawson.consumerClosed
dawsonInternalLogicClosed = refl

dawsonMajorityRuleOpen :
  Dawson.consumerClosure Dawson.determineMajorityNativeTitleRule ≡ Dawson.consumerOpen
dawsonMajorityRuleOpen = refl

dawsonColonialLegitimacyOpen :
  Dawson.consumerClosure Dawson.evaluateColonialLegitimacy ≡ Dawson.consumerOpen
dawsonColonialLegitimacyOpen = refl

dawsonCrossOrderConflictLocated :
  Dawson.consumerClosure Dawson.compareIndependentIndigenousLegalOrder
  ≡ Dawson.consumerCriticalConflictLocated
dawsonCrossOrderConflictLocated = refl

radicalTitleIntermediateIsDerivativeRights :
  Dawson.nextNode Dawson.crownUltimateRadicalTitleNode ≡ Dawson.crownDerivativeRightsNode
radicalTitleIntermediateIsDerivativeRights = refl

derivativeRightsThenRecognitionChoice :
  Dawson.nextNode Dawson.crownDerivativeRightsNode ≡ Dawson.crownRecognitionChoiceNode
derivativeRightsThenRecognitionChoice = refl

------------------------------------------------------------------------
-- Corrected source-attribution defaults.
------------------------------------------------------------------------

cpiPreferredStatusIsIndependentPolicyAssociation :
  CPI.preferredStatus CPI.cpiModeratorAttributionCorrection
  ≡ CPI.independentPolicyAssociationMapped
cpiPreferredStatusIsIndependentPolicyAssociation = refl

cpiAuthorNotGovernment :
  Source.analysisAuthorIsGovernment Source.cpi2024RuralCreditAuthority ≡ false
cpiAuthorNotGovernment = refl

cpiStillUsesOfficialUnderlyingData :
  Source.usesOfficialUnderlyingData Source.cpi2024RuralCreditAuthority ≡ true
cpiStillUsesOfficialUnderlyingData = refl

ashDatabookIsAcademicSynthesis :
  Source.authorityKind Source.ashCenter2025DatabookAuthority
  ≡ Source.academicDescriptiveStatisticalSynthesis
ashDatabookIsAcademicSynthesis = refl

probstPreferredDesignIsFixedEffectsCausalChain :
  Design.preferredDesign Design.probst2020DesignCorrection
  ≡ Design.fixedEffectsCausalChainDesign
probstPreferredDesignIsFixedEffectsCausalChain = refl

denBraberPreferredClaimRemainsComparative :
  Design.preferredClaimVerb Design.denBraber2024ClaimVerbCorrection
  ≡ Design.sourceReportsComparativeAssociationOrEstimatedDifference
denBraberPreferredClaimRemainsComparative = refl

------------------------------------------------------------------------
-- Carbon value: category, market price and social valuation stay orthogonal.
------------------------------------------------------------------------

biaCategoryIsAdministrativePolicy :
  Source.authorityKind Source.biaCarbon2023Authority ≡ Source.officialAdministrativePolicy
biaCategoryIsAdministrativePolicy = refl

abatableIsCommercialMarketObservation :
  Source.authorityKind Source.abatable2025ReddPriceAuthority ≡ Source.commercialMarketObservation
abatableIsCommercialMarketObservation = refl

wriIsEconomicValuation :
  Source.authorityKind Source.wriTenureEconomicValuationAuthority ≡ Source.economicValuationReport
wriIsEconomicValuation = refl

wriVsAbatableNeedsCommonFunctionalUnit :
  Carbon.comparability Carbon.wriMarketGapBoundary ≡ Carbon.conversionReceiptRequired
wriVsAbatableNeedsCommonFunctionalUnit = refl

noExactUndercompensationRatioPromoted :
  Carbon.exactDirectUndercompensationRatioClaimed Carbon.wriMarketGapBoundary ≡ false
noExactUndercompensationRatioPromoted = refl

------------------------------------------------------------------------
-- Triple projection-inadequacy cross-pollination.
------------------------------------------------------------------------

incomeObserverCannotCarryLandAuthority :
  INF.FactorsThrough Income.cashIncomeObserver Income.landAuthorityOutcome → ⊥
incomeObserverCannotCarryLandAuthority = Income.cashIncomeDoesNotFactorLandAuthority

crownRecognitionCannotCarryIndigenousAuthority :
  INF.FactorsThrough Recognition.crownRecognitionObserver Recognition.indigenousAuthorityOutcome → ⊥
crownRecognitionCannotCarryIndigenousAuthority = Recognition.crownRecognitionDoesNotFactorIndigenousAuthority

trustAssetCategoryCannotCarryStewardshipValue :
  INF.FactorsThrough CarbonProjection.trustAssetObserver CarbonProjection.stewardshipValueOutcome → ⊥
trustAssetCategoryCannotCarryStewardshipValue = CarbonProjection.trustAssetCategoryCannotFactorStewardshipValue

------------------------------------------------------------------------
-- Source audit itself does not create substantive truth.
------------------------------------------------------------------------

laterAuditPreservesHistoricalState :
  Audit.priorAuditStillHistoricallyValid Audit.dawsonLaterSourceClosure ≡ true
laterAuditPreservesHistoricalState = refl

laterAuditDoesNotRewriteHistory :
  Audit.retroactiveRewriteOfPriorAudit Audit.dawsonLaterSourceClosure ≡ false
laterAuditDoesNotRewriteHistory = refl

------------------------------------------------------------------------
-- No-collapse exports.
------------------------------------------------------------------------

internalDawsonClosureDoesNotBecomeMajority : Dawson.DawsonInternalClosureEqualsMajorityHolding → ⊥
internalDawsonClosureDoesNotBecomeMajority = Dawson.dawsonClosureDoesNotBecomeMajorityHolding

officialInputDoesNotTransferAuthorship : Source.OfficialUnderlyingDataMakesDerivedAnalysisOfficial → ⊥
officialInputDoesNotTransferAuthorship = Source.officialInputDoesNotTransferAuthorship

marketPriceDoesNotEqualSocialValue : Source.CommercialMarketPriceEqualsSocialValue → ⊥
marketPriceDoesNotEqualSocialValue = Source.marketPriceDoesNotEqualSocialValue

agencyCategoryDoesNotExhaustStewardship : Source.AgencyPolicyClassificationExhaustsStewardshipValue → ⊥
agencyCategoryDoesNotExhaustStewardship = Source.agencyCategoryDoesNotExhaustStewardshipValue

comparativeEstimateDoesNotBecomeUniversalLaw : Design.ComparativeEstimateBecomesUniversalCausalLaw → ⊥
comparativeEstimateDoesNotBecomeUniversalLaw = Design.comparativeEstimateDoesNotBecomeUniversalLaw
