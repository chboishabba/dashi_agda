module DASHI.Economics.AICurrentRegimeSourceAttributionCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Attribution
import DASHI.Economics.MicrosoftCloudAIMarginPressure2026Exact as Microsoft
import DASHI.Economics.NvidiaCoreWeaveReflexiveInvestment2026Exact as Nvidia
import DASHI.Economics.CoreWeaveGPUBackedStructuredFinance2026Exact as CoreWeave
import DASHI.Economics.SoftBankOpenAIValuationLeverage2026Exact as SoftBank
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as Manufacturing
import DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact as Short
import DASHI.Economics.MarxCapitalAIInfrastructureCrossPollinationExact as Marx

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTION RETROFIT FOR CURRENT-REGIME CALIBRATIONS
--
-- Existing application owners remain the proposition/data owners.  This module
-- adds the attribution coordinates required by the earlier DASHI source rules.
-- It does not rewrite a primary corporate statement into an independent fact,
-- or a secondary report into primary authorship.
------------------------------------------------------------------------

microsoftMarginAttribution : Attribution.SourceAttributionReceipt
microsoftMarginAttribution = Attribution.sourceAttributionReceipt
  "Microsoft Corporation"
  "Microsoft investor relations / management disclosure"
  "Microsoft FY2026 Q3 investor-relations performance and metrics"
  "Microsoft Investor Relations, FY2026 Q3 performance and metrics"
  "Microsoft investor-relations access carrier"
  Attribution.canonicalCarrier
  "Microsoft Cloud gross-margin discussion, FY2026 Q3"
  "Microsoft Cloud gross margin was 66 percent and Microsoft attributed year-over-year pressure to continued AI infrastructure investment and growing AI-product usage, partly offset by efficiencies."
  Attribution.primarySourceProposition
  "DASHI.Economics.MicrosoftCloudAIMarginPressure2026Exact"
  "source proposition only; no authority to infer incremental AI gross margin or terminal economic viability"
  true true true

nvidiaCoreWeaveAttribution : Attribution.SourceAttributionReceipt
nvidiaCoreWeaveAttribution = Attribution.sourceAttributionReceipt
  "NVIDIA and CoreWeave"
  "NVIDIA/CoreWeave joint company release"
  "Joint company release; SEC exhibit carrier also identified by application owner"
  "NVIDIA/CoreWeave 2026-01-26 company release"
  "company release / SEC-access surface"
  Attribution.canonicalCarrier
  "bounded investment and expanded-platform relationship proposition"
  "NVIDIA invested USD 2 billion in CoreWeave while the companies expanded a relationship involving CoreWeave adoption of NVIDIA platform generations."
  Attribution.primarySourceProposition
  "DASHI.Economics.NvidiaCoreWeaveReflexiveInvestment2026Exact"
  "bounded transaction/relationship proposition only; no authority to infer dollar-for-dollar revenue recycling, fraud, or terminal external demand"
  true true true

coreWeaveFacilityAttribution : Attribution.SourceAttributionReceipt
coreWeaveFacilityAttribution = Attribution.sourceAttributionReceipt
  "CoreWeave"
  "CoreWeave investor relations / issuer disclosure"
  "CoreWeave investor-relations and SEC exhibit surfaces"
  "CoreWeave 2026 financing disclosures"
  "issuer/SEC access carriers"
  Attribution.canonicalCarrier
  "USD 8.5B, USD 3.1B and USD 2.6B facility propositions as separately dated in application owner"
  "CoreWeave disclosed GPU/HPC and customer-contract-backed financing, public syndication/secondary-market features, and a facility whose maturity extends beyond average underlying contract length."
  Attribution.primarySourceProposition
  "DASHI.Economics.CoreWeaveGPUBackedStructuredFinance2026Exact"
  "financing-structure propositions only; no authority to classify the facilities as classical CDOs, resecuritisations, or independent-risk bundles"
  true true true

softBankPrimaryAttribution : Attribution.SourceAttributionReceipt
softBankPrimaryAttribution = Attribution.sourceAttributionReceipt
  "SoftBank Group Corp."
  "SoftBank Group issuer disclosure"
  "SoftBank Group follow-on-investment and bridge-facility releases"
  "SoftBank Group investor-relations releases dated 2026-02-27, 2026-03-27 and 2026-04-01"
  "SoftBank investor-relations carrier"
  Attribution.canonicalCarrier
  "OpenAI follow-on investment, bridge facility and first-tranche borrowing propositions"
  "SoftBank disclosed additional OpenAI investment exposure and borrowing used to fund the first investment tranche."
  Attribution.primarySourceProposition
  "DASHI.Economics.SoftBankOpenAIValuationLeverage2026Exact"
  "transaction/leverage proposition only; no authority to infer OpenAI terminal cash-flow validation or bubble classification"
  true true true

softBankGainSecondaryAttribution : Attribution.SourceAttributionReceipt
softBankGainSecondaryAttribution = Attribution.sourceAttributionReceipt
  "Reuters"
  "Reuters reporting"
  "Reuters news report"
  "Reuters report dated 2026-02-12"
  "Reuters access carrier"
  Attribution.secondaryReportingCarrier
  "reported SoftBank OpenAI investment-gain proposition"
  "Reuters reported an approximately USD 19.8 billion investment gain from SoftBank's OpenAI stake for the October-December 2025 quarter."
  Attribution.secondarySourceReport
  "DASHI.Economics.SoftBankOpenAIValuationLeverage2026Exact"
  "secondary reporting authority only until the corresponding primary accounting receipt is independently recovered"
  false true true

manufacturingAttribution : Attribution.SourceAttributionReceipt
manufacturingAttribution = Attribution.sourceAttributionReceipt
  "TSMC and SK hynix, as separate source owners"
  "TSMC for foundry/packaging proposition; SK hynix for HBM proposition"
  "TSMC AGM materials and SK hynix Q2 2026 business-results materials"
  "respective company investor-relations/publication surfaces"
  "company primary-source carriers"
  Attribution.canonicalCarrier
  "separately bounded TSMC capacity-planning and SK hynix HBM-demand propositions"
  "TSMC reports multi-year AI-related capacity/advanced-packaging planning and a government-support coordinate; SK hynix reports HBM demand, customer LTAs and multi-year contract discussions."
  Attribution.primarySourceProposition
  "DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact"
  "company demand/capacity propositions only; no authority to infer monopoly, permanent chokepoint, quantified scarcity rent or downstream project viability"
  true true true

shortTranscriptAttribution : Attribution.SourceAttributionReceipt
shortTranscriptAttribution = Attribution.sourceAttributionReceipt
  "unknown / not recovered"
  "speaker identity unresolved"
  "YouTube Short IYjxiGUMMKE transcript supplied in chat"
  "https://youtube.com/shorts/IYjxiGUMMKE"
  "user-supplied transcript text"
  Attribution.userSuppliedCarrier
  "claim-by-claim transcript segmentation owned by AIInfrastructureYouTubeShortTranscriptBoundaryExact"
  "The transcript carries multiple claims about US-China capability, chip access, serving constraints, talent, EUV and open-weight deployment."
  Attribution.transcriptProposition
  "DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact"
  "transcript-carrier authority only; each empirical proposition needs its own independent source receipt"
  false false true

marxBoundaryAttribution : Attribution.SourceAttributionReceipt
marxBoundaryAttribution = Attribution.sourceAttributionReceipt
  "Karl Marx"
  "Karl Marx"
  "Capital, Volume I"
  "Capital, Volume I (1867), bounded Chapters 6, 10 and 13 as owned by MarxLabourUnionSourceBoundaryExact"
  "stable edition identified by the upstream Marx source owner"
  Attribution.primaryCarrierMirror
  "labour-power exchange; working-day conflict; co-operation"
  "bounded historical/theoretical context for capital/labour relations, not the modern DASHI reflexive-finance graph"
  Attribution.primarySourceProposition
  "DASHI.Culture.MarxLabourUnionSourceBoundaryExact; downstream cross-pollination by DASHI.Economics.MarxCapitalAIInfrastructureCrossPollinationExact"
  "bounded source-context authority only; DASHI modern economic graph and theorems remain DASHI-owned"
  true true true

------------------------------------------------------------------------
-- Downstream uses explicitly preserve ownership and promotion limits.
------------------------------------------------------------------------

microsoftEconomicUse : Attribution.SourceUseReceipt
microsoftEconomicUse = Attribution.sourceUseReceipt
  microsoftMarginAttribution Attribution.dashiBoundedInterpretation
  true true true true

shortTranscriptUse : Attribution.SourceUseReceipt
shortTranscriptUse = Attribution.sourceUseReceipt
  shortTranscriptAttribution Attribution.dashiBoundedInterpretation
  true true true true

marxEconomicUse : Attribution.SourceUseReceipt
marxEconomicUse = Attribution.sourceUseReceipt
  marxBoundaryAttribution Attribution.dashiBoundedInterpretation
  true true true true

------------------------------------------------------------------------
-- Retain the application owners and their no-promotion boundaries.
------------------------------------------------------------------------

microsoftCalibration : Microsoft.MicrosoftAIMarginPressureCalibration
microsoftCalibration = Microsoft.canonicalMicrosoftAIMarginPressureCalibration

nvidiaCalibration : Nvidia.VendorCustomerReflexivityCalibration
nvidiaCalibration = Nvidia.canonicalVendorCustomerReflexivityCalibration

coreWeaveCalibration : CoreWeave.CoreWeaveStructuredFinanceCalibration
coreWeaveCalibration = CoreWeave.canonicalCoreWeaveStructuredFinanceCalibration

softBankCalibration : SoftBank.SoftBankOpenAIValuationLeverageCalibration
softBankCalibration = SoftBank.canonicalSoftBankOpenAIValuationLeverageCalibration

manufacturingCalibration : Manufacturing.ManufacturingDemandPolicyCalibration
manufacturingCalibration = Manufacturing.canonicalManufacturingDemandPolicyCalibration

shortBoundary : Short.YouTubeShortSourceBoundary
shortBoundary = Short.canonicalYouTubeShortSourceBoundary

marxBoundary : Marx.MarxAIEconomicReadingBoundary
marxBoundary = Marx.canonicalMarxAIEconomicReadingBoundary

------------------------------------------------------------------------
-- Aggregate attribution firewalls.
------------------------------------------------------------------------

accessCarrierStillDoesNotImplyAuthorship :
  Attribution.AccessCarrierImpliesAuthorshipPermission → ⊥
accessCarrierStillDoesNotImplyAuthorship = Attribution.accessCarrierDoesNotAutoPromoteToAuthorship

jointCarrierStillDoesNotAssignEverySentenceJointly :
  Attribution.JointPublicationImpliesEverySentenceJointlyOwnedPermission → ⊥
jointCarrierStillDoesNotAssignEverySentenceJointly =
  Attribution.jointPublicationDoesNotAutoPromoteEverySentenceToJointOwnership

sourceArgumentStillDoesNotOwnDASHIFormalisation :
  Attribution.SourceArgumentImpliesDASHIFormalisationOwnershipPermission → ⊥
sourceArgumentStillDoesNotOwnDASHIFormalisation =
  Attribution.sourceArgumentDoesNotAutoPromoteToDASHIFormalisationOwnership

secondaryReportStillDoesNotBecomePrimaryAuthority :
  Attribution.SecondaryReportImpliesPrimarySourceAuthorityPermission → ⊥
secondaryReportStillDoesNotBecomePrimaryAuthority =
  Attribution.secondaryReportDoesNotAutoPromoteToPrimaryAuthority

transcriptStillDoesNotBecomeIndependentVerification :
  Attribution.TranscriptImpliesIndependentVerificationPermission → ⊥
transcriptStillDoesNotBecomeIndependentVerification =
  Attribution.transcriptDoesNotAutoPromoteToIndependentVerification

sourceBundleStillDoesNotBecomeSystemicClassification :
  Attribution.SourcePropositionImpliesSystemicClassificationPermission → ⊥
sourceBundleStillDoesNotBecomeSystemicClassification =
  Attribution.sourcePropositionDoesNotAutoPromoteToSystemicClassification
