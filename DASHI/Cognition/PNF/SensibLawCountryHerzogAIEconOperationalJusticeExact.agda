module DASHI.Cognition.PNF.SensibLawCountryHerzogAIEconOperationalJusticeExact where

------------------------------------------------------------------------
-- COUNTRY x HERZOG x AI/ECON OPERATIONAL JUSTICE
--
-- Current-master cross-pollination.  This owner does not merge histories or
-- doctrines.  It reuses the same operational question across distinct domains:
--
--   What does the system actually realise for the affected/material consumer,
--   and which coordinates are erased by the dominant public label?
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Justice
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Law.OperationalDirectionProvenanceBidiExact as Direction
import DASHI.Law.HerzogPoliceCountryColonialityCrossPollinationExact as Herzog
import DASHI.Economics.AICriticalInfrastructurePoliticsCrossPollinationExact as AIInfra
import DASHI.Economics.AITerminalPayerEconomicValidationExact as AIPayer
import DASHI.Economics.MarxCapitalAIInfrastructureCrossPollinationExact as MarxAI

------------------------------------------------------------------------
-- Existing realised-justice state remains the Country/native-title anchor.
------------------------------------------------------------------------

countryJusticeState : Justice.CorrectionWithoutFullRepair
countryJusticeState = Justice.currentCorrectionWithoutFullRepair

nativeTitleCorrectionOccurred :
  Justice.doctrinalCorrectionOccurred countryJusticeState ≡ true
nativeTitleCorrectionOccurred = refl

landReturnStillUnrealised :
  Justice.landReturnRealised countryJusticeState ≡ false
landReturnStillUnrealised = refl

materialRepairStillUnrealised :
  Justice.materialRepairRealised countryJusticeState ≡ false
materialRepairStillUnrealised = refl

fullRemedyStillUnclosed :
  Justice.fullEffectiveRemedyPubliclyClosed countryJusticeState ≡ false
fullRemedyStillUnclosed = refl

------------------------------------------------------------------------
-- Herzog: public-order/security classification does not determine lawful field
-- implementation or preserve political/coloniality content automatically.
------------------------------------------------------------------------

herzogDirectionBoundary : Direction.CommandFieldCommunicationBoundary
herzogDirectionBoundary = Direction.canonicalCommandFieldBoundary

commandAuthorisationDoesNotDetermineFieldReceipt :
  Direction.commandAuthorisationImpliesFieldReceipt herzogDirectionBoundary ≡ false
commandAuthorisationDoesNotDetermineFieldReceipt = refl

commandExistenceDoesNotDetermineLawfulExecution :
  Direction.directionExistenceImpliesLawfulExecution herzogDirectionBoundary ≡ false
commandExistenceDoesNotDetermineLawfulExecution = refl

herzogColonialityFibre : Herzog.HerzogPolicingColonialityFibre
herzogColonialityFibre = Herzog.canonicalHerzogColonialityFibre

publicOrderDoesNotExhaustPoliticalMeaning :
  Herzog.publicOrderLabelExhaustsPoliticalMeaning herzogColonialityFibre ≡ false
publicOrderDoesNotExhaustPoliticalMeaning = refl

securityRationaleDoesNotProveLawfulExercise :
  Herzog.securityRationaleProvesLawfulExercise herzogColonialityFibre ≡ false
securityRationaleDoesNotProveLawfulExercise = refl

------------------------------------------------------------------------
-- AI/econ: strategic/critical-infrastructure usefulness does not collapse the
-- terminal-payer, beneficiary, dependency, sovereignty or distributional axes.
------------------------------------------------------------------------

criticalInfrastructureClaimNeedsProducer :
  AIInfra.CriticalInfrastructureClaim → AIInfra.CriticalInfrastructureProducer
criticalInfrastructureClaimNeedsProducer = AIInfra.reverseCriticalInfrastructure

publicBenefitClaimNeedsDistributionProducer :
  AIInfra.reverseCriticalInfrastructure AIInfra.publicSupportBenefitsDomesticPublic
  ≡ AIInfra.beneficiaryDistributionProducer
publicBenefitClaimNeedsDistributionProducer = refl

independentDemandClaimNeedsTerminalPayerProducer :
  AIInfra.reverseCriticalInfrastructure AIInfra.policyBackingRevealsIndependentDemand
  ≡ AIInfra.terminalPayerProducer
independentDemandClaimNeedsTerminalPayerProducer = refl

surroundingAISuccessSignalsDoNotManufactureTerminalValidation :
  AIPayer.SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingAISuccessSignalsDoNotManufactureTerminalValidation =
  AIPayer.surroundingSignalsDoNotAutoPromoteToEconomicValidation

------------------------------------------------------------------------
-- Marx/capital lane: observed finance/valuation is not realised productive or
-- external economic flow, and the bounded source context does not own DASHI's
-- modern infrastructure graph.
------------------------------------------------------------------------

marxAIBoundary : MarxAI.MarxAIEconomicReadingBoundary
marxAIBoundary = MarxAI.canonicalMarxAIEconomicReadingBoundary

modernFinanceGraphIsNotMarxTheorem :
  MarxAI.dashiReflexiveFinanceGraphIsMarxTheorem marxAIBoundary ≡ false
modernFinanceGraphIsNotMarxTheorem = refl

valuationGainDoesNotEqualRealisedCash :
  MarxAI.valuationGainEqualsRealisedSurplusOrExternalCash marxAIBoundary ≡ false
valuationGainDoesNotEqualRealisedCash = refl

capitalRelationAloneDoesNotExhaustAIRegime :
  MarxAI.capitalRelationAloneExhaustsCurrentAIRegime marxAIBoundary ≡ false
capitalRelationAloneDoesNotExhaustAIRegime = refl

------------------------------------------------------------------------
-- Cross-domain operator: declared label, realised effect, distribution and
-- correction are different coordinates.
------------------------------------------------------------------------

data OperationalJusticeDomain : Set where
  countryNativeTitleDomain : OperationalJusticeDomain
  herzogPolicingDomain : OperationalJusticeDomain
  aiInfrastructureDomain : OperationalJusticeDomain


data DominantSurface : Set where
  recognisedNativeTitleSurface : DominantSurface
  publicOrderSecuritySurface : DominantSurface
  criticalInfrastructureStrategicSurface : DominantSurface


data MaterialConsumer : Set where
  countryAuthorityAndLandControlConsumer : MaterialConsumer
  lawfulFieldExecutionAndPoliticalContentConsumer : MaterialConsumer
  terminalPayerBeneficiaryDependencyConsumer : MaterialConsumer


surfaceFor : OperationalJusticeDomain → DominantSurface
surfaceFor countryNativeTitleDomain = recognisedNativeTitleSurface
surfaceFor herzogPolicingDomain = publicOrderSecuritySurface
surfaceFor aiInfrastructureDomain = criticalInfrastructureStrategicSurface

consumerFor : OperationalJusticeDomain → MaterialConsumer
consumerFor countryNativeTitleDomain = countryAuthorityAndLandControlConsumer
consumerFor herzogPolicingDomain = lawfulFieldExecutionAndPoliticalContentConsumer
consumerFor aiInfrastructureDomain = terminalPayerBeneficiaryDependencyConsumer

record OperationalJusticeCrossDomainReceipt : Set where
  constructor operational-justice-cross-domain-receipt
  field
    domain : OperationalJusticeDomain
    dominantSurfaceReference : String
    consumerReference : String
    dominantSurfaceMayBeLocallyUseful : Bool
    dominantSurfaceMayBeLocallyUsefulIsTrue : dominantSurfaceMayBeLocallyUseful ≡ true
    dominantSurfaceExhaustsMaterialConsumer : Bool
    dominantSurfaceExhaustsMaterialConsumerIsFalse :
      dominantSurfaceExhaustsMaterialConsumer ≡ false
    sourceOrFormalOwner : String
    sharedStructureImpliesHistoricalIdentity : Bool
    sharedStructureImpliesHistoricalIdentityIsFalse :
      sharedStructureImpliesHistoricalIdentity ≡ false

open OperationalJusticeCrossDomainReceipt public

countryOperationalReceipt : OperationalJusticeCrossDomainReceipt
countryOperationalReceipt = operational-justice-cross-domain-receipt
  countryNativeTitleDomain
  "Native Title doctrinal recognition"
  "equal sovereignty, Country/land control, material repair, community-defined realised justice"
  true refl false refl
  "SensibLawCountrySystemRealisedJusticeBidiExact"
  false refl

herzogOperationalReceipt : OperationalJusticeCrossDomainReceipt
herzogOperationalReceipt = operational-justice-cross-domain-receipt
  herzogPolicingDomain
  "public order / security / command-authorisation surface"
  "political content, direction transmission/receipt, opportunity to comply, force path, exit access and lawful execution"
  true refl false refl
  "OperationalDirectionProvenanceBidiExact + HerzogPoliceCountryColonialityCrossPollinationExact"
  false refl

aiOperationalReceipt : OperationalJusticeCrossDomainReceipt
aiOperationalReceipt = operational-justice-cross-domain-receipt
  aiInfrastructureDomain
  "critical-infrastructure / strategic-value / usage / valuation surface"
  "terminal payer, realised revenue, beneficiary distribution, dependency, sovereignty, energy-water burden and commercial viability"
  true refl false refl
  "AICriticalInfrastructurePoliticsCrossPollinationExact + AITerminalPayerEconomicValidationExact + MarxCapitalAIInfrastructureCrossPollinationExact"
  false refl

------------------------------------------------------------------------
-- POSIWID: correction handling is itself observable system behaviour.
------------------------------------------------------------------------

operationalBoundary : POSIWID.OperationalDescriptionBoundary
operationalBoundary = POSIWID.canonicalOperationalDescriptionBoundary

observedOperationMayClassifyWhatSystemDoes :
  POSIWID.observedOperationMayClassifyWhatSystemDoes operationalBoundary ≡ true
observedOperationMayClassifyWhatSystemDoes = refl

declaredPurposeDoesNotOverrideRealisedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect operationalBoundary ≡ false
declaredPurposeDoesNotOverrideRealisedEffect = refl

correctionResponseIsPartOfSystemOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation operationalBoundary ≡ true
correctionResponseIsPartOfSystemOperation = refl

------------------------------------------------------------------------
-- Shared epistemic pattern: a dominant surface can be technically/local-useful
-- yet insufficient for a different consumer.  The formal shape is shared; the
-- source histories and politics are not thereby identified.
------------------------------------------------------------------------

compressionBoundary : Compression.DominantChartEpistemicCompressionBoundary
compressionBoundary = Compression.canonicalDominantChartEpistemicCompressionBoundary

usefulObserverMayStillBeLossy :
  Compression.usefulObserverMayStillBeLossy compressionBoundary ≡ true
usefulObserverMayStillBeLossy = refl

observerOutputIsNotOntologyByDefault :
  Compression.observerOutputIsOntologyByDefault compressionBoundary ≡ false
observerOutputIsNotOntologyByDefault = refl

sharedFormalFailureDoesNotMergePolitics :
  Compression.sharedFormalFailureImpliesSharedPolitics compressionBoundary ≡ false
sharedFormalFailureDoesNotMergePolitics = refl

------------------------------------------------------------------------
-- Colonial/economic cross-pollination without collapsing one into the other.
------------------------------------------------------------------------

data ColonialEconomicAuditCoordinate : Set where
  authorityToDefineLegibleValue : ColonialEconomicAuditCoordinate
  authorityToDefineLegibleSecurity : ColonialEconomicAuditCoordinate
  authorityToDefineLegibleProperty : ColonialEconomicAuditCoordinate
  distributionOfMaterialBenefit : ColonialEconomicAuditCoordinate
  distributionOfMaterialBurden : ColonialEconomicAuditCoordinate
  correctionChannelAccess : ColonialEconomicAuditCoordinate


record ColonialEconomicAuditBoundary : Set where
  constructor colonial-economic-audit-boundary
  field
    crownPropertyRecognitionExhaustsCountryRelation : Bool
    crownPropertyRecognitionExhaustsCountryRelationIsFalse :
      crownPropertyRecognitionExhaustsCountryRelation ≡ false
    securityClassificationExhaustsPoliticalRelation : Bool
    securityClassificationExhaustsPoliticalRelationIsFalse :
      securityClassificationExhaustsPoliticalRelation ≡ false
    marketValuationExhaustsSocialEcologicalValue : Bool
    marketValuationExhaustsSocialEcologicalValueIsFalse :
      marketValuationExhaustsSocialEcologicalValue ≡ false
    strategicInvestmentExhaustsWhoBenefitsAndPays : Bool
    strategicInvestmentExhaustsWhoBenefitsAndPaysIsFalse :
      strategicInvestmentExhaustsWhoBenefitsAndPays ≡ false
    theseFailuresProveOneHistoricalColonialMechanism : Bool
    theseFailuresProveOneHistoricalColonialMechanismIsFalse :
      theseFailuresProveOneHistoricalColonialMechanism ≡ false

open ColonialEconomicAuditBoundary public

canonicalColonialEconomicAuditBoundary : ColonialEconomicAuditBoundary
canonicalColonialEconomicAuditBoundary = colonial-economic-audit-boundary
  false refl
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- BIDI reverse route: ask for the producer the dominant surface lacks.
------------------------------------------------------------------------

data OperationalJusticeClaim : Set where
  nativeTitleHasRealisedEqualSovereignty : OperationalJusticeClaim
  herzogFieldActionWasLawfullyGovernedByDirection : OperationalJusticeClaim
  aiPublicSupportProducesDomesticPublicBenefit : OperationalJusticeClaim
  aiPolicyBackingShowsIndependentDemand : OperationalJusticeClaim


data OperationalJusticeProducer : Set where
  equalSovereigntyRealisationProducer : OperationalJusticeProducer
  fieldReceiptAndLawfulExecutionProducer : OperationalJusticeProducer
  beneficiaryDistributionProducer : OperationalJusticeProducer
  terminalPayerProducer : OperationalJusticeProducer


reverseOperationalJustice : OperationalJusticeClaim → OperationalJusticeProducer
reverseOperationalJustice nativeTitleHasRealisedEqualSovereignty = equalSovereigntyRealisationProducer
reverseOperationalJustice herzogFieldActionWasLawfullyGovernedByDirection = fieldReceiptAndLawfulExecutionProducer
reverseOperationalJustice aiPublicSupportProducesDomesticPublicBenefit = beneficiaryDistributionProducer
reverseOperationalJustice aiPolicyBackingShowsIndependentDemand = terminalPayerProducer

nativeTitleEqualSovereigntyNeedsRealisationProducer :
  reverseOperationalJustice nativeTitleHasRealisedEqualSovereignty
  ≡ equalSovereigntyRealisationProducer
nativeTitleEqualSovereigntyNeedsRealisationProducer = refl

herzogLawfulFieldActionNeedsReceiptAndExecutionProducer :
  reverseOperationalJustice herzogFieldActionWasLawfullyGovernedByDirection
  ≡ fieldReceiptAndLawfulExecutionProducer
herzogLawfulFieldActionNeedsReceiptAndExecutionProducer = refl

aiPublicBenefitNeedsDistributionProducer :
  reverseOperationalJustice aiPublicSupportProducesDomesticPublicBenefit
  ≡ beneficiaryDistributionProducer
aiPublicBenefitNeedsDistributionProducer = refl

aiIndependentDemandNeedsTerminalPayer :
  reverseOperationalJustice aiPolicyBackingShowsIndependentDemand
  ≡ terminalPayerProducer
aiIndependentDemandNeedsTerminalPayer = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data NativeTitleRecognitionEqualsLandReturn : Set where
data CommandAuthorisationEqualsLawfulExecution : Set where
data CriticalInfrastructureLabelEqualsPublicBenefit : Set where
data StrategicValueEqualsExternalEconomicValidation : Set where
data SharedOperationalPatternEqualsSharedHistoricalMechanism : Set where

aNativeTitleRecognitionDoesNotEqualLandReturn : NativeTitleRecognitionEqualsLandReturn → ⊥
aNativeTitleRecognitionDoesNotEqualLandReturn ()

commandAuthorisationDoesNotEqualLawfulExecution : CommandAuthorisationEqualsLawfulExecution → ⊥
commandAuthorisationDoesNotEqualLawfulExecution ()

criticalInfrastructureLabelDoesNotEqualPublicBenefit : CriticalInfrastructureLabelEqualsPublicBenefit → ⊥
criticalInfrastructureLabelDoesNotEqualPublicBenefit ()

strategicValueDoesNotEqualExternalEconomicValidation : StrategicValueEqualsExternalEconomicValidation → ⊥
strategicValueDoesNotEqualExternalEconomicValidation ()

sharedOperationalPatternDoesNotMergeHistoricalMechanisms :
  SharedOperationalPatternEqualsSharedHistoricalMechanism → ⊥
sharedOperationalPatternDoesNotMergeHistoricalMechanisms ()
