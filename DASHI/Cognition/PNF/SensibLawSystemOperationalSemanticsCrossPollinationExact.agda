module DASHI.Cognition.PNF.SensibLawSystemOperationalSemanticsCrossPollinationExact where

------------------------------------------------------------------------
-- SYSTEM OPERATIONAL SEMANTICS CROSS-POLLINATION
--
-- Generic question:
--   What does the system actually do, for the consumer whose material relation
--   matters, rather than what does it merely declare, authorise or call itself?
--
-- Historical domains remain distinct.  This file imports master-owned Mabo,
-- Billy and Herzog owners directly.  The AI/economics material is still on
-- open draft PR #763, so it is represented by branch-qualified formalisation
-- receipts and is NOT imported as though already merged.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusJuridicalDehumanisationExact as Terra
import DASHI.Cognition.PNF.SensibLawDominantChartEpistemicCompressionCrossPollinationExact as Chart
import DASHI.Law.OperationalDirectionProvenanceBidiExact as Direction
import DASHI.Law.HerzogPoliceCountryColonialityCrossPollinationExact as Herzog

------------------------------------------------------------------------
-- Repository-state provenance for unmerged cross-branch material.
------------------------------------------------------------------------

data FormalisationMergeState : Set where
  mergedOnMaster
  openDraftExternalBranch
  : FormalisationMergeState

record FormalisationProvenanceReceipt : Set where
  constructor formalisation-provenance-receipt
  field
    repository : String
    sourcePR : String
    sourceBranch : String
    sourceHead : String
    sourceModule : String
    boundedFormalProposition : String
    mergeState : FormalisationMergeState
    importedAsKernelDependencyHere : Bool
    sourceFormalisationAutomaticallyWorldTruth : Bool
    sourceFormalisationAutomaticallyWorldTruthIsFalse :
      sourceFormalisationAutomaticallyWorldTruth ≡ false

open FormalisationProvenanceReceipt public

aiCriticalInfrastructureBranchReceipt : FormalisationProvenanceReceipt
aiCriticalInfrastructureBranchReceipt = formalisation-provenance-receipt
  "chboishabba/dashi_agda"
  "PR #763"
  "agent/ai-reflexive-infrastructure-econ"
  "46d265c59800b3efdfe706f4c2b7eca66381f6a6"
  "DASHI/Economics/AICriticalInfrastructurePoliticsCrossPollinationExact.agda"
  "The 'critical infrastructure' label may be locally useful while failing to exhaust commercial return, beneficiary, dependency, sovereignty, distributional and terminal-payer coordinates."
  openDraftExternalBranch
  false
  false refl

aiMarxCapitalBranchReceipt : FormalisationProvenanceReceipt
aiMarxCapitalBranchReceipt = formalisation-provenance-receipt
  "chboishabba/dashi_agda"
  "PR #763"
  "agent/ai-reflexive-infrastructure-econ"
  "46d265c59800b3efdfe706f4c2b7eca66381f6a6"
  "DASHI/Economics/MarxCapitalAIInfrastructureCrossPollinationExact.agda"
  "Capital provision, realised customer revenue, marked valuation exposure, labour relation, debt and terminal payer are distinct coordinates; modern DASHI finance graphs are not attributed to Marx."
  openDraftExternalBranch
  false
  false refl

------------------------------------------------------------------------
-- Declared / authorised / transmitted / realised / distributed are distinct.
------------------------------------------------------------------------

data OperationalLayer : Set where
  declaredLayer
  authorisedLayer
  transmittedLayer
  receivedLayer
  executedLayer
  realisedMaterialLayer
  distributionalLayer
  correctionFeedbackLayer
  : OperationalLayer

record SystemOperationalSemantics : Set where
  constructor system-operational-semantics
  field
    systemReference : String
    declaredReference : String
    realisedConsumerReference : String
    declarationAloneDeterminesRealisedEffect : Bool
    declarationAloneDeterminesRealisedEffectIsFalse :
      declarationAloneDeterminesRealisedEffect ≡ false
    authorityAloneDeterminesExecution : Bool
    authorityAloneDeterminesExecutionIsFalse : authorityAloneDeterminesExecution ≡ false
    aggregateLabelExhaustsDistribution : Bool
    aggregateLabelExhaustsDistributionIsFalse : aggregateLabelExhaustsDistribution ≡ false
    correctionFeedbackCanRemainOpen : Bool
    correctionFeedbackCanRemainOpenIsTrue : correctionFeedbackCanRemainOpen ≡ true

open SystemOperationalSemantics public

canonicalSystemOperationalSemantics : SystemOperationalSemantics
canonicalSystemOperationalSemantics = system-operational-semantics
  "generic declared/authorised/realised system"
  "official declaration, classification, authorisation or public label"
  "realised situated effect, material distribution, authority relation and correction state"
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Billy: a remedy is not the declaration of a remedy.
------------------------------------------------------------------------

billyOperationalSemantics : Billy.RemedyOperationalSemantics
billyOperationalSemantics = Billy.canonicalRemedyOperationalSemantics

billyDeclarationDoesNotCloseRemedy :
  Billy.declarationAloneClosesRemedy billyOperationalSemantics ≡ false
billyDeclarationDoesNotCloseRemedy = refl

billyMeetingDoesNotCloseNeedsAssessment :
  Billy.consultationMeetingAloneClosesNeedsAssessment billyOperationalSemantics ≡ false
billyMeetingDoesNotCloseNeedsAssessment = refl

billyRealisedOutcomeRequiresCommunityFeedback :
  Billy.implementationMustBeMonitoredAgainstCommunityDefinedOutcome billyOperationalSemantics ≡ true
billyRealisedOutcomeRequiresCommunityFeedback = refl

billyFullReparationResidualStillLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
billyFullReparationResidualStillLive = refl

------------------------------------------------------------------------
-- Herzog: command existence/authorisation is not field receipt/execution.
------------------------------------------------------------------------

herzogCommandBoundary : Direction.CommandFieldCommunicationBoundary
herzogCommandBoundary = Direction.canonicalCommandFieldBoundary

commandAuthorisationDoesNotDetermineFieldReceipt :
  Direction.commandAuthorisationImpliesFieldReceipt herzogCommandBoundary ≡ false
commandAuthorisationDoesNotDetermineFieldReceipt = refl

directionExistenceDoesNotDetermineLawfulExecution :
  Direction.directionExistenceImpliesLawfulExecution herzogCommandBoundary ≡ false
directionExistenceDoesNotDetermineLawfulExecution = refl

laterDiscoveryDoesNotRewriteHistoricalReceipt :
  Direction.laterDiscoveryOfDirectionRetroactivelySuppliesFieldReceipt herzogCommandBoundary ≡ false
laterDiscoveryDoesNotRewriteHistoricalReceipt = refl

herzogPublicOrderLabelDoesNotExhaustPoliticalMeaning :
  Herzog.publicOrderLabelExhaustsPoliticalMeaning Herzog.canonicalHerzogColonialityFibre ≡ false
herzogPublicOrderLabelDoesNotExhaustPoliticalMeaning = refl

herzogSecurityRationaleDoesNotProveLawfulExercise :
  Herzog.securityRationaleProvesLawfulExercise Herzog.canonicalHerzogColonialityFibre ≡ false
herzogSecurityRationaleDoesNotProveLawfulExercise = refl

------------------------------------------------------------------------
-- Terra nullius: operational legal capacity denial is itself legally material.
------------------------------------------------------------------------

terraOperationalReading : Terra.FunctionalSystemReading
terraOperationalReading = Terra.terraNulliusSystemReading

terraEffectCanBeClassifiedFromOperation :
  Terra.operationCanBeClassifiedFromEffects terraOperationalReading ≡ true
terraEffectCanBeClassifiedFromOperation = refl

terraEffectClassificationIsNotSpeakerQuotation :
  Terra.effectClassificationEqualsSpeakerQuotation terraOperationalReading ≡ false
terraEffectClassificationIsNotSpeakerQuotation = refl

terraJuridicalDehumanisation : Terra.FunctionalJuridicalDehumanisation
terraJuridicalDehumanisation = Terra.terraNulliusFunctionalJuridicalDehumanisation

terraDeniedConstitutiveLocalLawStanding :
  Terra.localLawDeniedConstitutiveStanding terraJuridicalDehumanisation ≡ true
terraDeniedConstitutiveLocalLawStanding = refl

terraDeniedConstitutiveSovereignStanding :
  Terra.indigenousSovereigntyDeniedConstitutiveStanding terraJuridicalDehumanisation ≡ true
terraDeniedConstitutiveSovereignStanding = refl

terraDeniedOccupancyProprietaryStanding :
  Terra.occupancyDeniedProprietaryStanding terraJuridicalDehumanisation ≡ true
terraDeniedOccupancyProprietaryStanding = refl

------------------------------------------------------------------------
-- Two-Eyed Seeing / Country: realised remedy cannot be reduced to extracting
-- a community proposition into a State-owned observer.
------------------------------------------------------------------------

billyConsultationBoundary : Billy.RemedyConsultationBoundary
billyConsultationBoundary = Billy.canonicalRemedyConsultationBoundary

hearingObservationDoesNotTransferAuthority :
  Billy.hearingCommunityObservationEqualsTransferringAuthority billyConsultationBoundary ≡ false
hearingObservationDoesNotTransferAuthority = refl

scientificGovernmentObservationDoesNotExhaustCountryKnowledge :
  Billy.scientificGovernmentObservationExhaustsCountryKnowledge billyConsultationBoundary ≡ false
scientificGovernmentObservationDoesNotExhaustCountryKnowledge = refl

remedyCanCoordinateWithoutEpistemicFusion :
  Billy.remedyCanBeCoordinatedWithoutEpistemicFusion billyConsultationBoundary ≡ true
remedyCanCoordinateWithoutEpistemicFusion = refl

------------------------------------------------------------------------
-- Shared operational pattern across domains, without historical identity.
------------------------------------------------------------------------

data OperationalDomain : Set where
  terraNulliusDomain
  billyRemedyDomain
  herzogPolicingDomain
  aiInfrastructureEconomicsDomain
  : OperationalDomain

data OperationalFailureMode : Set where
  declarationRealisationGap
  authorisationExecutionGap
  labelDistributionGap
  recognitionAuthorityGap
  correctionFeedbackGap
  : OperationalFailureMode

record CrossDomainOperationalBridge : Set where
  constructor cross-domain-operational-bridge
  field
    domain : OperationalDomain
    dominantSurface : String
    materialResidual : String
    failureMode : OperationalFailureMode
    sourceOrFormalOwner : String
    sameHistoricalMechanismAsOtherDomains : Bool
    sameHistoricalMechanismAsOtherDomainsIsFalse :
      sameHistoricalMechanismAsOtherDomains ≡ false

open CrossDomainOperationalBridge public

terraBridge : CrossDomainOperationalBridge
terraBridge = cross-domain-operational-bridge
  terraNulliusDomain
  "settled-colony / terra-nullius juridical classification"
  "actual Indigenous law, polity, occupancy, sovereignty and proprietorship excluded from constitutive legal standing"
  recognitionAuthorityGap
  "SensibLawMaboTerraNulliusJuridicalDehumanisationExact"
  false refl

billyBridge : CrossDomainOperationalBridge
billyBridge = cross-domain-operational-bridge
  billyRemedyDomain
  "government commitments, consultation, funding, adaptation and monitoring declarations"
  "whether each required remedy coordinate is realised for affected communities"
  declarationRealisationGap
  "SensibLawBillyEffectiveRemedyTwoEyedSeeingExact"
  false refl

herzogBridge : CrossDomainOperationalBridge
herzogBridge = cross-domain-operational-bridge
  herzogPolicingDomain
  "public-order/security label plus command-level authorisation"
  "political content, command receipt, opportunity to comply, force path, exit access and lawful execution"
  authorisationExecutionGap
  "OperationalDirectionProvenanceBidiExact + HerzogPoliceCountryColonialityCrossPollinationExact"
  false refl

aiEconomicsBridge : CrossDomainOperationalBridge
aiEconomicsBridge = cross-domain-operational-bridge
  aiInfrastructureEconomicsDomain
  "critical-infrastructure / strategic-value / valuation / adoption surface"
  "terminal payer, realised revenue, beneficiary distribution, dependency, energy-water burden and commercial viability"
  labelDistributionGap
  "PR #763 branch-qualified formalisation receipts; not imported as merged code here"
  false refl

------------------------------------------------------------------------
-- A system-is-what-it-does consumer is effect-indexed, not slogan-indexed.
------------------------------------------------------------------------

data SystemEvaluationConsumer : Set where
  declaredComplianceConsumer
  realisedRemedyConsumer
  lawfulExecutionConsumer
  materialDistributionConsumer
  sovereigntyAuthorityConsumer
  : SystemEvaluationConsumer

data SystemEvaluationSurface : Set where
  declarationSurface
  implementationSurface
  executionSurface
  distributionSurface
  authoritySurface
  : SystemEvaluationSurface

requiredSurface : SystemEvaluationConsumer → SystemEvaluationSurface
requiredSurface declaredComplianceConsumer = declarationSurface
requiredSurface realisedRemedyConsumer = implementationSurface
requiredSurface lawfulExecutionConsumer = executionSurface
requiredSurface materialDistributionConsumer = distributionSurface
requiredSurface sovereigntyAuthorityConsumer = authoritySurface

realisedRemedyDoesNotUseDeclarationSurface :
  requiredSurface realisedRemedyConsumer ≡ implementationSurface
realisedRemedyDoesNotUseDeclarationSurface = refl

lawfulExecutionDoesNotUseAuthorisationAsTerminalSurface :
  requiredSurface lawfulExecutionConsumer ≡ executionSurface
lawfulExecutionDoesNotUseAuthorisationAsTerminalSurface = refl

materialDistributionDoesNotUseStrategicLabelAsTerminalSurface :
  requiredSurface materialDistributionConsumer ≡ distributionSurface
materialDistributionDoesNotUseStrategicLabelAsTerminalSurface = refl

sovereigntyAuthorityDoesNotUseRecognitionAsTerminalSurface :
  requiredSurface sovereigntyAuthorityConsumer ≡ authoritySurface
sovereigntyAuthorityDoesNotUseRecognitionAsTerminalSurface = refl

------------------------------------------------------------------------
-- Dominant-chart connection.
------------------------------------------------------------------------

countryVocabularyBoundary : Chart.CountryRelationVocabularyBoundary
countryVocabularyBoundary = Chart.canonicalCountryRelationVocabularyBoundary

countryIsNotAssetByDefault :
  Chart.countryRelationIsAssetByDefault countryVocabularyBoundary ≡ false
countryIsNotAssetByDefault = refl

cashIncomeIsNotSovereignWellbeingMeasure :
  Chart.cashIncomeIsSovereignMeasureOfWellbeing countryVocabularyBoundary ≡ false
cashIncomeIsNotSovereignWellbeingMeasure = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DeclarationEqualsRealisation : Set where
data AuthorisationEqualsExecution : Set where
data StrategicLabelEqualsMaterialDistribution : Set where
data GovernmentObservationEqualsCountryKnowledge : Set where
data FunctionalLegalEffectClassificationEqualsSourceQuotation : Set where
data CrossDomainOperationalPatternProvesHistoricalIdentity : Set where
data UnmergedBranchFormalisationIsMergedKernelDependency : Set where

declarationDoesNotEqualRealisation : DeclarationEqualsRealisation → ⊥
declarationDoesNotEqualRealisation ()

authorisationDoesNotEqualExecution : AuthorisationEqualsExecution → ⊥
authorisationDoesNotEqualExecution ()

strategicLabelDoesNotEqualMaterialDistribution : StrategicLabelEqualsMaterialDistribution → ⊥
strategicLabelDoesNotEqualMaterialDistribution ()

governmentObservationDoesNotEqualCountryKnowledge : GovernmentObservationEqualsCountryKnowledge → ⊥
governmentObservationDoesNotEqualCountryKnowledge ()

functionalEffectDoesNotBecomeSourceQuotation : FunctionalLegalEffectClassificationEqualsSourceQuotation → ⊥
functionalEffectDoesNotBecomeSourceQuotation ()

sharedOperationalPatternDoesNotMergeHistories : CrossDomainOperationalPatternProvesHistoricalIdentity → ⊥
sharedOperationalPatternDoesNotMergeHistories ()

unmergedFormalisationDoesNotBecomeMergedDependency : UnmergedBranchFormalisationIsMergedKernelDependency → ⊥
unmergedFormalisationDoesNotBecomeMergedDependency ()
