module DASHI.Cognition.PNF.SensibLawCountryRemedyTerminalValidationCrossPollinationExact where

------------------------------------------------------------------------
-- COUNTRY / REMEDY / TERMINAL VALIDATION CROSS-POLLINATION
--
-- Existing source propositions remain owned upstream:
--   * Mabo / terra-nullius judicial propositions;
--   * Human Rights Committee Billy Views and Australian responses;
--   * Pabai / negligence authority receipts;
--   * Kimmerer / Two-Eyed Seeing / LES source registries;
--   * AI terminal-payer economic formalism.
--
-- The cross-domain correspondences below are DASHI/SensibLaw theorem shapes.
-- Formal similarity does not transfer source authorship or legal authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TerminalRealisationValidationExact as Terminal
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Economics.AITerminalPayerEconomicValidationExact as AI
import DASHI.Environment.LESCountryExternalityRealisationExact as LESCountry
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Personhood
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

------------------------------------------------------------------------
-- Three terminal consumers: external payer, realised remedy, realised
-- socio-ecological/Country outcome.  They share validation topology, not domain
-- semantics.
------------------------------------------------------------------------

data TerminalValidationDomain : Set where
  externalEconomicPayerValidation
  effectiveRemedyRealisation
  countrySocioEcologicalRealisation
  : TerminalValidationDomain

data ValidationStatus : Set where
  surroundingSignalsOnly
  terminalReceiptPresent
  residualOpen
  : ValidationStatus

record CrossDomainValidationBoundary : Set where
  constructor cross-domain-validation-boundary
  field
    sameValidationTopology : Bool
    sameValidationTopologyIsTrue : sameValidationTopology ≡ true
    sameDomainSemantics : Bool
    sameDomainSemanticsIsFalse : sameDomainSemantics ≡ false
    sameSourceAuthority : Bool
    sameSourceAuthorityIsFalse : sameSourceAuthority ≡ false
    terminalConsumerMustRemainExplicit : Bool
    terminalConsumerMustRemainExplicitIsTrue :
      terminalConsumerMustRemainExplicit ≡ true

open CrossDomainValidationBoundary public

canonicalCrossDomainValidationBoundary : CrossDomainValidationBoundary
canonicalCrossDomainValidationBoundary = cross-domain-validation-boundary
  true refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Exact upstream firewalls.
------------------------------------------------------------------------

aiSurroundingSignalsDoNotManufactureTerminalPayer :
  AI.SurroundingSignalsImplyEconomicValidationPermission → ⊥
aiSurroundingSignalsDoNotManufactureTerminalPayer =
  AI.surroundingSignalsDoNotAutoPromoteToEconomicValidation

billyFullReparationRemainsTerminalResidual :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
billyFullReparationRemainsTerminalResidual = refl

landCountryControlRemainsOperationalResidual :
  Country.currentOperationalJusticeState Country.landAndCountryControl
  ≡ Country.residualOpen
landCountryControlRemainsOperationalResidual = refl

compensationReparationRemainsOperationalResidual :
  Country.currentOperationalJusticeState Country.compensationAndReparation
  ≡ Country.residualOpen
compensationReparationRemainsOperationalResidual = refl

------------------------------------------------------------------------
-- Terra nullius: the issue is juridical constitutivity, not a biological quote.
------------------------------------------------------------------------

terraNulliusFoundationalActorWasJuridicallyErased :
  Personhood.personhoodState Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ Personhood.juridicallyErasedActor
terraNulliusFoundationalActorWasJuridicallyErased = refl

terraNulliusLawWasActuallyPresent :
  Personhood.lawActuallyPresent Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ true
terraNulliusLawWasActuallyPresent = refl

terraNulliusPolityWasActuallyPresent :
  Personhood.polityActuallyPresent Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ true
terraNulliusPolityWasActuallyPresent = refl

terraNulliusLawDidNotCountAgainstUnilateralAcquisition :
  Personhood.lawCountsAgainstUnilateralAcquisition
    Personhood.terraNulliusFoundationalJuridicalPersonhood ≡ false
terraNulliusLawDidNotCountAgainstUnilateralAcquisition = refl

terraNulliusSovereigntyDidNotCountAgainstUnilateralAcquisition :
  Personhood.sovereigntyCountsAgainstUnilateralAcquisition
    Personhood.terraNulliusFoundationalJuridicalPersonhood ≡ false
terraNulliusSovereigntyDidNotCountAgainstUnilateralAcquisition = refl

------------------------------------------------------------------------
-- Realised remedy: declarations and inputs are surrounding signals.
------------------------------------------------------------------------

terminalBoundary : Terminal.TerminalRealisationBoundary
terminalBoundary = Terminal.canonicalTerminalRealisationBoundary

apologyDoesNotEqualRealisation :
  Terminal.declarationEqualsRealisation terminalBoundary ≡ false
apologyDoesNotEqualRealisation = refl

fundingDoesNotEqualRealisation :
  Terminal.fundingEqualsRealisation terminalBoundary ≡ false
fundingDoesNotEqualRealisation = refl

consultationDoesNotEqualRealisation :
  Terminal.consultationEqualsRealisation terminalBoundary ≡ false
consultationDoesNotEqualRealisation = refl

recognitionDoesNotEqualRealisation :
  Terminal.recognitionEqualsRealisation terminalBoundary ≡ false
recognitionDoesNotEqualRealisation = refl

billyConsultationDoesNotEqualFullReparation : Billy.ConsultationEqualsFullReparation → ⊥
billyConsultationDoesNotEqualFullReparation = Billy.consultationDoesNotEqualFullReparation

billyFundingDoesNotEqualCompensation : Billy.AdaptationFundingEqualsCompensation → ⊥
billyFundingDoesNotEqualCompensation = Billy.adaptationFundingDoesNotEqualCompensation

------------------------------------------------------------------------
-- POSIWID: realised correction/output belongs to operational classification.
------------------------------------------------------------------------

operationalBoundary : POSIWID.OperationalDescriptionBoundary
operationalBoundary = POSIWID.canonicalOperationalDescriptionBoundary

correctionResponseCountsAsOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation operationalBoundary ≡ true
correctionResponseCountsAsOperation = refl

declaredPurposeCannotOverrideRepeatedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect operationalBoundary ≡ false
declaredPurposeCannotOverrideRepeatedEffect = refl

------------------------------------------------------------------------
-- Externalities: monetary and carbon observers remain partial.
------------------------------------------------------------------------

marketRevenueDoesNotExhaustCountry :
  LESCountry.marketRevenueExhaustsCountryValue
    LESCountry.canonicalExternalityAccountingBoundary ≡ false
marketRevenueDoesNotExhaustCountry = refl

carbonPriceDoesNotExhaustClimateValue :
  LESCountry.carbonPriceExhaustsClimateValue
    LESCountry.canonicalExternalityAccountingBoundary ≡ false
carbonPriceDoesNotExhaustClimateValue = refl

carbonDoesNotExhaustCommunityAuthority :
  LESCountry.carbonMetricExhaustsCommunityAuthority
    LESCountry.canonicalExternalityAccountingBoundary ≡ false
carbonDoesNotExhaustCommunityAuthority = refl

fiscalTransferDoesNotExhaustMaterialRepair :
  LESCountry.fiscalTransferExhaustsMaterialRepair
    LESCountry.canonicalExternalityAccountingBoundary ≡ false
fiscalTransferDoesNotExhaustMaterialRepair = refl

unpricedDoesNotMeanNonexistent :
  LESCountry.unpricedEffectMeansEffectDoesNotExist
    LESCountry.canonicalExternalityAccountingBoundary ≡ false
unpricedDoesNotMeanNonexistent = refl

------------------------------------------------------------------------
-- Duty of care cross-pollination.
--
-- Rich climate/land/externality evidence can be relevant to factual or
-- relational duty coordinates.  It does not manufacture doctrinal and
-- institutional predicates, causation or compensability.
------------------------------------------------------------------------

data ExternalityDutyBridgeRole : Set where
  mayInformForeseeability
  mayInformKnowledge
  mayInformControl
  mayInformVulnerability
  mayInformHarmCharacterisation
  cannotAutoPayCausation
  cannotAutoPayCorePolicyGate
  cannotAutoPayInstitutionalCompetence
  cannotAutoPayCompensability
  : ExternalityDutyBridgeRole

externalityRoleForDutyIssue : Climate.DutyIssue → ExternalityDutyBridgeRole
externalityRoleForDutyIssue Climate.reasonableForeseeability = mayInformForeseeability
externalityRoleForDutyIssue Climate.knowledge = mayInformKnowledge
externalityRoleForDutyIssue Climate.control = mayInformControl
externalityRoleForDutyIssue Climate.vulnerability = mayInformVulnerability
externalityRoleForDutyIssue Climate.harmTypeDeterminacy = mayInformHarmCharacterisation
externalityRoleForDutyIssue Climate.causation = cannotAutoPayCausation
externalityRoleForDutyIssue Climate.coreGovernmentPolicy = cannotAutoPayCorePolicyGate
externalityRoleForDutyIssue Climate.institutionalCompetence = cannotAutoPayInstitutionalCompetence
externalityRoleForDutyIssue Climate.compensability = cannotAutoPayCompensability
externalityRoleForDutyIssue _ = mayInformHarmCharacterisation

foreseeabilityRemainsFactualFeature :
  Negligence.classifyDutyIssue Climate.reasonableForeseeability
  ≡ Negligence.factualDutyFeature
foreseeabilityRemainsFactualFeature = refl

vulnerabilityRemainsRelationalFeature :
  Negligence.classifyDutyIssue Climate.vulnerability
  ≡ Negligence.relationalDutyFeature
vulnerabilityRemainsRelationalFeature = refl

corePolicyRemainsInstitutionalConstraint :
  Negligence.classifyDutyIssue Climate.coreGovernmentPolicy
  ≡ Negligence.institutionalDutyConstraint
corePolicyRemainsInstitutionalConstraint = refl

causationRemainsDownstreamElement :
  Negligence.classifyDutyIssue Climate.causation
  ≡ Negligence.downstreamNegligenceElement
causationRemainsDownstreamElement = refl

pabaiRecognisedHarmDoesNotAutomaticallyCreateDuty :
  Climate.PhysicalInjuryAutomaticallyCreatesDuty → ⊥
pabaiRecognisedHarmDoesNotAutomaticallyCreateDuty =
  Climate.physicalInjuryDoesNotAutomaticallyCreateDuty

climateScienceDoesNotAutomaticallyCreatePrivateDuty :
  Climate.ClimateScienceFindingAutomaticallyCreatesDuty → ⊥
climateScienceDoesNotAutomaticallyCreatePrivateDuty =
  Climate.scienceDoesNotAutomaticallyCreatePrivateDuty

------------------------------------------------------------------------
-- Terminal validation / material justice analogy boundary.
------------------------------------------------------------------------

record TerminalPayerRemedyAnalogyBoundary : Set where
  constructor terminal-payer-remedy-analogy-boundary
  field
    surroundingSuccessSignalsCanCoexistWithTerminalFailure : Bool
    surroundingSuccessSignalsCanCoexistWithTerminalFailureIsTrue :
      surroundingSuccessSignalsCanCoexistWithTerminalFailure ≡ true
    economicExternalPayerEqualsAffectedCommunity : Bool
    economicExternalPayerEqualsAffectedCommunityIsFalse :
      economicExternalPayerEqualsAffectedCommunity ≡ false
    economicRevenueEqualsMaterialJustice : Bool
    economicRevenueEqualsMaterialJusticeIsFalse : economicRevenueEqualsMaterialJustice ≡ false
    sharedTopologyTransfersNormativeAuthority : Bool
    sharedTopologyTransfersNormativeAuthorityIsFalse :
      sharedTopologyTransfersNormativeAuthority ≡ false
    realisedConsumerMustBeCheckedDirectly : Bool
    realisedConsumerMustBeCheckedDirectlyIsTrue :
      realisedConsumerMustBeCheckedDirectly ≡ true

open TerminalPayerRemedyAnalogyBoundary public

canonicalTerminalPayerRemedyAnalogyBoundary : TerminalPayerRemedyAnalogyBoundary
canonicalTerminalPayerRemedyAnalogyBoundary = terminal-payer-remedy-analogy-boundary
  true refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- No-collapse / source-attribution laws.
------------------------------------------------------------------------

data TerminalPayerTheoryIsHumanRightsDoctrine : Set where
data BillyCommitteeOwnsTerminalPayerAnalogy : Set where
data PabaiOwnsLESExternalityHyperfabric : Set where
data KimmererOwnsDutyOfCareDoctrine : Set where
data CarbonPricePaysCountryAuthority : Set where

terminalPayerDoesNotBecomeHumanRightsDoctrine : TerminalPayerTheoryIsHumanRightsDoctrine → ⊥
terminalPayerDoesNotBecomeHumanRightsDoctrine ()

committeeDoesNotOwnOurEconomicAnalogy : BillyCommitteeOwnsTerminalPayerAnalogy → ⊥
committeeDoesNotOwnOurEconomicAnalogy ()

pabaiDoesNotOwnOurLESConstruction : PabaiOwnsLESExternalityHyperfabric → ⊥
pabaiDoesNotOwnOurLESConstruction ()

kimmererDoesNotOwnNegligenceDoctrine : KimmererOwnsDutyOfCareDoctrine → ⊥
kimmererDoesNotOwnNegligenceDoctrine ()

carbonPriceDoesNotPayCountryAuthority : CarbonPricePaysCountryAuthority → ⊥
carbonPriceDoesNotPayCountryAuthority ()
