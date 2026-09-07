module DASHI.Cognition.PNF.SensibLawTerraNulliusBillyTwoEyedOperationalJusticeExact where

------------------------------------------------------------------------
-- TERRA NULLIUS -> BILLY REMEDY -> TWO-EYED OPERATIONAL JUSTICE
--
-- Cross-pollination only.  The historical Mabo/terra-nullius propositions,
-- Billy HRC Views/state-response propositions, Two-Eyed Seeing sources and
-- POSIWID formalisation remain separately attributed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusJuridicalHumanityOperationalEquivalenceExact as Humanity
import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Personhood
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawBillySituatedKnowledgeRemedyAdequacyExact as Situated
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- 1. Means of remedy != odds of realised remedy.
------------------------------------------------------------------------

data RemedyCompulsionMode : Set where
  selfExecutingDomesticCommand
  directDomesticImplementationCapacity
  indirectTreatyBodyPressure
  communityNegotiatedImplementation
  separateDomesticLitigation
  : RemedyCompulsionMode

data RealisationControl : Set where
  highDirectControl
  politicallyContingentControl
  indirectExternalPressure
  separateJurisdictionalRoute
  : RealisationControl

controlFor : RemedyCompulsionMode → RealisationControl
controlFor selfExecutingDomesticCommand = highDirectControl
controlFor directDomesticImplementationCapacity = politicallyContingentControl
controlFor indirectTreatyBodyPressure = indirectExternalPressure
controlFor communityNegotiatedImplementation = politicallyContingentControl
controlFor separateDomesticLitigation = separateJurisdictionalRoute

record BillyRemedyMeansOddsBoundary : Set where
  constructor billy-remedy-means-odds-boundary
  field
    directExecutiveMeansExist : Bool
    directExecutiveMeansExistIsTrue : directExecutiveMeansExist ≡ true
    parliamentaryMeansExist : Bool
    parliamentaryMeansExistIsTrue : parliamentaryMeansExist ≡ true
    treatyFollowUpExists : Bool
    treatyFollowUpExistsIsTrue : treatyFollowUpExists ≡ true
    directTreatyBodyExecutionWritExistsByDefault : Bool
    directTreatyBodyExecutionWritExistsByDefaultIsFalse :
      directTreatyBodyExecutionWritExistsByDefault ≡ false
    mechanismAvailabilityDeterminesRealisationProbability : Bool
    mechanismAvailabilityDeterminesRealisationProbabilityIsFalse :
      mechanismAvailabilityDeterminesRealisationProbability ≡ false
    numericProbabilitySupportedByCurrentPublicReceipts : Bool
    numericProbabilitySupportedByCurrentPublicReceiptsIsFalse :
      numericProbabilitySupportedByCurrentPublicReceipts ≡ false
    reading : String

open BillyRemedyMeansOddsBoundary public

canonicalBillyRemedyMeansOddsBoundary : BillyRemedyMeansOddsBoundary
canonicalBillyRemedyMeansOddsBoundary = billy-remedy-means-odds-boundary
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  "The HRC Views specify remedy obligations and Australia has domestic political/administrative means to implement them, but the treaty-body View is not a self-executing Australian writ. Available implementation channels therefore do not identify a numeric probability of full reparation."

compensationHasDirectImplementationChannel :
  Remedy.directDomesticExecution Remedy.executiveCompensationChannel ≡ true
compensationHasDirectImplementationChannel = refl

committeeViewStillDoesNotSelfExecute :
  Billy.mechanismStrength Billy.directTreatyBodyDomesticExecutionWrit
  ≡ Billy.unavailableByDefault
committeeViewStillDoesNotSelfExecute = refl

currentPublicFullReparationStillOpen :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
currentPublicFullReparationStillOpen = refl

compensationPublicReceiptStillNotRecovered :
  Billy.publicImplementationState Billy.adequateCompensation
  ≡ Billy.publicReceiptNotRecovered
compensationPublicReceiptStillNotRecovered = refl

------------------------------------------------------------------------
-- 2. Operational state: activity is not realised full reparation.
------------------------------------------------------------------------

data PublicBillyOperationalState : Set where
  noImplementationMapped
  partialImplementationMapped
  realisedFullReparationMapped
  : PublicBillyOperationalState

currentPublicBillyOperationalState : PublicBillyOperationalState
currentPublicBillyOperationalState = partialImplementationMapped

record PublicBillyOperationalReading : Set where
  constructor public-billy-operational-reading
  field
    state : PublicBillyOperationalState
    consultationActivityMapped : Bool
    protectiveAdaptationActivityMapped : Bool
    monitoringActivityMapped : Bool
    fullReparationClosed : Bool
    fullReparationClosedIsFalse : fullReparationClosed ≡ false
    publicCompensationExecutionReceiptRecovered : Bool
    publicCompensationExecutionReceiptRecoveredIsFalse :
      publicCompensationExecutionReceiptRecovered ≡ false
    noPublicReceiptMeansNoPaymentEver : Bool
    noPublicReceiptMeansNoPaymentEverIsFalse : noPublicReceiptMeansNoPaymentEver ≡ false
    reading : String

open PublicBillyOperationalReading public

canonicalPublicBillyOperationalReading : PublicBillyOperationalReading
canonicalPublicBillyOperationalReading = public-billy-operational-reading
  partialImplementationMapped
  true true true
  false refl
  false refl
  false refl
  "On the current public atlas, consultation/adaptation/monitoring activity is mapped while full reparation remains open and no public compensation execution receipt has been recovered. This classifies the public operational state as partial implementation, without inferring that compensation was never privately paid."

------------------------------------------------------------------------
-- 3. Two-Eyed Seeing: hearing content is not preserving authority.
------------------------------------------------------------------------

consultationRecordDoesNotRecoverAuthority :
  INF.FactorsThrough Situated.consultationSurface Situated.authorityParticipation → ⊥
consultationRecordDoesNotRecoverAuthority =
  Situated.consultationRecordCannotRecoverAuthorityParticipation

consultationRecordDoesNotRecoverReciprocity :
  INF.FactorsThrough Situated.consultationSurface Situated.reciprocalImplementation → ⊥
consultationRecordDoesNotRecoverReciprocity =
  Situated.consultationRecordCannotRecoverReciprocalImplementation

------------------------------------------------------------------------
-- 4. Structural cross-pollination: foundational erasure and remedial extraction
-- share a possible authority-erasure operator without becoming one history.
------------------------------------------------------------------------

data AuthorityErasureSite : Set where
  foundationalAcquisitionSite
  remedialConsultationSite
  : AuthorityErasureSite

data AuthorityRelationState : Set where
  authorityConstitutive
  authorityObservedButNonconstitutive
  authorityErasedFromDecision
  : AuthorityRelationState

record AuthorityErasurePattern : Set where
  constructor authority-erasure-pattern
  field
    site : AuthorityErasureSite
    communityPhysicallyOrDiscursivelyPresent : Bool
    communityContentObserved : Bool
    communityAuthorityConstitutive : Bool
    state : AuthorityRelationState
    historicalIdentityWithOtherSiteClaimed : Bool
    historicalIdentityWithOtherSiteClaimedIsFalse :
      historicalIdentityWithOtherSiteClaimed ≡ false
    patternReading : String

open AuthorityErasurePattern public

terraNulliusFoundationalErasure : AuthorityErasurePattern
terraNulliusFoundationalErasure = authority-erasure-pattern
  foundationalAcquisitionSite
  true true false
  authorityErasedFromDecision
  false refl
  "Foundational land/sovereignty machinery could acknowledge physical inhabitants while refusing their law, polity, occupancy and proprietorship constitutive force against Crown acquisition."

extractiveConsultationPattern : AuthorityErasurePattern
extractiveConsultationPattern = authority-erasure-pattern
  remedialConsultationSite
  true true false
  authorityObservedButNonconstitutive
  false refl
  "Conditional remedial pattern: a consultation may record community content while leaving community authority non-constitutive in implementation. This is a structural possibility/witness, not a finding that every Billy consultation actually operated this way."

------------------------------------------------------------------------
-- 5. POSIWID: if authority is erased in operation, a "meaningful consultation"
-- label cannot cure the realised process.
------------------------------------------------------------------------

data ConsultationDeclaredLabel : Set where
  meaningfulConsultationDeclared : ConsultationDeclaredLabel

data ConsultationRealizedAuthority : Set where
  authorityNotCarriedIntoDecision
  authorityCarriedIntoDecision
  : ConsultationRealizedAuthority

data ConsultationSystemState : Set where
  declaredMeaningfulButExtractive
  declaredMeaningfulAndAuthorityBearing
  : ConsultationSystemState

consultationDeclaredLabel : ConsultationSystemState → ConsultationDeclaredLabel
consultationDeclaredLabel _ = meaningfulConsultationDeclared

consultationRealizedAuthority : ConsultationSystemState → ConsultationRealizedAuthority
consultationRealizedAuthority declaredMeaningfulButExtractive = authorityNotCarriedIntoDecision
consultationRealizedAuthority declaredMeaningfulAndAuthorityBearing = authorityCarriedIntoDecision

sameDeclaredConsultationLabel :
  consultationDeclaredLabel declaredMeaningfulButExtractive
  ≡ consultationDeclaredLabel declaredMeaningfulAndAuthorityBearing
sameDeclaredConsultationLabel = refl

authorityOutcomesDiffer :
  consultationRealizedAuthority declaredMeaningfulButExtractive
  ≡ consultationRealizedAuthority declaredMeaningfulAndAuthorityBearing → ⊥
authorityOutcomesDiffer ()

declaredMeaningfulCannotRecoverAuthorityBearingOperation :
  INF.FactorsThrough consultationDeclaredLabel consultationRealizedAuthority → ⊥
declaredMeaningfulCannotRecoverAuthorityBearingOperation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      declaredMeaningfulButExtractive
      declaredMeaningfulAndAuthorityBearing
      refl authorityOutcomesDiffer)

operationalBoundary : POSIWID.OperationalDescriptionBoundary
operationalBoundary = POSIWID.canonicalOperationalDescriptionBoundary

observedOperationMatters :
  POSIWID.observedOperationMayClassifyWhatSystemDoes operationalBoundary ≡ true
observedOperationMatters = refl

declaredPurposeDoesNotOverrideRealisedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect operationalBoundary ≡ false
declaredPurposeDoesNotOverrideRealisedEffect = refl

------------------------------------------------------------------------
-- 6. Deep repair boundary.
------------------------------------------------------------------------

record DecolonialRemedyAdequacyBoundary : Set where
  constructor decolonial-remedy-adequacy-boundary
  field
    rightsRecognitionAloneRepairsFoundationalJuridicalErasure : Bool
    rightsRecognitionAloneRepairsFoundationalJuridicalErasureIsFalse :
      rightsRecognitionAloneRepairsFoundationalJuridicalErasure ≡ false
    consultationCountAloneRepairsAuthorityErasure : Bool
    consultationCountAloneRepairsAuthorityErasureIsFalse :
      consultationCountAloneRepairsAuthorityErasure ≡ false
    communityDefinedSuccessMustMatter : Bool
    communityDefinedSuccessMustMatterIsTrue : communityDefinedSuccessMustMatter ≡ true
    reciprocalCorrectionLoopMustMatter : Bool
    reciprocalCorrectionLoopMustMatterIsTrue : reciprocalCorrectionLoopMustMatter ≡ true
    communityAuthorityMustRemainIndependentCoordinate : Bool
    communityAuthorityMustRemainIndependentCoordinateIsTrue :
      communityAuthorityMustRemainIndependentCoordinate ≡ true
    stateRecognitionCreatesCommunityAuthority : Bool
    stateRecognitionCreatesCommunityAuthorityIsFalse :
      stateRecognitionCreatesCommunityAuthority ≡ false

open DecolonialRemedyAdequacyBoundary public

canonicalDecolonialRemedyAdequacyBoundary : DecolonialRemedyAdequacyBoundary
canonicalDecolonialRemedyAdequacyBoundary = decolonial-remedy-adequacy-boundary
  false refl
  false refl
  true refl
  true refl
  true refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data TerraNulliusEqualsEveryModernConsultation : Set where
data PartialImplementationEqualsFullReparation : Set where
data HRCViewMeansGuaranteedDomesticPayment : Set where
data CommunityContentEqualsCommunityAuthority : Set where

doNotEquateHistoricalSites : TerraNulliusEqualsEveryModernConsultation → ⊥
doNotEquateHistoricalSites ()

partialDoesNotEqualFullReparation : PartialImplementationEqualsFullReparation → ⊥
partialDoesNotEqualFullReparation ()

viewDoesNotGuaranteeDomesticPayment : HRCViewMeansGuaranteedDomesticPayment → ⊥
viewDoesNotGuaranteeDomesticPayment ()

contentDoesNotEqualAuthority : CommunityContentEqualsCommunityAuthority → ⊥
contentDoesNotEqualAuthority ()
