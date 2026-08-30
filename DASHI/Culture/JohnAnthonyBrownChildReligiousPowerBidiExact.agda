module DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: CHILD RELIGIOUS POWER / AUTONOMY BIDI
--
-- Primary manuscript source:
--   Author: John Anthony Brown
--   Document label: Johns-Research-Paper_3_tracked changes.docx
--   Status: working / tracked-changes research manuscript; no DOI asserted.
--
-- The manuscript studies religious indoctrination specifically in the
-- Catholic context through children's autonomy, self-determination, human
-- rights, developmental vulnerability, family dynamics, psychological
-- well-being, institutional power, hell/damnation, cultural hegemony,
-- colonisation/cultural dispossession, transparency and accountability.
--
-- This owner is deliberately BIDI.
--
--   paper -> formalism:
--     each manuscript proposition is decomposed into a typed research
--     obligation rather than being promoted as a repository theorem.
--
--   formalism -> paper:
--     repository boundaries are returned as revision / evidence obligations;
--     they do not erase the manuscript's normative research programme.
--
-- In particular, the manuscript itself contains conditional hypotheses:
-- religious formation may have positive OR negative outcomes depending on
-- beliefs/practices, family dynamics and social context; moderate involvement
-- may be protective while extreme indoctrination may be associated with
-- distress.  The formalisation therefore must not rewrite John Anthony Brown's
-- paper as the universal claim "religion harms children".
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.ReligiousPowerChildFearClaimBidiExact as ClaimAudit

------------------------------------------------------------------------
-- Exact manuscript attribution and bounded source role.
------------------------------------------------------------------------

record BrownPaperSource : Set where
  constructor brown-paper-source
  field
    author : String
    documentLabel : String
    sourceStatus : String
    doiOrIdentifier : String
    boundedRole : String

open BrownPaperSource public

johnAnthonyBrownPaper : BrownPaperSource
johnAnthonyBrownPaper = brown-paper-source
  "John Anthony Brown"
  "Johns-Research-Paper_3_tracked changes.docx"
  "working tracked-changes interdisciplinary research manuscript"
  "no DOI asserted"
  "primary source for the author's research questions, hypotheses, normative concerns and proposed comparisons; not independent empirical verification of its bibliography or conclusions"

johnAnthonyBrownIsAttributedAuthor :
  BrownPaperSource.author johnAnthonyBrownPaper ≡ "John Anthony Brown"
johnAnthonyBrownIsAttributedAuthor = refl

------------------------------------------------------------------------
-- What the paper is actually trying to study.
------------------------------------------------------------------------

data BrownPaperAxis : Set where
  childAutonomy : BrownPaperAxis
  childSelfDetermination : BrownPaperAxis
  childHumanRights : BrownPaperAxis
  developmentalVulnerability : BrownPaperAxis
  familyDynamics : BrownPaperAxis
  hellDamnationThreat : BrownPaperAxis
  religiousAuthority : BrownPaperAxis
  institutionalPower : BrownPaperAxis
  culturalHegemony : BrownPaperAxis
  indigenousCulturalDispossession : BrownPaperAxis
  psychologicalWellbeing : BrownPaperAxis
  transparencyAccountability : BrownPaperAxis
  survivorAccessToJustice : BrownPaperAxis
  legalClassification : BrownPaperAxis

data ManuscriptStatus : Set where
  researchQuestion : ManuscriptStatus
  proposedMechanism : ManuscriptStatus
  empiricalHypothesis : ManuscriptStatus
  normativeArgument : ManuscriptStatus
  legalQuestion : ManuscriptStatus
  revisionNeeded : ManuscriptStatus

record BrownPaperClaim : Set where
  constructor brown-paper-claim
  field
    axis : BrownPaperAxis
    status : ManuscriptStatus
    paperWordingRole : String
    source : BrownPaperSource

open BrownPaperClaim public

earlyGodSatanFormationClaim : BrownPaperClaim
earlyGodSatanFormationClaim = brown-paper-claim
  developmentalVulnerability empiricalHypothesis
  "introduction of Catholic concepts including God and Satan before substantial reason/consent may affect autonomy and self-determination"
  johnAnthonyBrownPaper

hellDamnationFearClaim : BrownPaperClaim
hellDamnationFearClaim = brown-paper-claim
  hellDamnationThreat proposedMechanism
  "threat of hell / eternal punishment may be psychologically salient to young children and participate in guilt, anxiety, fear or low self-worth"
  johnAnthonyBrownPaper

familyAuthorityClaim : BrownPaperClaim
familyAuthorityClaim = brown-paper-claim
  familyDynamics empiricalHypothesis
  "religious authority can interact with family relationships, disagreement, communication, belonging and emotional support"
  johnAnthonyBrownPaper

institutionalHegemonyClaim : BrownPaperClaim
institutionalHegemonyClaim = brown-paper-claim
  institutionalPower normativeArgument
  "long-standing institutional and cultural power can normalise religious authority and make harms or dissent harder to recognise and contest"
  johnAnthonyBrownPaper

colonialDispossessionClaim : BrownPaperClaim
colonialDispossessionClaim = brown-paper-claim
  indigenousCulturalDispossession researchQuestion
  "the manuscript compares religious hegemony with colonial cultural dispossession and suppression of Indigenous beliefs/practices"
  johnAnthonyBrownPaper

melbourneResponseClaim : BrownPaperClaim
melbourneResponseClaim = brown-paper-claim
  survivorAccessToJustice researchQuestion
  "the manuscript questions transparency, confidentiality, conflicts of interest, accountability and access to external justice in institutional response systems such as the Melbourne Response"
  johnAnthonyBrownPaper

------------------------------------------------------------------------
-- Preserve the paper's own conditional / non-universal hypotheses.
------------------------------------------------------------------------

data OutcomeDirection : Set where
  potentiallyProtective : OutcomeDirection
  potentiallyHarmful : OutcomeDirection
  mixedOrContextDependent : OutcomeDirection
  unresolvedOutcome : OutcomeDirection

record ConditionalReligiousFormationHypothesis : Set where
  constructor conditional-religious-formation-hypothesis
  field
    direction : OutcomeDirection
    beliefsAndPracticesMatter : Bool
    familyDynamicsMatter : Bool
    socialContextMatters : Bool
    exposureIntensityMatters : Bool

hypothesis4ContextDependence : ConditionalReligiousFormationHypothesis
hypothesis4ContextDependence =
  conditional-religious-formation-hypothesis
    mixedOrContextDependent true true true true

hypothesis6ModerateProtectivePossibility : ConditionalReligiousFormationHypothesis
hypothesis6ModerateProtectivePossibility =
  conditional-religious-formation-hypothesis
    potentiallyProtective true true true true

hypothesis6ExtremeDistressPossibility : ConditionalReligiousFormationHypothesis
hypothesis6ExtremeDistressPossibility =
  conditional-religious-formation-hypothesis
    potentiallyHarmful true true true true

data BrownPaperPromotesUniversalReligiousHarm : Set where

paperDoesNotPromoteUniversalReligiousHarm :
  BrownPaperPromotesUniversalReligiousHarm → ⊥
paperDoesNotPromoteUniversalReligiousHarm ()

------------------------------------------------------------------------
-- Dependency / authority / formation coordinates.
--
-- These are research coordinates, not an automatic coercion classifier.
------------------------------------------------------------------------

record ChildReligiousFormationCoordinates : Set where
  constructor child-religious-formation-coordinates
  field
    developmentalDependence : Bool
    familyBelongingDependence : Bool
    authorityAsymmetry : Bool
    divineSanctionRepresented : Bool
    counterEvidenceRestricted : Bool
    doubtOrRefusalPenalised : Bool
    practicalExitRestricted : Bool
    alternativesAvailable : Bool

open ChildReligiousFormationCoordinates public

record EntrapmentCandidateWitness
    (c : ChildReligiousFormationCoordinates) : Set where
  constructor entrapment-candidate-witness
  field
    dependencePresent : developmentalDependence c ≡ true
    belongingDependencePresent : familyBelongingDependence c ≡ true
    authorityAsymmetryPresent : authorityAsymmetry c ≡ true
    sanctionPresent : divineSanctionRepresented c ≡ true
    counterEvidenceRestrictionPresent : counterEvidenceRestricted c ≡ true
    refusalPenaltyPresent : doubtOrRefusalPenalised c ≡ true
    exitRestrictionPresent : practicalExitRestricted c ≡ true

open EntrapmentCandidateWitness public

data ReligiousTeachingPromotesEntrapment : Set where

data EarlyFormationPromotesCoercion : Set where

data FearPromotesUniqueFormationRoute : Set where

religiousTeachingDoesNotPromoteEntrapment :
  ReligiousTeachingPromotesEntrapment → ⊥
religiousTeachingDoesNotPromoteEntrapment ()

earlyFormationDoesNotPromoteCoercion : EarlyFormationPromotesCoercion → ⊥
earlyFormationDoesNotPromoteCoercion ()

fearDoesNotPromoteUniqueFormationRoute : FearPromotesUniqueFormationRoute → ⊥
fearDoesNotPromoteUniqueFormationRoute ()

existingReverseNonfactorability :
  ClaimAudit.INF.FactorsThrough
    ClaimAudit.behaviourSurface
    ClaimAudit.formationRoute → ⊥
existingReverseNonfactorability = ClaimAudit.behaviourCannotRecoverFormationRoute

------------------------------------------------------------------------
-- Paper -> formal obligation direction.
------------------------------------------------------------------------

data FormalObligation : Set where
  developmentalCapacityReceipt : FormalObligation
  fearMechanismReceipt : FormalObligation
  familyBelongingExitReceipt : FormalObligation
  institutionalPowerReceipt : FormalObligation
  colonialHistoryReceipt : FormalObligation
  transparencyContestabilityReceipt : FormalObligation
  empiricalOutcomeReceipt : FormalObligation
  normativePromotionReceipt : FormalObligation
  jurisdictionSpecificLegalReceipt : FormalObligation

paperToPrimaryObligation : BrownPaperClaim → FormalObligation
paperToPrimaryObligation earlyGodSatanFormationClaim = developmentalCapacityReceipt
paperToPrimaryObligation hellDamnationFearClaim = fearMechanismReceipt
paperToPrimaryObligation familyAuthorityClaim = familyBelongingExitReceipt
paperToPrimaryObligation institutionalHegemonyClaim = institutionalPowerReceipt
paperToPrimaryObligation colonialDispossessionClaim = colonialHistoryReceipt
paperToPrimaryObligation melbourneResponseClaim = transparencyContestabilityReceipt

------------------------------------------------------------------------
-- Formalism -> paper direction.
--
-- The reverse pass says how a proposition should return to the manuscript:
-- preserve, qualify, split, source-check, or withhold legal promotion.
------------------------------------------------------------------------

data PaperRevisionAction : Set where
  preserveAsResearchQuestion : PaperRevisionAction
  preserveAsConditionalHypothesis : PaperRevisionAction
  splitMechanismFromOutcome : PaperRevisionAction
  addPopulationScope : PaperRevisionAction
  addDevelopmentalCapacityScope : PaperRevisionAction
  addHistoricalSourceReceipt : PaperRevisionAction
  addIndependentInstitutionalReceipt : PaperRevisionAction
  separateNormativeFromEmpirical : PaperRevisionAction
  withholdLegalLabelPendingElements : PaperRevisionAction
  replaceHardAgeSwitchWithCapacitySensitiveLanguage : PaperRevisionAction

formalToPaperRevision : FormalObligation → PaperRevisionAction
formalToPaperRevision developmentalCapacityReceipt =
  replaceHardAgeSwitchWithCapacitySensitiveLanguage
formalToPaperRevision fearMechanismReceipt = splitMechanismFromOutcome
formalToPaperRevision familyBelongingExitReceipt = addPopulationScope
formalToPaperRevision institutionalPowerReceipt = addIndependentInstitutionalReceipt
formalToPaperRevision colonialHistoryReceipt = addHistoricalSourceReceipt
formalToPaperRevision transparencyContestabilityReceipt = addIndependentInstitutionalReceipt
formalToPaperRevision empiricalOutcomeReceipt = preserveAsConditionalHypothesis
formalToPaperRevision normativePromotionReceipt = separateNormativeFromEmpirical
formalToPaperRevision jurisdictionSpecificLegalReceipt = withholdLegalLabelPendingElements

record BrownPaperBidiRoute (claim : BrownPaperClaim) : Set where
  constructor brown-paper-bidi-route
  field
    forwardObligation : FormalObligation
    forwardMatchesClaim : forwardObligation ≡ paperToPrimaryObligation claim
    backwardRevision : PaperRevisionAction
    backwardMatchesObligation :
      backwardRevision ≡ formalToPaperRevision forwardObligation

open BrownPaperBidiRoute public

hellBidiRoute : BrownPaperBidiRoute hellDamnationFearClaim
hellBidiRoute =
  brown-paper-bidi-route
    fearMechanismReceipt refl splitMechanismFromOutcome refl

colonialBidiRoute : BrownPaperBidiRoute colonialDispossessionClaim
colonialBidiRoute =
  brown-paper-bidi-route
    colonialHistoryReceipt refl addHistoricalSourceReceipt refl

melbourneResponseBidiRoute : BrownPaperBidiRoute melbourneResponseClaim
melbourneResponseBidiRoute =
  brown-paper-bidi-route
    transparencyContestabilityReceipt refl
    addIndependentInstitutionalReceipt refl

------------------------------------------------------------------------
-- Legal-label separation required by the manuscript's own ambitious legal
-- comparison programme.
------------------------------------------------------------------------

data BrownLegalLabel : Set where
  socialPsychologicalEntrapment : BrownLegalLabel
  falseImprisonment : BrownLegalLabel
  battery : BrownLegalLabel
  fraud : BrownLegalLabel
  modernSlavery : BrownLegalLabel
  taxEvasion : BrownLegalLabel
  deception : BrownLegalLabel

socialEntrapmentNotModernSlavery :
  socialPsychologicalEntrapment ≡ modernSlavery → ⊥
socialEntrapmentNotModernSlavery ()

socialEntrapmentNotFalseImprisonment :
  socialPsychologicalEntrapment ≡ falseImprisonment → ⊥
socialEntrapmentNotFalseImprisonment ()

record LegalPromotionReceipt (label : BrownLegalLabel) : Set where
  constructor legal-promotion-receipt
  field
    jurisdiction : String
    currentAuthority : String
    elementsSpecified : Bool
    elementsSpecifiedIsTrue : elementsSpecified ≡ true
    factsMappedToElements : Bool
    factsMappedToElementsIsTrue : factsMappedToElements ≡ true
    provenance : String

open LegalPromotionReceipt public

data MechanismResemblancePromotesLegalElements : Set where
\data PsychologicalCoercionPromotesModernSlavery : Set where

mechanismResemblanceDoesNotPromoteLegalElements :
  MechanismResemblancePromotesLegalElements → ⊥
mechanismResemblanceDoesNotPromoteLegalElements ()

psychologicalCoercionDoesNotPromoteModernSlavery :
  PsychologicalCoercionPromotesModernSlavery → ⊥
psychologicalCoercionDoesNotPromoteModernSlavery ()

------------------------------------------------------------------------
-- Rights / age wording boundary.
--
-- John Anthony Brown's draft uses "age of reason and consent" as part of the
-- developmental concern.  BIDI returns that as a capacity-sensitive research
-- variable rather than silently installing a universal age threshold.
------------------------------------------------------------------------

data HardAgeThresholdPromotesAutonomyCapacity : Set where

data ParentGuidancePromotesOwnershipOfBelief : Set where

data Under18PromotesNoReligiousExposure : Set where

hardAgeDoesNotPromoteCapacity : HardAgeThresholdPromotesAutonomyCapacity → ⊥
hardAgeDoesNotPromoteCapacity ()

parentGuidanceDoesNotPromoteOwnershipOfBelief :
  ParentGuidancePromotesOwnershipOfBelief → ⊥
parentGuidanceDoesNotPromoteOwnershipOfBelief ()

under18DoesNotPromoteNoReligiousExposure : Under18PromotesNoReligiousExposure → ⊥
under18DoesNotPromoteNoReligiousExposure ()

------------------------------------------------------------------------
-- Institutional scale: family, church, school/care/service and state are not
-- one actor.  This keeps the manuscript's hegemony question researchable
-- without collapsing every institution into a single command structure.
------------------------------------------------------------------------

data AuthorityScale : Set where
  familyScale : AuthorityScale
  congregationalScale : AuthorityScale
  schoolOrCareInstitutionScale : AuthorityScale
  churchGovernanceScale : AuthorityScale
  statePolicyScale : AuthorityScale
  colonialMissionScale : AuthorityScale

data SharedInstitutionalPowerPromotesSingleActor : Set where

data ColonialComparisonPromotesIdenticalHistory : Set where

sharedPowerDoesNotPromoteSingleActor : SharedInstitutionalPowerPromotesSingleActor → ⊥
sharedPowerDoesNotPromoteSingleActor ()

colonialComparisonDoesNotPromoteIdenticalHistory :
  ColonialComparisonPromotesIdenticalHistory → ⊥
colonialComparisonDoesNotPromoteIdenticalHistory ()

------------------------------------------------------------------------
-- BIDI settlement: match John Anthony Brown's programme while keeping both
-- evidence discipline and the manuscript's critical/normative direction.
------------------------------------------------------------------------

record JohnAnthonyBrownPaperBidiBoundary : Set where
  constructor john-anthony-brown-paper-bidi-boundary
  field
    authorExplicitlyAttributed : Bool
    paperTreatedAsEvidenceAuthorityForItsOwnEmpiricalConclusions : Bool
    paperPositiveAndNegativeOutcomeHypothesesPreserved : Bool
    ordinaryReligiousTeachingEqualsEntrapment : Bool
    hellFearMechanismMayBeResearchable : Bool
    observedConformityRecoversUniqueFormationRoute : Bool
    mechanismResemblanceEqualsLegalElementsSatisfied : Bool
    hardAgeThresholdInstalled : Bool
    familyChurchInstitutionStateCollapsedToOneActor : Bool
    colonialComparisonEqualsIdenticalHistory : Bool
    formalAuditErasesNormativeResearchProgramme : Bool
    paperMayReceiveRevisionObligationsFromFormalAudit : Bool

canonicalJohnAnthonyBrownPaperBidiBoundary :
  JohnAnthonyBrownPaperBidiBoundary
canonicalJohnAnthonyBrownPaperBidiBoundary =
  john-anthony-brown-paper-bidi-boundary
    true false true false true false false false false false false true
