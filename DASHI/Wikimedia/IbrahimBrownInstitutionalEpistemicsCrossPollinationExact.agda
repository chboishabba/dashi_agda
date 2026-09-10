module DASHI.Wikimedia.IbrahimBrownInstitutionalEpistemicsCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as John
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Alice
import DASHI.Biology.AliceBrownDissentGovernanceCrossPollinationExact as AliceDissent
import DASHI.Biology.BrownKimberGovernanceProfileBridge as BrownKimber
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Core.EpistemicInquiryGovernance as Governance
import DASHI.Wikimedia.IbrahimCountryCommunityKnowledgeAuthorityBridgeExact as Funnel

------------------------------------------------------------------------
-- JOHN / ALICE BROWN -> INSTITUTIONAL EPISTEMICS CROSS-POLLINATION
--
-- This owner does not merge the two source families. It extracts a shared
-- institutional-epistemic carrier while retaining attribution and claim role:
--
--   John Anthony Brown: formation, authority asymmetry, threat, belonging,
--   exit, institutional power, colonial comparison and contestability are
--   research/hypothesis/normative/legal obligations in a working manuscript.
--
--   Alice Brown (+ coauthors): student voice, parent allyship, observer
--   plurality, barriers, contestability and coordinate-wise epistemic agency
--   are source-bounded education/institutional participation results.
--
-- The useful cross-pollination is bidirectional:
--
--   authority -> formation/constraint
--   subject/community -> contestation/revision of authority
--
-- Neither source family empirically proves the other.
------------------------------------------------------------------------

data InstitutionalEpistemicCoordinate : Set where
  subjectFormation : InstitutionalEpistemicCoordinate
  participation : InstitutionalEpistemicCoordinate
  voice : InstitutionalEpistemicCoordinate
  observerPlurality : InstitutionalEpistemicCoordinate
  authorityAsymmetry : InstitutionalEpistemicCoordinate
  belongingDependence : InstitutionalEpistemicCoordinate
  refusalExit : InstitutionalEpistemicCoordinate
  contestability : InstitutionalEpistemicCoordinate
  evidenceReturn : InstitutionalEpistemicCoordinate
  institutionalRevision : InstitutionalEpistemicCoordinate
  historicalPower : InstitutionalEpistemicCoordinate
  communityAuthority : InstitutionalEpistemicCoordinate

record BrownCrossSurface : Set where
  constructor brown-cross-surface
  field
    coordinate : InstitutionalEpistemicCoordinate
    johnSurface : String
    aliceSurface : String
    sharedReading : String
    johnSourceBoundaryRetained : Bool
    aliceSourceBoundaryRetained : Bool
    empiricalEquivalenceClaimed : Bool
open BrownCrossSurface public

formationVoiceSurface : BrownCrossSurface
formationVoiceSurface = brown-cross-surface
  subjectFormation
  "ChildReligiousFormationCoordinates: dependence, belonging, authority asymmetry, sanction, counter-evidence, refusal and exit"
  "StudentVoiceEpistemicAgencyBridge / InstitutionalAgencySurface: contest/refuse/evidence-return coordinates"
  "formation conditions and later/current voice must be separately represented; observed participation or profession cannot reconstruct autonomous endorsement"
  true true false

authorityAgencySurface : BrownCrossSurface
authorityAgencySurface = brown-cross-surface
  authorityAsymmetry
  "family/congregational/institutional/church/state/colonial authority scales; institutional-power research obligations"
  "BrownKimber coordinate-wise epistemic authority profile; feedback, question, projection, relevance, carrier, consumer, residual and revision roles remain distinct"
  "institutional power over a subject is not identical to epistemic authority for the subject; agency must be assigned coordinate-wise"
  true true false

belongingExitSurface : BrownCrossSurface
belongingExitSurface = brown-cross-surface
  belongingDependence
  "family-belonging / practical-exit restrictions and conditional formation hypotheses"
  "formal option presented != effective accessibility; participation and accessibility are distinct"
  "nominal membership or option availability cannot pay a real exit/choice/agency claim when social or institutional dependence constrains the option cone"
  true true false

contestabilitySurface : BrownCrossSurface
contestabilitySurface = brown-cross-surface
  contestability
  "transparency/accountability and survivor-access-to-justice research questions; dissent may be harder to recognise under institutional hegemony"
  "feedback/consultation != epistemic agency; admitted voice != meta-rule power; effective contestability requires more than participation"
  "a legitimate institutional knowledge loop requires subjects to contest framing, interpretation, downstream use and revision pathways"
  true true false

historyCommunitySurface : BrownCrossSurface
historyCommunitySurface = brown-cross-surface
  historicalPower
  "colonial cultural dispossession is retained as a research question requiring historical-source receipts and non-identity of histories"
  "observer/community fibres remain situated and cannot be replaced by institutional records or scalar participation"
  "historical/institutional power must preserve affected-community and observer provenance; comparison does not create identical histories"
  true true false

------------------------------------------------------------------------
-- Two-way institutional loop.
------------------------------------------------------------------------

data InstitutionalDirection : Set where
  authorityToFormation : InstitutionalDirection
  subjectToAuthority : InstitutionalDirection
  communityToInstitution : InstitutionalDirection
  institutionToCommunity : InstitutionalDirection

record InstitutionalEpistemicEdge : Set where
  constructor institutional-epistemic-edge
  field
    direction : InstitutionalDirection
    reading : String
    requiredCoordinates : String
    sourceBounded : Bool
    automaticPromotionForbidden : Bool
open InstitutionalEpistemicEdge public

authorityFormationEdge : InstitutionalEpistemicEdge
authorityFormationEdge = institutional-epistemic-edge
  authorityToFormation
  "institutional/family/religious authority may shape formation conditions, but mechanism, outcome, coercion and legal classification remain separate promotion gates"
  "authority scale; developmental capacity; belonging; sanction; counter-evidence; refusal; exit; empirical outcome"
  true true

subjectAuthorityEdge : InstitutionalEpistemicEdge
subjectAuthorityEdge = institutional-epistemic-edge
  subjectToAuthority
  "subject voice may contest question, coding/projection, relevance, carrier, consumer, residual and revision coordinates; mere feedback carries no constitutive authority"
  "voice stage; contestability; refusal; evidence return; coordinate-wise authority"
  true true

communityInstitutionEdge : InstitutionalEpistemicEdge
communityInstitutionEdge = institutional-epistemic-edge
  communityToInstitution
  "situated subject/parent/community evidence may inform and contest institutional knowledge, but no one observer fibre silently becomes the whole-system view"
  "observer identity; community scope; provenance; authority role; method"
  true true

institutionCommunityEdge : InstitutionalEpistemicEdge
institutionCommunityEdge = institutional-epistemic-edge
  institutionToCommunity
  "institutional classifications, teaching, policy or records act on communities/subjects without manufacturing assent, identity, legitimacy or complete knowledge"
  "institutional power; communication/action surface; affected subject/community; interpretation; downstream effects"
  true true

------------------------------------------------------------------------
-- Cross-pollination with the Ibrahim parent seam.
------------------------------------------------------------------------

record BrownFunnelWeld : Set where
  constructor brown-funnel-weld
  field
    communityCoordinateUsed : Bool
    knowledgeCoordinateUsed : Bool
    authorityCoordinateUsed : Bool
    societyStateBoundaryUsed : Bool
    participationIsNotAuthority : Bool
    institutionalRecordIsNotWholeSystem : Bool
    observedConformityIsNotAutonomousEndorsement : Bool
    stateOrInstitutionalRecognitionCreatesCommunityAuthority : Bool
    johnAndAliceEmpiricalClaimsMerged : Bool
open BrownFunnelWeld public

canonicalBrownFunnelWeld : BrownFunnelWeld
canonicalBrownFunnelWeld = brown-funnel-weld
  true true true true true true true false false

countryCommunityAuthorityBridge : Funnel.CountryCommunityKnowledgeAuthorityBridgeReceipt
countryCommunityAuthorityBridge =
  Funnel.canonicalCountryCommunityKnowledgeAuthorityBridgeReceipt

------------------------------------------------------------------------
-- Direct reuse of existing source-bound firewalls.
------------------------------------------------------------------------

johnPaperKeepsConditionalOutcomes :
  John.JohnAnthonyBrownPaperBidiBoundary.paperPositiveAndNegativeOutcomeHypothesesPreserved
    John.canonicalJohnAnthonyBrownPaperBidiBoundary ≡ true
johnPaperKeepsConditionalOutcomes = refl

aliceFormalAvailabilityStillNotAgency :
  Alice.AliceInstitutionalChoiceBoundary.formalAvailabilityEqualsAgency
    Alice.canonicalAliceInstitutionalChoiceBoundary ≡ false
aliceFormalAvailabilityStillNotAgency = refl

aliceInstitutionRecordStillNotWholeSystem :
  Alice.AliceInstitutionalChoiceBoundary.institutionalRecordEqualsWholeSystem
    Alice.canonicalAliceInstitutionalChoiceBoundary ≡ false
aliceInstitutionRecordStillNotWholeSystem = refl

aliceFeedbackStillNotEpistemicAgency :
  AliceDissent.AliceBrownDissentGovernanceBoundary.feedbackSurfaceEqualsEpistemicAgency
    AliceDissent.canonicalAliceBrownDissentGovernanceBoundary ≡ false
aliceFeedbackStillNotEpistemicAgency = refl

feedbackHasNoConstitutiveAuthority :
  (coordinate : Governance.InquiryCoordinate) →
  Governance.authorityLevel
    BrownKimber.brownKimberAuthorityProfile
    Voice.feedbackSourceStage
    coordinate
  ≡ Governance.noAuthority
feedbackHasNoConstitutiveAuthority = BrownKimber.feedbackAuthorityLevelIsZero

------------------------------------------------------------------------
-- Firewalls learned from the combined tranche.
------------------------------------------------------------------------

data AuthorityAsymmetryCreatesCoercionVerdict : Set where
data ParticipationCreatesAgency : Set where
data InstitutionCreatesCommunityAuthority : Set where
data ParentVoiceEqualsSubjectVoice : Set where
data AffectedSubjectVoiceSettlesJustice : Set where
data CrossFamilyAnalogyCreatesEmpiricalEvidence : Set where
data HistoricalComparisonCreatesHistoricalIdentity : Set where

authorityAsymmetryDoesNotByItselfCreateCoercionVerdict : AuthorityAsymmetryCreatesCoercionVerdict → ⊥
authorityAsymmetryDoesNotByItselfCreateCoercionVerdict ()

participationDoesNotCreateAgency : ParticipationCreatesAgency → ⊥
participationDoesNotCreateAgency ()

institutionDoesNotCreateCommunityAuthority : InstitutionCreatesCommunityAuthority → ⊥
institutionDoesNotCreateCommunityAuthority ()

parentVoiceDoesNotReplaceSubjectVoice : ParentVoiceEqualsSubjectVoice → ⊥
parentVoiceDoesNotReplaceSubjectVoice ()

affectedVoiceDoesNotAutomaticallySettleJustice : AffectedSubjectVoiceSettlesJustice → ⊥
affectedVoiceDoesNotAutomaticallySettleJustice ()

crossFamilyAnalogyDoesNotCreateEvidence : CrossFamilyAnalogyCreatesEmpiricalEvidence → ⊥
crossFamilyAnalogyDoesNotCreateEvidence ()

historicalComparisonDoesNotCreateIdentity : HistoricalComparisonCreatesHistoricalIdentity → ⊥
historicalComparisonDoesNotCreateIdentity ()

record BrownInstitutionalEpistemicsBoundary : Set where
  constructor brown-institutional-epistemics-boundary
  field
    authorityFormationDirectionRetained : Bool
    voiceRevisionDirectionRetained : Bool
    observerFibresRemainPlural : Bool
    accessParticipationAgencySeparated : Bool
    mechanismOutcomeLegalPromotionSeparated : Bool
    communityAuthorityNonDescentRetained : Bool
    historicalComparisonNonIdentityRetained : Bool
    sourceFamiliesRemainIndependent : Bool
    crossPollinationCreatesUniversalInstitutionTheory : Bool

canonicalBrownInstitutionalEpistemicsBoundary : BrownInstitutionalEpistemicsBoundary
canonicalBrownInstitutionalEpistemicsBoundary =
  brown-institutional-epistemics-boundary
    true true true true true true true true false
