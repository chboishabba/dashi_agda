module DASHI.Governance.ThielAntichristPoliticalTheology20261101Exact where

------------------------------------------------------------------------
-- THIEL / ANTICHRIST POLITICAL THEOLOGY: AUTHOR- AND EDGE-SCOPED MODEL
--
-- Original assertions belong to Peter Thiel, Sam Wolfe, named interviewers
-- and essay authors, NOT to this Agda module. This module is a DASHI
-- attributed finite epistemic/causal countermodel. No supernatural truth,
-- private motive, coordinated conspiracy or defamatory individual claim
-- is inferred.
--
-- Canonical generic owners reused, not refounded:
-- IbrahimSnowballReligionEschatologyIdeologyIdentityExact (original
-- eschatology narrative/identity/political programme non-collapse);
-- OperationalSystemBehaviourSemanticsExact (Stafford Beer POSIWID);
-- PowerAndGrammar (second-order admission); IntersectionalNonFactorability.
--
-- First-person/author:
-- Thiel, The Education of a Libertarian, Cato Unbound, 2009-04-13.
-- Tyler Cowen interviews Peter Thiel, Political Theology, 2024-04-17
--   https://conversationswithtyler.com/episodes/peter-thiel-political-theology/
-- Peter Thiel and Sam Wolfe, Voyages to the End of the World,
--   First Things 2025-10-01
--   https://firstthings.com/voyages-to-the-end-of-the-world/
-- Peter Thiel and Sam Wolfe, The Pope and the Antichrist,
--   First Things 2026-07-15
--   https://firstthings.com/the-pope-and-the-antichrist/
--
-- Recorded lectures, SECONDARY RECORDING REPORTAGE:
-- Tiku, Dwoskin, De Vynck, Washington Post, 2025-10-10;
-- Guardian, 2025-10-10, explicitly sourced to attendee recording;
-- Rome AP and Reuters, 2026-03-15, observed conferences and disputes.
--
-- Manidis/Roberts, The Commanding Heights (2026-10-29)
--   https://commanding-heights.com/ ; the text uses "antichrist is in
--   the details", Thiel great-stagnation thesis, sovereign firm/state
--   convergence; a shared phrase does not establish common authorship.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Philosophy.PowerAndGrammar as Power
import DASHI.Wikimedia.IbrahimSnowballReligionEschatologyIdeologyIdentityExact as Ibrahim
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Sources

data NamedActor : Set where
  thiel wolfe cowen girard schmitt newman bacon
    manidis roberts palantirInstitution karp cohen vance : NamedActor

data StatementRole : Set where
  authoredText liveInterview recordedLectureJournalist accountOfIdeas
    attributedSourceConcept independentEssay corporateInstitution : StatementRole

record AttributedText : Set where
  constructor attributedText
  field
    authorOrSpeaker : NamedActor
    titleOrLocator : String
    originalCarrier : String
    observationDate : String
    role : StatementRole
    boundedAssertion : String
    forbiddenInference : String

open AttributedText public

cowenThiel2024 : AttributedText
cowenThiel2024 = attributedText thiel
  "Peter Thiel on Political Theology; Conversation with Tyler; sections on millenarianism, katechon and AI"
  "https://conversationswithtyler.com/episodes/peter-thiel-political-theology/"
  "2024-04-17" liveInterview
  "Thiel says one-world totalitarian government may be as existential a risk as AI/climate/nuclear risks; safety fear can produce centralised global compute governance; the katechon (restrainer) risks becoming the Antichrist; AI has strong centralising returns to scale."
  "Thiel explicitly raises AI centralisation as a concern; does not declare all regulation evil or assert particular colleagues share his theology."

firstThings2025 : AttributedText
firstThings2025 = attributedText thiel
  "Voyages to the End of the World; coauthored Sam Wolfe"
  "https://firstthings.com/voyages-to-the-end-of-the-world/"
  "2025-10-01" authoredText
  "Political-theological interpretation of Bacon's New Atlantis, Swift, Watchmen, One Piece; antichrist/science/Christian belief; Daniel 12:4."
  "Authors' exegesis does not establish literal fulfillment of prophecy or private intention of industry participants."

firstThings2026 : AttributedText
firstThings2026 = attributedText thiel
  "The Pope and the Antichrist; coauthored Sam Wolfe"
  "https://firstthings.com/the-pope-and-the-antichrist/"
  "2026-07-15" authoredText
  "Author's first-person account of Rome talks connects nuclear, climate and AI existential risk, theological end-times, and feared totalitarian peace and safety."
  "Thiel's own doctrine is observable; worldwide deployment of his doctrine, papal endorsement and common corporate control are not thereby established."

commandingAuthors2026 : AttributedText
commandingAuthors2026 = attributedText manidis
  "The Commanding Heights; coauthored Joe Roberts, peculiar laboratories, antichrist passage, Thiel great stagnation, Alpha/Omega"
  "https://commanding-heights.com/"
  "2026-10-29" independentEssay
  "Authors forecast sovereign frontier under state influence, identify scarce AI distribution tollbooths, use biblical imagery and the phrase antichrist is in the details."
  "Essay rhetoric and acknowledgement do not establish adoption of Thiel/Wolfe full theology; future sovereign lab is forecast, not a completed transaction."

-- Important role distinctions for intellectual/genealogical paths:
-- coauthorship is not a shared contract; citation is not agreement;
-- documented corporate relationship is not same-command proof.

data ConnectionType : Set where
  namedCoauthor sourceInterviewer citesIntellectualPrecedent
    foundingCorporateConnection laterAuthorRhetoric
    financialElectoralSupport votingTrustMember : ConnectionType

data DocumentedConnection :
  NamedActor → NamedActor → ConnectionType → Set where
  thielWolfeCoauthored :
    DocumentedConnection thiel wolfe namedCoauthor
  cowenThielInterview :
    DocumentedConnection cowen thiel sourceInterviewer
  girardReference :
    DocumentedConnection thiel girard citesIntellectualPrecedent
  schmittReference :
    DocumentedConnection thiel schmitt citesIntellectualPrecedent
  newmanReference :
    DocumentedConnection thiel newman citesIntellectualPrecedent
  baconInterpretation :
    DocumentedConnection thiel bacon citesIntellectualPrecedent
  thielPalantirFounding :
    DocumentedConnection thiel palantirInstitution foundingCorporateConnection
  manidisAndRoberts :
    DocumentedConnection manidis roberts namedCoauthor
  thielKarpFoundersVotingTrust :
    DocumentedConnection thiel karp votingTrustMember
  thielCohenFoundersVotingTrust :
    DocumentedConnection thiel cohen votingTrustMember
  thielVanceCampaignFunding :
    DocumentedConnection thiel vance financialElectoralSupport

data AttributionPath : Set where
  directlyAuthored documentedIntellectualCitation institutionalConnection
    similarRhetoric inferredSharedCommand : AttributionPath

data DirectCoCommandFromSharedRhetoric : Set where
data CommonReligionFromCorporateTie : Set where
data CoauthorshipMeansGovPolicy : Set where

rhetoricCannotProduceDirectCommand :
  DirectCoCommandFromSharedRhetoric → ⊥
rhetoricCannotProduceDirectCommand ()

corporateTieDoesNotDefineReligion :
  CommonReligionFromCorporateTie → ⊥
corporateTieDoesNotDefineReligion ()

coauthorshipDoesNotAutomaticallyCausePolicy :
  CoauthorshipMeansGovPolicy → ⊥
coauthorshipDoesNotAutomaticallyCausePolicy ()

------------------------------------------------------------------------
-- ASSOCIATE INTERFACES: typed financial/administrative ties, not a
-- collective political theology.
------------------------------------------------------------------------

record NamedRelationshipReceipt : Set where
  constructor namedRelationshipReceipt
  field
    leftActor rightActor : NamedActor
    relationship : ConnectionType
    firstPartyOrSecondarySource : String
    boundedEvent : String
    sourceGradeAndCaveat : String

foundersVotingTrust2025 : NamedRelationshipReceipt
foundersVotingTrust2025 = namedRelationshipReceipt
  thiel karp votingTrustMember
  "Palantir Technologies 2025 10-K / SEC: https://www.sec.gov/Archives/edgar/data/1321655/000132165526000011/pltr-20251231.htm"
  "Class F founder voting trust established by Cohen, Karp and Thiel, potentially up to 49.999999pct founder voting power if threshold holds at 2025-12-31."
  "Filed structural corporate governance link; not proof Karp/Cohen accepted Thiel's religious doctrine or directed particular model actions."

vanceHistoricalFunding2022 : NamedRelationshipReceipt
vanceHistoricalFunding2022 = namedRelationshipReceipt
  thiel vance financialElectoralSupport
  "University of Queensland, Luke Munn, 2025-08-01; corroborated FT/WP historical reporting, FEC/OpenSecrets original transaction acquisition still pending"
  "Thiel donated USD15m supporting Vance's 2022 Senate campaign through independent-expenditure political committee; former Mithril employer relationship also reported."
  "The documented financial support is not direct evidence Vance endorses Antichrist doctrine or that any later White House action was purchased."

-- A jointly filed corporate voting structure, an independent political
-- donation, and named theological coauthorship are three different
-- edge types. In particular, their composition is NOT a public-policy or
-- theological adherence proof.
data VotingControlImpliesTheologicalAgreement : Set where
data PoliticalDonationImpliesPolicyInstruction : Set where

founderStatusCannotDictateDoctrine :
  VotingControlImpliesTheologicalAgreement → ⊥
founderStatusCannotDictateDoctrine ()

donationCannotSubstituteForInstruction :
  PoliticalDonationImpliesPolicyInstruction → ⊥
donationCannotSubstituteForInstruction ()

------------------------------------------------------------------------
-- Distinct doctrinal/operational claims: an actor can oppose a universal
-- safety bureaucracy while benefiting from selective national security
-- procurement. It is a real-world test target, not a logical contradiction.
------------------------------------------------------------------------

data GovernanceScope : Set where
  globalUniversalRegulator nationalPublicProcurement
    privateCapitalControl pluralOpenComputation : GovernanceScope

data Position : Set where
  opposesGlobalCentralism backsTechnologyDevelopment
    testsNationalSecurityControl advocatesOpenPlurality : Position

record AssertedGovernancePosition : Set where
  constructor assertedGovernancePosition
  field
    source : AttributedText
    jurisdictionalScope : GovernanceScope
    reading : Position
    interpretationOrDirectQuotation : String

antiGlobalComputeGovernance : AssertedGovernancePosition
antiGlobalComputeGovernance = assertedGovernancePosition
  cowenThiel2024 globalUniversalRegulator opposesGlobalCentralism
  "Directly from 2024 interview: universal coercive safety coordination may itself be existential risk."

technologyOverStagnation : AssertedGovernancePosition
technologyOverStagnation = assertedGovernancePosition
  cowenThiel2024 privateCapitalControl backsTechnologyDevelopment
  "2024 interview supports technological development amid danger; does not alone prescribe a specific lab control architecture."

data KatechonRole : Set where
  temporaryProtection entrenchedRestrainer mimeticControlDrift : KatechonRole

data AntichristFrame : Set where
  centralizedWorldSafetyRationale coerciveOneWorldState
    theologicalEndTimesLiterature : AntichristFrame

-- Thiel explicitly says in his 2024 interview that the restrainer can
-- become indistinguishable from what it is intended to restrain.
-- The transition is a synthetic example of this asserted risk.
data RestraintStage : Set where
  guardsAgainstGlobalMonopoly acquiresUnaccountableControl : RestraintStage

declaredSecurityPurpose : RestraintStage → Bool
declaredSecurityPurpose _ = true

realizedPluralKnowledgeAccess : RestraintStage → Bool
realizedPluralKnowledgeAccess guardsAgainstGlobalMonopoly = true
realizedPluralKnowledgeAccess acquiresUnaccountableControl = false

sameDeclaredRestraint :
  declaredSecurityPurpose guardsAgainstGlobalMonopoly
  ≡ declaredSecurityPurpose acquiresUnaccountableControl
sameDeclaredRestraint = refl

differentActualPlurality :
  realizedPluralKnowledgeAccess guardsAgainstGlobalMonopoly
  ≡ realizedPluralKnowledgeAccess acquiresUnaccountableControl → ⊥
differentActualPlurality ()

restrainerCanBecomeGateCountermodel :
  INF.NonFactorabilityWitness
    declaredSecurityPurpose realizedPluralKnowledgeAccess
restrainerCanBecomeGateCountermodel =
  INF.nonFactorabilityWitness
    guardsAgainstGlobalMonopoly acquiresUnaccountableControl
    sameDeclaredRestraint differentActualPlurality

sameProtectiveClaimDoesNotGuaranteePluralAccess :
  INF.FactorsThrough
    declaredSecurityPurpose realizedPluralKnowledgeAccess → ⊥
sameProtectiveClaimDoesNotGuaranteePluralAccess =
  INF.witnessRulesOutEveryFlatFactorisation
    restrainerCanBecomeGateCountermodel

canonicalPODiagnostic : POSIWID.OperationalDescriptionBoundary
canonicalPODiagnostic =
  POSIWID.canonicalOperationalDescriptionBoundary

canonicalIbrahimSnowball :
  Ibrahim.ReligionEschatologyIdeologySnowballBoundary
canonicalIbrahimSnowball =
  Ibrahim.canonicalReligionEschatologyIdeologySnowballBoundary

thielPrimarySource : Sources.SourceReceipt
thielPrimarySource = Sources.thielWolfeOriginal

thielEarlierOriginal : Sources.SourceReceipt
thielEarlierOriginal = Sources.thielOriginal2009

-- Impact verification must be a chain with separately attributed stages,
-- not a generalized statement that all named people share an ideology.
record PolicyTransmissionPayment : Set where
  constructor policyTransmissionPayment
  field
    originalAuthoredAssertion : String
    boundedRecipientOrAudience : String
    identifiedDraftPolicyClause : String
    datedAdoptionOrImplementation : String
    observedIndependentAccessEffect : String
    sameObjectCausalTest : String

ideologyBoundarySummary : String
ideologyBoundarySummary =
  "Thiel's specific doctrine is source-authored and his contradictory institutional roles are an empirical research question. His 2024 warning says a katechon can become the Antichrist; reuse POSIWID/INF proves that identical stated protection can coexist with opposite realised plural-access outcome in a finite model. Girard, Schmitt, Newman, Wolfe, Cowen, Thiel, Palantir, Manidis and Roberts remain role-scoped, not a single collective author."
