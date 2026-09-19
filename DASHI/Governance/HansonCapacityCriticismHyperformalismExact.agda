module DASHI.Governance.HansonCapacityCriticismHyperformalismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryFactorisationSufficiency as QFS
import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Admissible
import DASHI.Interop.SourceAttributionShapePolicyExact as SourceShape
import DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact as HealthWrongType
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as WrongType
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma
import DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge as Hyperfabric
import DASHI.ComputerScience.SuicidePreventionTraumaMemoryLearningHyperfabricExact as TML

------------------------------------------------------------------------
-- HANSON / CAPACITY / CRITICISM HYPERFORMALISM
--
-- DASHI-original formal reconstruction of:
--
--   Patrick Marlborough,
--   "Is it ableist to criticise Pauline Hanson?",
--   The Yeah Nah Review, 18 September 2026.
--   https://yeahnah.substack.com/p/is-it-ableist-to-criticise-pauline
--
-- SOURCE BOUNDARY
--
-- Marlborough owns the essay, its first-person disability-support-worker
-- anecdote, its satire, and its interpretive claims.  This module does not
-- silently convert those claims into medical, psychological, electoral, or
-- causal facts about Pauline Hanson, One Nation, the former client, or any
-- other person.
--
-- Political-history and current-affairs facts are separately attributed below.
-- DASHI owns the typed reconstruction, non-factorability witnesses, WrongType
-- firewalls, hyperfabric decomposition and consumer-indexed theorems.
--
-- Central law:
--
--   public conduct evidence
--     != person-level clinical attribution
--     != capacity attribution
--     != response calibration
--
-- while:
--
--   evidenced functional limitation + situated context
--     may alter an admissible response
--
-- without creating:
--
--   moral immunity
--   political immunity
--   institutional epistemic exemption
--   diagnosis from rhetoric
------------------------------------------------------------------------

------------------------------------------------------------------------
-- CARRIER-SENSITIVE SOURCE PROVENANCE
------------------------------------------------------------------------

data PublicSourceRole : Set where
  interpretiveSatire : PublicSourceRole
  firstPersonAnecdote : PublicSourceRole
  electoralHistory : PublicSourceRole
  electoralResult : PublicSourceRole
  parliamentaryConduct : PublicSourceRole
  investigativeJournalism : PublicSourceRole
  relationshipAndDonationReporting : PublicSourceRole
  policyPositionReporting : PublicSourceRole

record AttributedPublicSource : Set where
  constructor attributed-public-source
  field
    authorOrInstitution : String
    title : String
    publicationDate : String
    canonicalLocator : String
    role : PublicSourceRole
    boundedClaim : String
    importsClinicalAuthority : Bool
    importsClinicalAuthorityIsFalse : importsClinicalAuthority ≡ false

open AttributedPublicSource public

marlboroughEssay : AttributedPublicSource
marlboroughEssay = attributed-public-source
  "Patrick Marlborough"
  "Is it ableist to criticise Pauline Hanson?"
  "2026-09-18"
  "https://yeahnah.substack.com/p/is-it-ableist-to-criticise-pauline"
  interpretiveSatire
  "source for the essay's support-work anecdote, satire, framing, quotations and interpretive political claims; not clinical authority"
  false refl

abcHansonHistory : AttributedPublicSource
abcHansonHistory = attributed-public-source
  "ABC News"
  "The rises and falls of Pauline Hanson"
  "2011-04-12; updated 2014-11-19"
  "https://www.abc.net.au/news/2011-04-12/the-rises-and-falls-of-pauline-hanson/2618106"
  electoralHistory
  "Ipswich council origin; 1996 Oxley disendorsement/election; 1997 One Nation formation; 1998 defeat; later unsuccessful candidacies"
  false refl

abcBurqa2017 : AttributedPublicSource
abcBurqa2017 = attributed-public-source
  "ABC News"
  "Pauline Hanson wears burka to Question Time in the Senate, slammed by George Brandis"
  "2017-08-18"
  "https://www.abc.net.au/news/2017-08-18/pauline-hanson-wears-burka-to-question-time-in-the-senate/8816886"
  parliamentaryConduct
  "documents the 2017 Senate burqa stunt and Hanson's stated rationale; criticism remains attributed to named speakers"
  false refl

abcBurqa2025 : AttributedPublicSource
abcBurqa2025 = attributed-public-source
  "ABC News"
  "Senate shut down for 1.5 hours after Pauline Hanson's burka stunt"
  "2025-11-24"
  "https://www.abc.net.au/news/2025-11-24/senate-suspended-after-pauline-hansons-burka-stunt/106047124"
  parliamentaryConduct
  "documents Hanson's repeated burqa stunt, refusal to leave, Senate suspension and chamber sanction"
  false refl

abcNRAInvestigation : AttributedPublicSource
abcNRAInvestigation = attributed-public-source
  "ABC News / Al Jazeera Investigative Unit reporting"
  "Hidden cameras and fake websites: Inside the investigation into One Nation's bid for NRA donations"
  "2019-03-27"
  "https://www.abc.net.au/news/2019-03-27/inside-the-investigation-into-one-nations-bid-for-nra-donations/10939256"
  investigativeJournalism
  "documents James Ashby and Steve Dickson seeking meetings and discussing potential NRA funding; does not establish that Hanson authorised the trip or that a donation was received"
  false refl

guardianRinehartRelationship : AttributedPublicSource
guardianRinehartRelationship = attributed-public-source
  "Guardian Australia"
  "Has Gina Rinehart 'bought' One Nation? Pauline Hanson has the billionaire's backing - and she's super happy"
  "2026-04-30; updated 2026-08-17"
  "https://www.theguardian.com/australia-news/ng-interactive/2026/apr/30/gina-rinehart-one-nation-pauline-hanson-donations-ntwnfb"
  relationshipAndDonationReporting
  "reports Rinehart-linked travel, donor activity, Mar-a-Lago access and donations/aircraft support around One Nation; relationship does not by itself prove policy capture"
  false refl

abcRinehartItaly : AttributedPublicSource
abcRinehartItaly = attributed-public-source
  "ABC News"
  "Pauline Hanson reveals Gina Rinehart paid for Italy flights and Dolce & Gabbana show"
  "2026-07-28"
  "https://www.abc.net.au/news/2026-07-28/hanson-reveals-rinehart-paid-for-italy-trip/106968518"
  relationshipAndDonationReporting
  "records Hanson's declaration that Rinehart paid London-Sicily travel and fashion-show access"
  false refl

guardianGasReversal : AttributedPublicSource
guardianGasReversal = attributed-public-source
  "Guardian Australia"
  "One Nation under fire for abandoning gas reservation plan in favour of policy benefiting Gina Rinehart"
  "2026-09-14"
  "https://www.theguardian.com/australia-news/2026/sep/14/one-nation-pauline-hanson-abandoning-gas-reservation-plan-gina-rinehart-relationship-ntwnfb"
  policyPositionReporting
  "reports a 2026 One Nation reversal from supporting to opposing domestic gas reservation after industry consultation; critics' donor-influence claims remain attributed"
  false refl

abcSecretHarbour : AttributedPublicSource
abcSecretHarbour = attributed-public-source
  "ABC News"
  "One Nation secures victory in Secret Harbour by-election, taking first WA lower house seat"
  "2026-08-30"
  "https://www.abc.net.au/news/2026-08-30/one-nation-claims-win-secret-harbour-by-election/107094074"
  electoralResult
  "documents One Nation's first Western Australian lower-house seat, won by Luke Herdegen in the Secret Harbour by-election"
  false refl

abcIpswichContext : AttributedPublicSource
abcIpswichContext = attributed-public-source
  "ABC Elections"
  "Ipswich - QLD Electorate, Candidates, Results"
  "2020 election guide"
  "https://www.abc.net.au/news/elections/qld/2020/guide/ipsw"
  electoralHistory
  "documents Ipswich's long Labor history and One Nation's major 1998 intervention in Hanson's former federal-seat geography"
  false refl

aecGroomContext : AttributedPublicSource
aecGroomContext = attributed-public-source
  "Australian Electoral Commission"
  "Profile of the electoral division of Groom (Qld)"
  "2020-10-09"
  "https://www.aec.gov.au/profiles/qld/groom.htm"
  electoralHistory
  "institutional geographic/demographic carrier for Groom/Toowoomba; does not infer voter ideology from place"
  false refl

canonicalPublicSources : List AttributedPublicSource
canonicalPublicSources =
  marlboroughEssay
  ∷ abcHansonHistory
  ∷ abcBurqa2017
  ∷ abcBurqa2025
  ∷ abcNRAInvestigation
  ∷ guardianRinehartRelationship
  ∷ abcRinehartItaly
  ∷ guardianGasReversal
  ∷ abcSecretHarbour
  ∷ abcIpswichContext
  ∷ aecGroomContext
  ∷ []

sourceShapeForEssay :
  SourceShape.RequiredAttributionShape
sourceShapeForEssay =
  SourceShape.requiredAttributionShape SourceShape.interpretiveOrCulturalSource

------------------------------------------------------------------------
-- CLAIM ROLES: OBSERVATION / INTERPRETATION / CLINICAL ATTRIBUTION
------------------------------------------------------------------------

data ClaimRole : Set where
  observedPublicConduct : ClaimRole
  reportedInstitutionalAct : ClaimRole
  reportedRelationship : ClaimRole
  reportedElectoralOutcome : ClaimRole
  attributedInterpretation : ClaimRole
  functionalCapacityClaim : ClaimRole
  disabilityClaim : ClaimRole
  clinicalDiagnosisClaim : ClaimRole

data EvidenceCarrier : Set where
  articleText : EvidenceCarrier
  parliamentaryRecord : EvidenceCarrier
  electoralRecord : EvidenceCarrier
  publicInterview : EvidenceCarrier
  investigativeRecording : EvidenceCarrier
  declaredInterestRecord : EvidenceCarrier
  longitudinalSupportContext : EvidenceCarrier
  personLevelClinicalEvidence : EvidenceCarrier

record ClaimPayment : Set where
  constructor claim-payment
  field
    claimRole : ClaimRole
    carrier : EvidenceCarrier
    sourceReference : String
    scopeReference : String

open ClaimPayment public

------------------------------------------------------------------------
-- WRONGTYPE FIREWALLS
------------------------------------------------------------------------

data PublicPerformanceAutomaticallyDiagnoses : Set where
data InarticulacyAutomaticallyImpliesDisability : Set where
data OffensiveConductAutomaticallyImpliesImpairment : Set where
data DisabilityAutomaticallyExplainsRacism : Set where
data DisabilityAutomaticallyExcusesConduct : Set where
data CriticismAutomaticallyAbleist : Set where
data AccommodationAutomaticallyExemptsPublicScrutiny : Set where
data DonorRelationshipAutomaticallyProvesPolicyCapture : Set where
data GeographicContextAutomaticallyDeterminesVoterIdeology : Set where
data PolicyReversalAutomaticallyProvesCorruption : Set where
data SatireAutomaticallyBecomesEmpiricalFact : Set where
data PublicPopularityAutomaticallyProvesPolicyTruth : Set where

publicPerformanceDoesNotDiagnose :
  PublicPerformanceAutomaticallyDiagnoses → ⊥
publicPerformanceDoesNotDiagnose ()

inarticulacyDoesNotDiagnose :
  InarticulacyAutomaticallyImpliesDisability → ⊥
inarticulacyDoesNotDiagnose ()

offensiveConductDoesNotDiagnose :
  OffensiveConductAutomaticallyImpliesImpairment → ⊥
offensiveConductDoesNotDiagnose ()

disabilityDoesNotExplainRacismByType :
  DisabilityAutomaticallyExplainsRacism → ⊥
disabilityDoesNotExplainRacismByType ()

disabilityDoesNotAutoExcuse :
  DisabilityAutomaticallyExcusesConduct → ⊥
disabilityDoesNotAutoExcuse ()

criticismDoesNotAutoBecomeAbleist :
  CriticismAutomaticallyAbleist → ⊥
criticismDoesNotAutoBecomeAbleist ()

accommodationDoesNotExemptPublicClaims :
  AccommodationAutomaticallyExemptsPublicScrutiny → ⊥
accommodationDoesNotExemptPublicScrutiny ()

relationshipDoesNotAutoProveCapture :
  DonorRelationshipAutomaticallyProvesPolicyCapture → ⊥
relationshipDoesNotAutoProveCapture ()

placeDoesNotDetermineVoter :
  GeographicContextAutomaticallyDeterminesVoterIdeology → ⊥
placeDoesNotDetermineVoter ()

reversalDoesNotAutoProveCorruption :
  PolicyReversalAutomaticallyProvesCorruption → ⊥
reversalDoesNotAutoProveCorruption ()

satireDoesNotAutoBecomeFact :
  SatireAutomaticallyBecomesEmpiricalFact → ⊥
satireDoesNotAutoBecomeEmpiricalFact ()

popularityDoesNotProveTruth :
  PublicPopularityAutomaticallyProvesPolicyTruth → ⊥
popularityDoesNotProveTruth ()

------------------------------------------------------------------------
-- TWO-CONSUMER FACTORISATION WITNESS
--
-- The same public-performance surface can arise in two states that differ on
-- person-level clinical status.  Hence clinical attribution cannot factor
-- through public performance alone.
------------------------------------------------------------------------

data PublicFigureWorld : Set where
  samePerformanceNoClinicalReceipt : PublicFigureWorld
  samePerformanceClinicalReceipt : PublicFigureWorld

data PublicPerformanceSurface : Set where
  sameObservedPerformance : PublicPerformanceSurface

publicPerformanceObserver : PublicFigureWorld → PublicPerformanceSurface
publicPerformanceObserver samePerformanceNoClinicalReceipt = sameObservedPerformance
publicPerformanceObserver samePerformanceClinicalReceipt = sameObservedPerformance

data ClinicalReceiptStatus : Set where
  clinicalReceiptAbsent : ClinicalReceiptStatus
  clinicalReceiptPresent : ClinicalReceiptStatus

clinicalReceiptConsumer : PublicFigureWorld → ClinicalReceiptStatus
clinicalReceiptConsumer samePerformanceNoClinicalReceipt = clinicalReceiptAbsent
clinicalReceiptConsumer samePerformanceClinicalReceipt = clinicalReceiptPresent

clinicalReceiptDiffers :
  clinicalReceiptConsumer samePerformanceNoClinicalReceipt ≡
  clinicalReceiptConsumer samePerformanceClinicalReceipt → ⊥
clinicalReceiptDiffers ()

publicPerformanceClinicalNonFactorability :
  INF.NonFactorabilityWitness publicPerformanceObserver clinicalReceiptConsumer
publicPerformanceClinicalNonFactorability =
  INF.nonFactorabilityWitness
    samePerformanceNoClinicalReceipt
    samePerformanceClinicalReceipt
    refl
    clinicalReceiptDiffers

publicPerformanceCannotDetermineClinicalReceipt :
  INF.FactorsThrough publicPerformanceObserver clinicalReceiptConsumer → ⊥
publicPerformanceCannotDetermineClinicalReceipt =
  INF.witnessRulesOutEveryFlatFactorisation
    publicPerformanceClinicalNonFactorability

------------------------------------------------------------------------
-- PUBLIC CONDUCT, BY CONTRAST, CAN BE A PUBLIC-EVIDENCE CONSUMER.
------------------------------------------------------------------------

data ConductWorld : Set where
  recordedConductState : ConductWorld

data ConductSurface : Set where
  recordedConductSurface : ConductSurface

data ConductAnswer : Set where
  conductRecorded : ConductAnswer

conductProjection : ConductWorld → ConductSurface
conductProjection recordedConductState = recordedConductSurface

conductQuestions : QFS.InquiryQuestionFamily ConductWorld ⊤
conductQuestions = QFS.inquiryQuestionFamily
  (λ _ → ConductAnswer)
  (λ _ _ → conductRecorded)

conductFactorsThrough :
  QFS.FactorsThrough conductQuestions conductProjection tt
conductFactorsThrough = QFS.factorsThrough
  (λ _ → conductRecorded)
  (λ _ → refl)

------------------------------------------------------------------------
-- CAPACITY-SENSITIVE RESPONSE DOES NOT COLLAPSE RESPONSE MODES
------------------------------------------------------------------------

data ResponseMode : Set where
  criticism : ResponseMode
  correction : ResponseMode
  accommodation : ResponseMode
  environmentalRepair : ResponseMode
  safeguarding : ResponseMode
  sanction : ResponseMode
  institutionalScrutiny : ResponseMode

record CapacitySensitiveResponse : Set₁ where
  constructor capacity-sensitive-response
  field
    conductEvidence : Set
    capacityEvidence : Set
    functionalLinkEvidence : Set
    contextEvidence : Set
    mode : ResponseMode
    preservesAgency : Set
    preservesThirdPartySafety : Set
    doesNotManufactureDiagnosis : Set

open CapacitySensitiveResponse public

------------------------------------------------------------------------
-- SUPPORT-WORK ANECDOTE: LONGITUDINAL LEARNING / MEMORY FIXTURE
--
-- This is attributed to Marlborough's first-person account.  It is not a
-- diagnosis compiler and does not assert that every person with acquired brain
-- injury exhibits this pattern.
------------------------------------------------------------------------

data RetentionState : Set where
  revisionAccessible : RetentionState
  revisionUnavailable : RetentionState

data LearnedValueState : Set where
  antiRacistRevisionPresent : LearnedValueState
  antiRacistRevisionNotEstablished : LearnedValueState

record SupportWorkLearningLoop : Set where
  constructor support-work-learning-loop
  field
    source : AttributedPublicSource
    reportedHeadInjury : Bool
    reportedShortTermMemoryDifficulty : Bool
    repeatedCorrectionReported : Bool
    laterSelfCorrectionReported : Bool
    weekToWeekRetentionVariable : Bool
    clinicalMechanismInferredByDASHI : Bool
    clinicalMechanismInferredByDASHIIsFalse :
      clinicalMechanismInferredByDASHI ≡ false
    generalisedToAllBrainInjury : Bool
    generalisedToAllBrainInjuryIsFalse :
      generalisedToAllBrainInjury ≡ false

open SupportWorkLearningLoop public

marlboroughSupportWorkLoop : SupportWorkLearningLoop
marlboroughSupportWorkLoop =
  support-work-learning-loop
    marlboroughEssay
    true
    true
    true
    true
    true
    false refl
    false refl

------------------------------------------------------------------------
-- MEMORY / LEARNING / TRAUMA NON-COLLAPSE
--
-- Repo-native owners already distinguish remembered event, valuation,
-- salience, confidence, phase and action weight; learning receipts preserve
-- histories rather than equating a current action with the whole memory fibre.
-- This bridge preserves those distinctions for the essay's anecdotal model.
------------------------------------------------------------------------

data SameUtteranceState : Set where
  sameUtteranceRevisionAccessible : SameUtteranceState
  sameUtteranceRevisionUnavailable : SameUtteranceState

data UtteranceOnlySurface : Set where
  sameUtterance : UtteranceOnlySurface

utteranceObserver : SameUtteranceState → UtteranceOnlySurface
utteranceObserver sameUtteranceRevisionAccessible = sameUtterance
utteranceObserver sameUtteranceRevisionUnavailable = sameUtterance

revisionAccessibility : SameUtteranceState → RetentionState
revisionAccessibility sameUtteranceRevisionAccessible = revisionAccessible
revisionAccessibility sameUtteranceRevisionUnavailable = revisionUnavailable

revisionAccessibilityDiffers :
  revisionAccessibility sameUtteranceRevisionAccessible ≡
  revisionAccessibility sameUtteranceRevisionUnavailable → ⊥
revisionAccessibilityDiffers ()

utteranceDoesNotDetermineMemoryAccessibility :
  INF.FactorsThrough utteranceObserver revisionAccessibility → ⊥
utteranceDoesNotDetermineMemoryAccessibility =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameUtteranceRevisionAccessible
      sameUtteranceRevisionUnavailable
      refl
      revisionAccessibilityDiffers)

------------------------------------------------------------------------
-- POLITICAL HYPERFABRIC
--
-- No single axis is sovereign.  Race rhetoric, disability attribution,
-- institutional power, media treatment, donor/elite network, regional history,
-- policy chronology, electoral popularity and source provenance remain
-- independently addressable.
------------------------------------------------------------------------

data HansonAxis : Set where
  publicConductAxis : HansonAxis
  raceAndColonialityAxis : HansonAxis
  disabilityAttributionAxis : HansonAxis
  institutionalPowerAxis : HansonAxis
  mediaInterrogationAxis : HansonAxis
  donorEliteNetworkAxis : HansonAxis
  policyConsistencyAxis : HansonAxis
  regionalPoliticalHistoryAxis : HansonAxis
  electoralTrajectoryAxis : HansonAxis
  temporalPopularityAxis : HansonAxis
  sourceProvenanceAxis : HansonAxis

canonicalHansonAxes : List HansonAxis
canonicalHansonAxes =
  publicConductAxis
  ∷ raceAndColonialityAxis
  ∷ disabilityAttributionAxis
  ∷ institutionalPowerAxis
  ∷ mediaInterrogationAxis
  ∷ donorEliteNetworkAxis
  ∷ policyConsistencyAxis
  ∷ regionalPoliticalHistoryAxis
  ∷ electoralTrajectoryAxis
  ∷ temporalPopularityAxis
  ∷ sourceProvenanceAxis
  ∷ []

data PoliticalPeriod : Set where
  ipswichCouncil1994 : PoliticalPeriod
  oxleyBreakthrough1996 : PoliticalPeriod
  oneNationQueenslandPeak1998 : PoliticalPeriod
  parliamentaryAbsence1998to2016 : PoliticalPeriod
  senateReturn2016 : PoliticalPeriod
  renewedExpansion2025to2026 : PoliticalPeriod

data RegionalContext : Set where
  ipswichOxleyOrigin : RegionalContext
  lockyerBlairPeriphery : RegionalContext
  toowoombaGroomDarlingDowns : RegionalContext
  secretHarbourWesternAustralia : RegionalContext

record PoliticalTrajectoryFixture : Set where
  constructor political-trajectory-fixture
  field
    originSource : AttributedPublicSource
    ipswichOriginRecorded : Bool
    oxleyBreakthroughRecorded : Bool
    qld1998OneNationPeakRecorded : Bool
    laterPoliticalMarginalisationRecorded : Bool
    senateReturnRecorded : Bool
    waLowerHouseExpansionRecorded : Bool
    currentPopularityIsPolicyTruth : Bool
    currentPopularityIsPolicyTruthIsFalse :
      currentPopularityIsPolicyTruth ≡ false
    geographyDeterminesVoterBelief : Bool
    geographyDeterminesVoterBeliefIsFalse :
      geographyDeterminesVoterBelief ≡ false

open PoliticalTrajectoryFixture public

canonicalPoliticalTrajectory : PoliticalTrajectoryFixture
canonicalPoliticalTrajectory =
  political-trajectory-fixture
    abcHansonHistory
    true true true true true true
    false refl
    false refl

------------------------------------------------------------------------
-- OFFENSIVE / PROVOCATIVE PUBLIC CONDUCT AS EVENT SEQUENCE
--
-- "Offensive" is not silently asserted as a medical or cognitive property.
-- The source records the event; evaluations remain attributed to identified
-- political/community speakers or are represented as an application-supplied
-- norm.
------------------------------------------------------------------------

data PublicConductEvent : Set where
  burqaSenate2017 : PublicConductEvent
  burqaSenate2025 : PublicConductEvent
  indigenousComments2025Reported2026 : PublicConductEvent

record ConductEventReceipt : Set where
  constructor conduct-event-receipt
  field
    event : PublicConductEvent
    source : AttributedPublicSource
    eventOccurred : Bool
    eventOccurredIsTrue : eventOccurred ≡ true
    eventImpliesDiagnosis : Bool
    eventImpliesDiagnosisIsFalse : eventImpliesDiagnosis ≡ false

open ConductEventReceipt public

burqa2017Receipt : ConductEventReceipt
burqa2017Receipt =
  conduct-event-receipt burqaSenate2017 abcBurqa2017 true refl false refl

burqa2025Receipt : ConductEventReceipt
burqa2025Receipt =
  conduct-event-receipt burqaSenate2025 abcBurqa2025 true refl false refl

------------------------------------------------------------------------
-- DECLARED / REALISED / POLICY-REVERSAL SURFACE
------------------------------------------------------------------------

data OneNationPolicyEpisode : Set where
  foreignDonationEpisode2019 : OneNationPolicyEpisode
  gasReservationEpisode2026 : OneNationPolicyEpisode

record PolicyResidualCandidate : Set where
  constructor policy-residual-candidate
  field
    episode : OneNationPolicyEpisode
    declaredPositionReference : String
    laterActionOrPositionReference : String
    evidenceSource : AttributedPublicSource
    residualRequiresInterpretation : Bool
    residualRequiresInterpretationIsTrue :
      residualRequiresInterpretation ≡ true
    provesCorruption : Bool
    provesCorruptionIsFalse : provesCorruption ≡ false
    provesCognitiveDefect : Bool
    provesCognitiveDefectIsFalse : provesCognitiveDefect ≡ false

open PolicyResidualCandidate public

gasReservationResidual : PolicyResidualCandidate
gasReservationResidual =
  policy-residual-candidate
    gasReservationEpisode2026
    "reported prior One Nation support for domestic gas reservation"
    "reported June 2026 shift to opposition after industry consultation"
    guardianGasReversal
    true refl
    false refl
    false refl

nraResidual : PolicyResidualCandidate
nraResidual =
  policy-residual-candidate
    foreignDonationEpisode2019
    "Hanson publicly opposed foreign donations"
    "senior One Nation officials Ashby and Dickson were recorded discussing potential NRA funding; Hanson later said she did not know of or authorise the trip"
    abcNRAInvestigation
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- DONOR / ELITE-NETWORK RELATION: RELATION != CAPTURE
------------------------------------------------------------------------

data EliteRelationKind : Set where
  travelSupport : EliteRelationKind
  hospitality : EliteRelationKind
  donationSupport : EliteRelationKind
  eventAccess : EliteRelationKind
  politicalRelationship : EliteRelationKind

record EliteNetworkRelation : Set where
  constructor elite-network-relation
  field
    actorReference : String
    counterpartyReference : String
    relationKind : EliteRelationKind
    source : AttributedPublicSource
    documented : Bool
    documentedIsTrue : documented ≡ true
    automaticallyProvesPolicyCapture : Bool
    automaticallyProvesPolicyCaptureIsFalse :
      automaticallyProvesPolicyCapture ≡ false

open EliteNetworkRelation public

rinehartItalyRelation : EliteNetworkRelation
rinehartItalyRelation =
  elite-network-relation
    "Pauline Hanson"
    "Gina Rinehart"
    travelSupport
    abcRinehartItaly
    true refl
    false refl

rinehartOneNationRelation : EliteNetworkRelation
rinehartOneNationRelation =
  elite-network-relation
    "One Nation / Pauline Hanson"
    "Gina Rinehart / Hancock-linked network"
    donationSupport
    guardianRinehartRelationship
    true refl
    false refl

trumpAccessRelation : EliteNetworkRelation
trumpAccessRelation =
  elite-network-relation
    "One Nation donor network"
    "Donald Trump / Mar-a-Lago event access"
    eventAccess
    guardianRinehartRelationship
    true refl
    false refl

------------------------------------------------------------------------
-- ELECTORAL TRAJECTORY: HISTORICAL RELEGATION != CURRENT TRAJECTORY
------------------------------------------------------------------------

data TrajectoryStatus : Set where
  breakthrough : TrajectoryStatus
  marginalised : TrajectoryStatus
  returned : TrajectoryStatus
  expanding : TrajectoryStatus

trajectoryStatus : PoliticalPeriod → TrajectoryStatus
trajectoryStatus ipswichCouncil1994 = breakthrough
trajectoryStatus oxleyBreakthrough1996 = breakthrough
trajectoryStatus oneNationQueenslandPeak1998 = breakthrough
trajectoryStatus parliamentaryAbsence1998to2016 = marginalised
trajectoryStatus senateReturn2016 = returned
trajectoryStatus renewedExpansion2025to2026 = expanding

data HistoricalMarginalityImpliesCurrentMarginality : Set where
data CurrentExpansionErasesHistoricalMarginality : Set where

historicalMarginalityDoesNotFixCurrentStatus :
  HistoricalMarginalityImpliesCurrentMarginality → ⊥
historicalMarginalityDoesNotFixCurrentStatus ()

currentExpansionDoesNotEraseHistory :
  CurrentExpansionErasesHistoricalMarginality → ⊥
currentExpansionDoesNotEraseHistory ()

------------------------------------------------------------------------
-- INTERSECTIONAL NON-FACTORABILITY OF SINGLE-AXIS HANSON EXPLANATIONS
------------------------------------------------------------------------

data SameConductDifferentInstitutionalPosition : Set where
  sameConductLowInstitutionalPower : SameConductDifferentInstitutionalPosition
  sameConductHighInstitutionalPower : SameConductDifferentInstitutionalPosition

data ConductLabelSurface : Set where
  sameConductLabel : ConductLabelSurface

conductLabelObserver :
  SameConductDifferentInstitutionalPosition → ConductLabelSurface
conductLabelObserver sameConductLowInstitutionalPower = sameConductLabel
conductLabelObserver sameConductHighInstitutionalPower = sameConductLabel

institutionalScrutinyRequired :
  SameConductDifferentInstitutionalPosition → Bool
institutionalScrutinyRequired sameConductLowInstitutionalPower = false
institutionalScrutinyRequired sameConductHighInstitutionalPower = true

institutionalScrutinyDiffers :
  institutionalScrutinyRequired sameConductLowInstitutionalPower ≡
  institutionalScrutinyRequired sameConductHighInstitutionalPower → ⊥
institutionalScrutinyDiffers ()

conductAloneCannotDetermineInstitutionalResponse :
  INF.FactorsThrough conductLabelObserver institutionalScrutinyRequired → ⊥
conductAloneCannotDetermineInstitutionalResponse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameConductLowInstitutionalPower
      sameConductHighInstitutionalPower
      refl
      institutionalScrutinyDiffers)

------------------------------------------------------------------------
-- MEDIA / PUBLIC-POWER ASYMMETRY
------------------------------------------------------------------------

record PublicPowerResponseBoundary : Set where
  constructor public-power-response-boundary
  field
    disabilityAccommodationMayAlterInterviewForm : Bool
    disabilityAccommodationMayAlterInterviewFormIsTrue :
      disabilityAccommodationMayAlterInterviewForm ≡ true

    accommodationRemovesNeedForPolicyEvidence : Bool
    accommodationRemovesNeedForPolicyEvidenceIsFalse :
      accommodationRemovesNeedForPolicyEvidence ≡ false

    accommodationRemovesFollowUpQuestions : Bool
    accommodationRemovesFollowUpQuestionsIsFalse :
      accommodationRemovesFollowUpQuestions ≡ false

    officeHoldingChangesInstitutionalConsumer : Bool
    officeHoldingChangesInstitutionalConsumerIsTrue :
      officeHoldingChangesInstitutionalConsumer ≡ true

    unsupportedClinicalAttributionIsRequiredForCriticism : Bool
    unsupportedClinicalAttributionIsRequiredForCriticismIsFalse :
      unsupportedClinicalAttributionIsRequiredForCriticism ≡ false

open PublicPowerResponseBoundary public

canonicalPublicPowerResponseBoundary : PublicPowerResponseBoundary
canonicalPublicPowerResponseBoundary =
  public-power-response-boundary
    true refl
    false refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- REUSE RECEIPTS: THIS OWNER IS A THIN CONSUMER, NOT A PARALLEL ONTOLOGY
------------------------------------------------------------------------

sourceShapeBoundary :
  SourceShape.SourceAttributionShapeBoundary
sourceShapeBoundary =
  SourceShape.canonicalSourceAttributionShapeBoundary

healthEvidenceWrongTypeBoundary :
  HealthWrongType.TemporalHealthEvidenceBoundary
healthEvidenceWrongTypeBoundary =
  HealthWrongType.canonicalTemporalHealthEvidenceBoundary

tmlBoundary :
  TML.TraumaMemoryLearningBoundary
tmlBoundary =
  TML.canonicalTraumaMemoryLearningBoundary

admissibleMDLBoundary :
  Admissible.AdmissibleConsumerMDLBoundary
admissibleMDLBoundary =
  Admissible.canonicalAdmissibleConsumerMDLBoundary

declaredRealizedBoundary :
  Integrity.DeclaredRealizedBoundary
declaredRealizedBoundary =
  Integrity.canonicalDeclaredRealizedBoundary

------------------------------------------------------------------------
-- ENDPOINT
------------------------------------------------------------------------

record HansonCapacityCriticismBoundary : Set where
  constructor hanson-capacity-criticism-boundary
  field
    marlboroughEssayIsAttributed : Bool
    supportWorkAnecdoteRemainsAnecdotal : Bool
    satireRemainsInterpretiveSource : Bool
    publicConductMayBeCritiquedWithoutDiagnosis : Bool
    publicPerformanceCannotDetermineDiagnosis : Bool
    disabilityAndRacismRemainDistinctAxes : Bool
    memoryAndCurrentUtteranceRemainDistinctAxes : Bool
    learningAndRetentionRemainDistinctAxes : Bool
    capacitySensitiveResponseMayBeAdmissible : Bool
    capacitySensitivityCreatesMoralImmunity : Bool
    capacitySensitivityCreatesMoralImmunityIsFalse :
      capacitySensitivityCreatesMoralImmunity ≡ false
    accommodationCreatesPoliticalImmunity : Bool
    accommodationCreatesPoliticalImmunityIsFalse :
      accommodationCreatesPoliticalImmunity ≡ false
    donorRelationAutomaticallyProvesCapture : Bool
    donorRelationAutomaticallyProvesCaptureIsFalse :
      donorRelationAutomaticallyProvesCapture ≡ false
    policyResidualAutomaticallyProvesCorruption : Bool
    policyResidualAutomaticallyProvesCorruptionIsFalse :
      policyResidualAutomaticallyProvesCorruption ≡ false
    geographyAutomaticallyDeterminesPoliticalBelief : Bool
    geographyAutomaticallyDeterminesPoliticalBeliefIsFalse :
      geographyAutomaticallyDeterminesPoliticalBelief ≡ false
    historicalMarginalityAndCurrentExpansionBothRetained : Bool
    electoralPopularityCreatesTruthAuthority : Bool
    electoralPopularityCreatesTruthAuthorityIsFalse :
      electoralPopularityCreatesTruthAuthority ≡ false

open HansonCapacityCriticismBoundary public

canonicalHansonCapacityCriticismBoundary :
  HansonCapacityCriticismBoundary
canonicalHansonCapacityCriticismBoundary =
  hanson-capacity-criticism-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    false refl
    true
    false refl
