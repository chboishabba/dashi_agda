module DASHI.Cognition.EpsteinBarakPalantirFoundersFundBrokerage20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- EPSTEIN / BARAK / PALANTIR / FOUNDERS FUND BROKERAGE — 2026-10-15
--
-- The released record pays several brokerage stages separated by years and
-- distinct corporate objects.  A proposed Palantir board seat is not an
-- appointment.  A later Barak-Thiel meeting is not proof the board proposal was
-- its subject.  Carbyne -> Founders Fund is a later, separately paid investment
-- introduction path and must not be collapsed into the earlier Palantir pitch.
------------------------------------------------------------------------

data BrokerageStage : Set where
  proposedBoardRoute : BrokerageStage
  proposedIntroduction : BrokerageStage
  acceptedInterestInIntroduction : BrokerageStage
  completedContact : BrokerageStage
  companyFundIntroduction : BrokerageStage
  investorDiligence : BrokerageStage
  completedInvestment : BrokerageStage

record BrokerageReceipt : Set where
  constructor brokerage-receipt
  field
    label : String
    date : String
    source : String
    stage : BrokerageStage
    boundedFinding : String
    paid : Bool
    appointmentOrInvestmentPaid : Bool
open BrokerageReceipt public

barakPalantirBoardProposal2013 : BrokerageReceipt
barakPalantirBoardProposal2013 = brokerage-receipt
  "Epstein proposes Palantir board route to Barak"
  "2013-02"
  "DOJ-released audio EFTA01621008.mov; contemporaneous content independently reported by Wired and other 2026 reporting"
  proposedBoardRoute
  "In a released recorded conversation, Epstein suggested Palantir/Peter Thiel as a possible board route for Ehud Barak while discussing post-government private-sector opportunities. Reporting on the files states the Palantir board appointment did not materialise. The proposal is paid; appointment, Palantir acceptance and compensation are not."
  true false

barakThielOffer20140428 : BrokerageReceipt
barakThielOffer20140428 = brokerage-receipt
  "Epstein offers Barak a Thiel introduction"
  "2014-04-28"
  "EFTA00683942"
  proposedIntroduction
  "Epstein told Barak he had Peter Thiel in New York on May 19 and offered the meeting. Barak replied that Thiel could be very interesting but that he was flying to Europe and said next time. This pays proposed introduction plus Barak interest, not a completed May 19 meeting."
  true false

barakThielLaterContact : BrokerageReceipt
barakThielLaterContact = brokerage-receipt
  "Later Barak-Thiel contact"
  "2014 and later"
  "released schedules/correspondence and 2026 reporting on Barak-Thiel meetings"
  completedContact
  "Later records/reporting establish Barak and Thiel did meet. This pays contact at a later stage but does not identify the 2013 Palantir board proposal as the subject or show a board appointment."
  true false

carbyneFoundersFundIntro2018 : BrokerageReceipt
carbyneFoundersFundIntro2018 = brokerage-receipt
  "Carbyne founder connected to Founders Fund"
  "2018-05-22"
  "EFTA02656963 / related EFTA02656965 thread"
  companyFundIntroduction
  "Released correspondence records Carbyne founder Amir Elichai being introduced to Founders Fund partner Trae Stephens, with Epstein and Barak in the surrounding forwarding chain. The thread says the connection was made through a Peter Thiel route. This pays a company-to-fund introduction, not investment completion by this receipt alone."
  true false

epsteinFlagsCarbyneToThiel2018 : BrokerageReceipt
epsteinFlagsCarbyneToThiel2018 = brokerage-receipt
  "Epstein flags Carbyne/Barak company to Thiel"
  "2018-05-21"
  "EFTA01052344"
  investorDiligence
  "Epstein wrote to Thiel that Trae was meeting Carbyne, described as Ehud Barak's company. This pays Epstein directly flagging the meeting/company to Thiel; it does not prove Thiel directed a later investment or that Epstein caused Founders Fund's decision."
  true false

record BrokerageBoundary : Set where
  constructor brokerage-boundary
  field
    palantirBoardProposalPaid : Bool
    palantirBoardAppointmentPaid : Bool
    barakThielIntroductionOfferPaid : Bool
    laterBarakThielContactPaid : Bool
    carbyneFoundersFundIntroductionPaid : Bool
    epsteinFlaggedCarbyneToThielPaid : Bool
    oneContinuousBrokeragePurposePaid : Bool
    epsteinCausedFoundersFundInvestmentPaid : Bool
    palantirAndCarbyneAreSameCorporateObject : Bool
open BrokerageBoundary public

canonicalBrokerageBoundary : BrokerageBoundary
canonicalBrokerageBoundary = brokerage-boundary
  true false true true true true false false false

data ProposalImpliesAppointment : Set where
data LaterContactImpliesEarlierProposalSubject : Set where
data IntroductionImpliesInvestment : Set where
data BrokerageImpliesInvestmentCausation : Set where

data PalantirProposalImpliesCarbyneContinuity : Set where

proposalDoesNotCreateAppointment : ProposalImpliesAppointment → ⊥
proposalDoesNotCreateAppointment ()

laterContactDoesNotCreateProposalSubject : LaterContactImpliesEarlierProposalSubject → ⊥
laterContactDoesNotCreateProposalSubject ()

introductionDoesNotCreateInvestment : IntroductionImpliesInvestment → ⊥
introductionDoesNotCreateInvestment ()

brokerageDoesNotCreateInvestmentCausation : BrokerageImpliesInvestmentCausation → ⊥
brokerageDoesNotCreateInvestmentCausation ()

palantirProposalDoesNotCreateCarbyneContinuity : PalantirProposalImpliesCarbyneContinuity → ⊥
palantirProposalDoesNotCreateCarbyneContinuity ()

------------------------------------------------------------------------
-- Acquisition moves from existence of brokerage to decision/transaction join.
------------------------------------------------------------------------

data BrokerageDebt : Set where
  audioExactTimestampAndTranscript : BrokerageDebt
  completedBarakThielMeetingTopic : BrokerageDebt
  palantirBoardInternalResponse : BrokerageDebt
  foundersFundCarbyneDecisionRecord : BrokerageDebt
  epsteinRoleInFoundersFundDecision : BrokerageDebt
  traePalantirAndurilRoleTimeline : BrokerageDebt

record BrokerageAcquisition : Set where
  constructor brokerage-acquisition
  field
    debt : BrokerageDebt
    priority : Nat
    instruction : String
open BrokerageAcquisition public

canonicalBrokerageAcquisition : List BrokerageAcquisition
canonicalBrokerageAcquisition =
  brokerage-acquisition palantirBoardInternalResponse 100
    "Search Thiel/Palantir correspondence, board materials or explicit rejection records for any response to Epstein's proposed Barak board route; proposal alone is not appointment authority." ∷
  brokerage-acquisition completedBarakThielMeetingTopic 100
    "Resolve actual Barak-Thiel meeting dates/attendees/topics and determine whether Palantir, Israeli government/security matters or other subjects were discussed rather than importing the 2013 proposal into later meetings." ∷
  brokerage-acquisition foundersFundCarbyneDecisionRecord 100
    "Acquire Founders Fund diligence/investment records for Carbyne, including Trae Stephens' role, terms and decision authority; introduction does not identify investment causation." ∷
  brokerage-acquisition epsteinRoleInFoundersFundDecision 99
    "Resolve whether Epstein did more than forward/flag the Carbyne meeting to Thiel; search follow-up, recommendation, diligence or decision communications on the same financing object." ∷
  brokerage-acquisition audioExactTimestampAndTranscript 98
    "Acquire a stable official transcript/timestamp for the EFTA01621008 audio so the 2013 Palantir-board proposal is pinned directly to the carrier rather than relying on later reporting summaries." ∷
  brokerage-acquisition traePalantirAndurilRoleTimeline 98
    "Map Trae Stephens' Palantir national-security role, Founders Fund role and Anduril founding chronology separately before using him as a personnel-transfer bridge."
  ∷ []
