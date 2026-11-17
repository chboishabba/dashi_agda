module DASHI.Governance.BoloBoloOWSContemporaneousBurdenControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- CONTEMPORANEOUS OWS SPOKES BURDEN / CONTROL EVIDENCE
--
-- Attribution firewall:
--
-- * Observer 2011 = contemporaneous journalism about the first Spokes meeting.
-- * In Front and Center 2011 = contemporaneous publication of a first-person
--   participant statement concerning the 9 Nov Spokes meeting.
-- * neither source = primary NYCGA Spokes minutes.
-- * DASHI's source-role typing below = derived formalisation only.
--
-- A first-person burden report is retained as such. It is not silently
-- upgraded into complete event ground truth, a population-level effect, a
-- domination finding or a causal estimate.
------------------------------------------------------------------------

data ContemporaneousSpokesSourceRole : Set where
  contemporaneousJournalism : ContemporaneousSpokesSourceRole
  contemporaneousParticipantStatement : ContemporaneousSpokesSourceRole

record ContemporaneousSpokesEvidence : Set where
  constructor contemporaneous-spokes-evidence
  field
    sourceRole : ContemporaneousSpokesSourceRole
    publicationDate : String
    sourceTitle : String
    sourceLocator : String
    meetingReference : String
    sourceSupports : String
    sourceDoesNotByItselfSupport : String

open ContemporaneousSpokesEvidence public

observerNov8 : ContemporaneousSpokesEvidence
observerNov8 =
  contemporaneous-spokes-evidence
    contemporaneousJournalism
    "2011-11-08"
    "Occupy Wall Street Moves Indoors With Spokes Council"
    "https://observer.com/2011/11/occupy-wall-street-moves-indoors-with-spokes-council/"
    "first Spokes Council meeting, 2011-11-07"
    "contemporaneous journalistic report that the first Spokes Council meeting occurred in Murray Bergtraum High School cafeteria; reports use of an electric microphone / turn-taking surface, working-group viability and day-to-day logistics as stated functions, and a press-admission temperature-check dispute"
    "primary Spokes minutes, complete attendance, exact decision incidence, causal coordination effect, non-domination, legitimacy or population-level burden"

participantNov11 : ContemporaneousSpokesEvidence
participantNov11 =
  contemporaneous-spokes-evidence
    contemporaneousParticipantStatement
    "2011-11-11"
    "OWS Must Resist Cis-Supremacy and Trans-Misogyny"
    "https://infrontandcenter.wordpress.com/2011/11/11/ows-must-resist-cis-supremacy-and-trans-misogyny/"
    "participant statement concerning 2011-11-09 Spokes Council"
    "first-person statement that the author served as a spoke at the November 9 meeting and experienced a severe panic attack which they attributed to angry, extra-procedural discussion of heavy topics; also reports alarm about disturbances involving an unrecognized affinity group"
    "primary Spokes minutes, independent verification of every event allegation, general systemic burden, domination, causal effect, group culpability, legitimacy or representativeness of all participants"

canonicalContemporaneousSpokesEvidence : List ContemporaneousSpokesEvidence
canonicalContemporaneousSpokesEvidence =
  observerNov8 ∷ participantNov11 ∷ []

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record OWSContemporaneousBurdenControlBoundary : Set where
  constructor ows-contemporaneous-burden-control-boundary
  field
    contemporaneousJournalismMaySupportBoundedVenueProcessObservation : Bool
    participantStatementMaySupportSelfReportedBurden : Bool
    contemporaneousJournalismEqualsPrimarySpokesMinutes : Bool
    participantStatementEqualsPrimarySpokesMinutes : Bool
    oneParticipantBurdenProvesGeneralSystemicBurden : Bool
    participantAttributionProvesCausalMechanism : Bool
    journalisticProcessDescriptionProvesRealisedPowerTopology : Bool
    sourceAgreementCreatesIndependentPrimaryMinute : Bool
    sourceDisagreementMustRemainRepresentable : Bool
    futurePrimaryMinutesMayCorroborateOrContradictTheseSources : Bool

open OWSContemporaneousBurdenControlBoundary public

canonicalOWSContemporaneousBurdenControlBoundary :
  OWSContemporaneousBurdenControlBoundary
canonicalOWSContemporaneousBurdenControlBoundary =
  ows-contemporaneous-burden-control-boundary
    true
    true
    false
    false
    false
    false
    false
    false
    true
    true

canonicalOWSContemporaneousBurdenControlReceipt : GenericReceipt.GenericReceipt
canonicalOWSContemporaneousBurdenControlReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS contemporaneous Spokes burden/control evidence"
    "DASHI.Governance.BoloBoloOWSContemporaneousBurdenControlExact"
    "observerNov8 / participantNov11 / canonicalOWSContemporaneousBurdenControlBoundary"
    "retains a contemporaneous journalistic first-meeting venue/process report and a separately published first-person November 9 Spokes burden account as distinct source roles that may calibrate later realised-control/burden coding"
    "neither source becomes the primary NYCGA minutes; one participant self-report is not population-level burden, domination or a causal estimate; journalism does not establish complete realised power topology; later primary minutes may corroborate, narrow or contradict these records"
    "agda -i . DASHI/Governance/BoloBoloOWSContemporaneousBurdenControlRegression.agda"
