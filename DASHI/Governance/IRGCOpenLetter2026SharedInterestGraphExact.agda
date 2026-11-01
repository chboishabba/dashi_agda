module DASHI.Governance.IRGCOpenLetter2026SharedInterestGraphExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IRGCOpenLetter2026StrategicCommunicationExact as Letter

------------------------------------------------------------------------
-- Source-verifiable argument topology.
-- The constructors below attest that the PRIMARY ARTIFACT contains these
-- argumentative moves.  They do not establish the moves' geopolitical truth.
------------------------------------------------------------------------

data ArgumentNode : Set where
  peopleStateDistinction commonOppressorAssertion sharedVictimAssertion
  popularAgencyAssertion conditionalCoexistenceAssertion
  liberationAssertion eschatologicalCompletion : ArgumentNode

data SourceEdge : ArgumentNode → ArgumentNode → Set where
  distinguishThenCommonOppressor :
    SourceEdge peopleStateDistinction commonOppressorAssertion
  commonOppressorThenSharedVictim :
    SourceEdge commonOppressorAssertion sharedVictimAssertion
  sharedVictimThenAgency :
    SourceEdge sharedVictimAssertion popularAgencyAssertion
  agencyThenCoexistence :
    SourceEdge popularAgencyAssertion conditionalCoexistenceAssertion
  coexistenceThenLiberation :
    SourceEdge conditionalCoexistenceAssertion liberationAssertion
  liberationThenEschatology :
    SourceEdge liberationAssertion eschatologicalCompletion

record SourceArgumentTopology : Set where
  constructor sourceArgumentTopology
  field
    e1 : SourceEdge peopleStateDistinction commonOppressorAssertion
    e2 : SourceEdge commonOppressorAssertion sharedVictimAssertion
    e3 : SourceEdge sharedVictimAssertion popularAgencyAssertion
    e4 : SourceEdge popularAgencyAssertion conditionalCoexistenceAssertion
    e5 : SourceEdge conditionalCoexistenceAssertion liberationAssertion
    e6 : SourceEdge liberationAssertion eschatologicalCompletion
    sourceReceipt : String

canonicalTopology : SourceArgumentTopology
canonicalTopology = sourceArgumentTopology
  distinguishThenCommonOppressor
  commonOppressorThenSharedVictim
  sharedVictimThenAgency
  agencyThenCoexistence
  coexistenceThenLiberation
  liberationThenEschatology
  "IRGC 2026 primary English PDF: source-local argumentative sequence"

data SharedInterestFactEstablished : Set where

sourceSharedVictimFrameDoesNotEstablishSharedInterestFact :
  SourceArgumentTopology → SharedInterestFactEstablished → ⊥
sourceSharedVictimFrameDoesNotEstablishSharedInterestFact topology ()

data ThreatClassificationEstablished : Set where

warningDoesNotAutoPromoteToThreat :
  Letter.SpeechAct → ThreatClassificationEstablished → ⊥
warningDoesNotAutoPromoteToThreat act ()

data PropagandaEfficacyEstablished : Set where

sourceStructureDoesNotEstablishPropagandaEfficacy :
  SourceArgumentTopology → PropagandaEfficacyEstablished → ⊥
sourceStructureDoesNotEstablishPropagandaEfficacy topology ()

record AgencyHistoryEschatologyBracket : Set where
  constructor agencyHistoryEschatologyBracket
  field
    openingAgencyCitation : Letter.CrossTraditionCitation
    politicalAgencyNode : ArgumentNode
    liberationNode : ArgumentNode
    closingEschatologyCitation : Letter.CrossTraditionCitation

canonicalBracket : AgencyHistoryEschatologyBracket
canonicalBracket = agencyHistoryEschatologyBracket
  Letter.quranAgency
  popularAgencyAssertion
  liberationAssertion
  Letter.quranClosure
