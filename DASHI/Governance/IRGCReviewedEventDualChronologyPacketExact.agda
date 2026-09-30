module DASHI.Governance.IRGCReviewedEventDualChronologyPacketExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.IRGCOpenLetter2026SourceAtlasExact as Sources
import DASHI.Governance.IRGCOpenLetter2026StrategicCommunicationExact as Letter
import DASHI.Governance.IRGCOpenLetter2026SharedInterestGraphExact as Graph
import DASHI.Governance.IranianRevolutionaryIntellectualGenealogyExact as Genealogy
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Chronology

------------------------------------------------------------------------
-- IRGC 2026 REVIEWED-EVENT / DUAL-CHRONOLOGY PACKET
--
-- This packet deliberately separates:
--
--   event/world time:
--     publication of the 2026 political communication
--
--   source/knowledge time:
--     later reporting and scholarly publication dates
--
-- from:
--
--   exact source-span review and historical-mechanism closure.
--
-- The existing source atlas and argument graph pay carrier/source-local
-- structure.  They do not yet pay exact PDF spans for every argument node.
------------------------------------------------------------------------

data PacketLayer : Set where
  publicationEventLayer : PacketLayer
  primaryArgumentLayer : PacketLayer
  secondaryReportLayer : PacketLayer
  historicalGenealogyLayer : PacketLayer

record ExactSpanDemand : Set where
  constructor exact-span-demand
  field
    propositionRef : String
    sourceRef : String
    requiredLocator : String
    reviewRef : String
    unresolvedReason : String
    mayPromoteTruth : Bool
    mayPromoteTruthIsFalse : mayPromoteTruth ≡ false

open ExactSpanDemand public

peopleStateSpanDemand : ExactSpanDemand
peopleStateSpanDemand =
  exact-span-demand
    "irgc:argument:people-state-distinction"
    "IRGC 2026 primary English PDF"
    "exact PDF page/span for people-versus-government distinction"
    "review:irgc:people-state"
    "source topology is paid, but exact passage coordinates are not yet attached"
    false refl

commonOppressorSpanDemand : ExactSpanDemand
commonOppressorSpanDemand =
  exact-span-demand
    "irgc:argument:common-oppressor"
    "IRGC 2026 primary English PDF"
    "exact PDF page/span for common-oppressor framing"
    "review:irgc:common-oppressor"
    "argument graph records the move but not an exact reviewed passage"
    false refl

agencySpanDemand : ExactSpanDemand
agencySpanDemand =
  exact-span-demand
    "irgc:argument:popular-agency"
    "IRGC 2026 primary English PDF"
    "exact PDF page/span for political-agency appeal"
    "review:irgc:popular-agency"
    "primary structure alone cannot substitute for a reviewed source span"
    false refl

record SourceLocalEvent : Set where
  constructor source-local-event
  field
    eventRef : String
    layer : PacketLayer
    sourceRef : String
    temporal : Chronology.TemporalAssertion
    independentlyEstablishesUnderlyingPoliticalClaim : Bool
    independentlyEstablishesUnderlyingPoliticalClaimIsFalse :
      independentlyEstablishesUnderlyingPoliticalClaim ≡ false

open SourceLocalEvent public

letterPublicationTime : Chronology.TemporalAssertion
letterPublicationTime =
  Chronology.temporal-assertion
    "time:irgc-letter:publication"
    (Chronology.exactDate "2026-09-29")
    ("IRGC 2026 primary English PDF" ∷ [])
    []
    "review:time:irgc-letter:publication"
    "source:IRGCOpenLetter2026StrategicCommunicationExact.irgcLetter"
    true refl
    false refl
    false refl
    false refl

reutersKnowledgeTime : Chronology.TemporalAssertion
reutersKnowledgeTime =
  Chronology.temporal-assertion
    "time:reuters:irgc-letter-report"
    (Chronology.exactDate "2026-09-30")
    ("Reuters report on IRGC letter publication" ∷ [])
    []
    "review:time:reuters:irgc-letter-report"
    "source:IRGCOpenLetter2026SourceAtlasExact.reutersReport"
    true refl
    false refl
    false refl
    false refl

letterPublicationEvent : SourceLocalEvent
letterPublicationEvent =
  source-local-event
    "event:irgc-letter:publication"
    publicationEventLayer
    "IRGCOpenLetter2026SourceAtlasExact.irgcPrimaryLetter"
    letterPublicationTime
    false refl

reutersObservationEvent : SourceLocalEvent
reutersObservationEvent =
  source-local-event
    "event:knowledge:reuters-irgc-letter"
    secondaryReportLayer
    "IRGCOpenLetter2026SourceAtlasExact.reutersReport"
    reutersKnowledgeTime
    false refl

------------------------------------------------------------------------
-- Historical-genealogy sources live on the knowledge/source timeline.
-- Their publication dates are not retroactively world-event dates for 1979.
------------------------------------------------------------------------

matinAsgariKnowledgeTime : Chronology.TemporalAssertion
matinAsgariKnowledgeTime =
  Chronology.temporal-assertion
    "time:knowledge:matin-asgari-2018"
    (Chronology.exactDate "2018")
    ("Both Eastern and Western" ∷ [])
    []
    "review:knowledge:matin-asgari"
    "source:IranianRevolutionaryIntellectualGenealogyExact.matinAsgari2018"
    true refl
    false refl
    false refl
    false refl

boroujerdiKnowledgeTime : Chronology.TemporalAssertion
boroujerdiKnowledgeTime =
  Chronology.temporal-assertion
    "time:knowledge:boroujerdi-2000"
    (Chronology.exactDate "2000")
    ("Islam as a modernizing ideology: Al-e Ahmad and Shari'ati" ∷ [])
    []
    "review:knowledge:boroujerdi"
    "source:IranianRevolutionaryIntellectualGenealogyExact.boroujerdiModernizingIslam"
    true refl
    false refl
    false refl
    false refl

data HistoricalSourcePublicationMeansHistoricalEventDate : Set where

sourcePublicationDoesNotBackdateWorldEvent :
  HistoricalSourcePublicationMeansHistoricalEventDate → ⊥
sourcePublicationDoesNotBackdateWorldEvent ()

------------------------------------------------------------------------
-- Packet state.
------------------------------------------------------------------------

record IRGCDualChronologyPacket : Set where
  constructor irgc-dual-chronology-packet
  field
    sourceAtlas : DASHI.Core.AttributedSourceCore.AttributedSourceAtlas
    sourceArgumentTopology : Graph.SourceArgumentTopology
    openingAgencyCitation : Letter.CrossTraditionCitation
    closingEschatologyCitation : Letter.CrossTraditionCitation
    eventTimeEntries : List SourceLocalEvent
    knowledgeTimeAssertions : List Chronology.TemporalAssertion
    exactSpanDemands : List ExactSpanDemand
    sourceRolesPaid : Bool
    sourceRolesPaidIsTrue : sourceRolesPaid ≡ true
    sourceArgumentTopologyPaid : Bool
    sourceArgumentTopologyPaidIsTrue :
      sourceArgumentTopologyPaid ≡ true
    dualChronologyRepresented : Bool
    dualChronologyRepresentedIsTrue :
      dualChronologyRepresented ≡ true
    exactPrimarySpansPaid : Bool
    exactPrimarySpansPaidIsFalse :
      exactPrimarySpansPaid ≡ false
    reviewedEventJoinPaid : Bool
    reviewedEventJoinPaidIsFalse :
      reviewedEventJoinPaid ≡ false
    historicalMechanismClosed : Bool
    historicalMechanismClosedIsFalse :
      historicalMechanismClosed ≡ false
    worldTruthPromoted : Bool
    worldTruthPromotedIsFalse :
      worldTruthPromoted ≡ false

open IRGCDualChronologyPacket public

canonicalIRGCDualChronologyPacket : IRGCDualChronologyPacket
canonicalIRGCDualChronologyPacket =
  irgc-dual-chronology-packet
    Sources.letterAtlas
    Graph.canonicalTopology
    Letter.quranAgency
    Letter.quranClosure
    (letterPublicationEvent ∷ reutersObservationEvent ∷ [])
    (matinAsgariKnowledgeTime ∷ boroujerdiKnowledgeTime ∷ [])
    ( peopleStateSpanDemand
    ∷ commonOppressorSpanDemand
    ∷ agencySpanDemand
    ∷ [])
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Historical-genealogy anchors are carried as source-paid edges, but packet
-- closure still requires reviewed exact passages / event joins for the claims
-- actually used in a trajectory.
------------------------------------------------------------------------

fieldContinuityEdges : List Genealogy.GenealogyEdge
fieldContinuityEdges =
  Genealogy.marxianFieldToShariati
  ∷ Genealogy.thirdWorldismToShariati
  ∷ Genealogy.shariatiToRevolutionaryGeneration
  ∷ Genealogy.iranianLeftToKhomeiniWestGrammar
  ∷ []

data SourceArgumentGraphCreatesWorldTruth : Set where
data DualChronologyCreatesHistoricalMechanism : Set where
data SourceRoleCreatesReviewedEventJoin : Set where
data SecondaryReportReplacesPrimarySpan : Set where
data HistoricalGenealogyAutomaticallyExplainsIRGCLetter : Set where

sourceGraphDoesNotCreateWorldTruth :
  SourceArgumentGraphCreatesWorldTruth → ⊥
sourceGraphDoesNotCreateWorldTruth ()

dualChronologyDoesNotCreateHistoricalMechanism :
  DualChronologyCreatesHistoricalMechanism → ⊥
dualChronologyDoesNotCreateHistoricalMechanism ()

sourceRoleDoesNotCreateReviewedEventJoin :
  SourceRoleCreatesReviewedEventJoin → ⊥
sourceRoleDoesNotCreateReviewedEventJoin ()

secondaryReportDoesNotReplacePrimarySpan :
  SecondaryReportReplacesPrimarySpan → ⊥
secondaryReportDoesNotReplacePrimarySpan ()

genealogyDoesNotAutomaticallyExplainLetter :
  HistoricalGenealogyAutomaticallyExplainsIRGCLetter → ⊥
genealogyDoesNotAutomaticallyExplainLetter ()
