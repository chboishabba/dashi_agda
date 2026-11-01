module DASHI.Cognition.PNF.SensibLawFriendlyjordiesCompetingNarrativeExact where

------------------------------------------------------------------------
-- FRIENDLYJORDIES / CLIMATE CHANGE POLITICS AU
-- EXISTING-SENSIBLAW COMPETING-NARRATIVE WELD
--
-- Runtime/source donors:
--   SensibLaw/demo/narrative/friendlyjordies_thread_extract.json
--   SensibLaw/demo/narrative/friendlyjordies_chat_arguments.json
--   SensibLaw/demo/narrative/friendlyjordies_authority_wrappers.json
--   SensibLaw/src/reporting/narrative_fixture_refresh.py
--   ITIR-suite/docs/planning/
--     friendlyjordies_narrative_validation_and_competing_narratives_20260309.md
--
-- This owner does NOT decide the political claims.  It proves that the
-- existing SensibLaw M12/S28 carriers can represent the named public-media
-- proving case without collapsing attribution, disagreement, provenance,
-- chronology, or review into truth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as Narrative
import DASHI.Reasoning.SensibLawCorpusWorldPNFBridgeExact as Horizon

------------------------------------------------------------------------
-- Source-pinned public case coordinates.
------------------------------------------------------------------------

sensibLawRevision : String
sensibLawRevision = "SensibLaw/main f9c4670ef04b40e8153caa7dd00fa1eba7013ef4"

itirSuiteRevision : String
itirSuiteRevision = "ITIR-suite/main 6e3114ddb50b59c4b64c1671ccb8264532d04289"

threadRef : String
threadRef = "Climate Change Politics AU / 69ac40e0-0cfc-839b-b2a8-0de3019379a9"

data ArgumentFamily : Set where
  cprsBlocking : ArgumentFamily
  woolworthsPrice : ArgumentFamily
  governmentCapacity : ArgumentFamily
  etsDelayAuthority : ArgumentFamily
  fallaciesFraming : ArgumentFamily

------------------------------------------------------------------------
-- Existing S28 proposition roots.  These are topics/questions, not verdicts.
------------------------------------------------------------------------

cprsRoot : Contest.PropositionRoot
cprsRoot =
  Contest.proposition-root
    "proposition:friendlyjordies:cprs-blocking"
    "CPRS blocking / downstream climate-policy effects"
    true refl false refl false refl false refl

governmentCapacityRoot : Contest.PropositionRoot
governmentCapacityRoot =
  Contest.proposition-root
    "proposition:friendlyjordies:government-capacity"
    "majority/minority government and long-run policy capacity"
    true refl false refl false refl false refl

priceRoot : Contest.PropositionRoot
priceRoot =
  Contest.proposition-root
    "proposition:friendlyjordies:woolworths-price"
    "Woolworths / direct pass-through / broader price effects"
    true refl false refl false refl false refl

------------------------------------------------------------------------
-- Claim leaves remain distinct even when attached to one proposition root.
------------------------------------------------------------------------

jordiesCPRSClaim : Contest.ClaimLeaf cprsRoot
jordiesCPRSClaim =
  Contest.claim-leaf
    "claim:friendlyjordies:cprs-instability"
    Contest.affirmation
    "speaker:friendlyjordies"
    ("statement:friendlyjordies:cprs-instability" ∷ [])
    ("observation:friendlyjordies:cprs-instability" ∷ [])
    []
    ("scope:historical-cprs" ∷ [])
    Contest.unreviewed
    "review:friendlyjordies:cprs-instability"
    "relation:source-trace:friendlyjordies:cprs-instability"
    true refl false refl false refl false refl

counterCPRSClaim : Contest.ClaimLeaf cprsRoot
counterCPRSClaim =
  Contest.claim-leaf
    "claim:counter-analysis:coalition-instability"
    Contest.alternativeAccount
    "speaker:counter-analysis"
    ("statement:counter-analysis:coalition-instability" ∷ [])
    ("observation:counter-analysis:coalition-instability" ∷ [])
    []
    ("scope:historical-cprs" ∷ [])
    Contest.unreviewed
    "review:counter-analysis:coalition-instability"
    "relation:source-trace:counter-analysis:coalition-instability"
    true refl false refl false refl false refl

cprsCompetingAccount : Contest.ContestationRelation jordiesCPRSClaim counterCPRSClaim
cprsCompetingAccount =
  Contest.contestation-relation
    "contestation:friendlyjordies:cprs-causal-account"
    Contest.sameIncidentDifferentAccount
    ("statement:friendlyjordies:cprs-instability"
      ∷ "statement:counter-analysis:coalition-instability"
      ∷ [])
    ("observation:friendlyjordies:cprs-instability"
      ∷ "observation:counter-analysis:coalition-instability"
      ∷ [])
    "review:friendlyjordies:cprs-causal-account"
    "relation:source-trace:cprs-competing-account"
    true refl false refl false refl false refl

------------------------------------------------------------------------
-- Attribution wrapper: "X argued/reported that P" is retained as an
-- attribution-bearing claim, not silently rewritten to P.
------------------------------------------------------------------------

record AttributionWrapper : Set where
  constructor attribution-wrapper
  field
    wrapperRef : String
    outerSpeakerRef : String
    attributedSpeakerRef : String
    propositionRef : String
    statementRef : String
    sourceRevisionRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open AttributionWrapper public

garnautWrapper : AttributionWrapper
garnautWrapper =
  attribution-wrapper
    "attribution:friendlyjordies:garnaut-imperfect-ets"
    "speaker:friendlyjordies"
    "authority:ross-garnaut"
    "proposition:imperfect-ets-better-than-delay"
    "statement:friendlyjordies:garnaut-imperfect-ets"
    sensibLawRevision
    true refl false refl

data AttributionWrapperIsUnderlyingTruth : Set where

attributionDoesNotCollapseToUnderlyingTruth :
  AttributionWrapperIsUnderlyingTruth → ⊥
attributionDoesNotCollapseToUnderlyingTruth ()

------------------------------------------------------------------------
-- M12 trace witness: source identity/span survives through the semantic path.
------------------------------------------------------------------------

cprsStatement : Trace.PersistentStatementIdentity
cprsStatement =
  Trace.persistent-statement-identity
    "statement:friendlyjordies:cprs-instability"
    "demo/narrative/friendlyjordies_thread_extract.json"
    sensibLawRevision
    "jordies_thread_position:u2"
    "FriendlyJordies argued that blocking the CPRS contributed to climate policy instability."

cprsParserRun : Trace.ParserRunIdentity
cprsParserRun =
  Trace.parser-run-identity
    "parser-run:friendlyjordies:cprs"
    "sensiblaw-narrative-fixture"

cprsStatementObservation : Trace.StatementCandidateObservationLink
cprsStatementObservation =
  Trace.statement-candidate-observation-link
    cprsStatement
    "pnf:friendlyjordies:cprs-instability"
    "observation:friendlyjordies:cprs-instability"
    cprsParserRun
    "review:parse:friendlyjordies:cprs-instability"
    "admission:candidate:friendlyjordies:cprs-instability"
    true refl false refl false refl false refl

cprsObservationEvent : Trace.ObservationEventLink
cprsObservationEvent =
  Trace.observation-event-link
    "observation:friendlyjordies:cprs-instability"
    "event:public-discourse:cprs"
    "assembly:friendlyjordies:cprs"
    true refl false refl

cprsTrace : Trace.SemanticTracePath
cprsTrace =
  Trace.traceFromLinks
    cprsStatementObservation
    cprsObservationEvent
    ("claim:friendlyjordies:cprs-instability" ∷ [])
    ("contestation:friendlyjordies:cprs-causal-account" ∷ [])

cprsForwardReceipt : Trace.ForwardTraceReceipt cprsTrace
cprsForwardReceipt = Trace.canonicalForwardTrace cprsTrace

cprsReverseReceipt : Trace.ReverseTraceReceipt cprsTrace
cprsReverseReceipt = Trace.canonicalReverseTrace cprsTrace

------------------------------------------------------------------------
-- Existing narrative provenance law: repetition raises salience but does not
-- create an independent evidential origin.
------------------------------------------------------------------------

threadLineage : Narrative.EvidenceLineage
threadLineage = Narrative.evidenceLineage 0 0

threadReplicated : Narrative.EvidenceLineage
threadReplicated = Narrative.replicateEvidence threadLineage

threadReplicationPreservesOrigin :
  Narrative.originId threadReplicated ≡ Narrative.originId threadLineage
threadReplicationPreservesOrigin =
  Narrative.replicationPreservesOrigin threadLineage

threadReplicationCannotWitnessIndependence :
  Narrative.IndependentEvidencePair threadLineage threadReplicated → ⊥
threadReplicationCannotWitnessIndependence =
  Narrative.replicationDoesNotCreateIndependentEvidence threadLineage

------------------------------------------------------------------------
-- Document-local extraction is not external-world resolution.
------------------------------------------------------------------------

record FriendlyjordiesResolutionDemand : Set where
  constructor friendlyjordies-resolution-demand
  field
    propositionRef : String
    requiredHorizon : Horizon.PNFResolutionHorizon
    sourceReference : String
    unresolvedReference : String

cprsWorldDemand : FriendlyjordiesResolutionDemand
cprsWorldDemand =
  friendlyjordies-resolution-demand
    "proposition:friendlyjordies:cprs-blocking"
    Horizon.externalWorldHorizon
    "fixture:friendlyjordies_thread_extract"
    "demand:independent-historical-corroboration"

------------------------------------------------------------------------
-- Comparison surface: shared, source-local, conflicting and unresolved remain
-- separate coordinates.  There is deliberately no winner field.
------------------------------------------------------------------------

record CompetingNarrativeComparison : Set where
  constructor competing-narrative-comparison
  field
    leftNarrativeRef : String
    rightNarrativeRef : String
    sharedPropositionRefs : List String
    leftOnlyClaimRefs : List String
    rightOnlyClaimRefs : List String
    contestationRefs : List String
    unresolvedRefs : List String
    sourceReceiptRefs : List String
    hiddenVerdict : Bool
    hiddenVerdictIsFalse : hiddenVerdict ≡ false
    truthScorePresent : Bool
    truthScorePresentIsFalse : truthScorePresent ≡ false

open CompetingNarrativeComparison public

canonicalFriendlyjordiesComparison : CompetingNarrativeComparison
canonicalFriendlyjordiesComparison =
  competing-narrative-comparison
    "narrative:friendlyjordies-position"
    "narrative:counter-analysis"
    ("proposition:friendlyjordies:cprs-blocking" ∷ [])
    ("claim:friendlyjordies:cprs-instability" ∷ [])
    ("claim:counter-analysis:coalition-instability" ∷ [])
    ("contestation:friendlyjordies:cprs-causal-account" ∷ [])
    ("demand:independent-historical-corroboration" ∷ [])
    (sensibLawRevision ∷ itirSuiteRevision ∷ threadRef ∷ [])
    false refl
    false refl

------------------------------------------------------------------------
-- Promotion firewalls inherited by the application.
------------------------------------------------------------------------

data ComparisonCreatesTruthVerdict : Set where
data SharedRootMergesAccounts : Set where
data SourceFixtureCreatesWorldResolution : Set where
data RepeatedClaimCreatesIndependentCorroboration : Set where

comparisonDoesNotCreateTruthVerdict : ComparisonCreatesTruthVerdict → ⊥
comparisonDoesNotCreateTruthVerdict ()

sharedRootDoesNotMergeAccounts : SharedRootMergesAccounts → ⊥
sharedRootDoesNotMergeAccounts ()

fixtureDoesNotCreateWorldResolution : SourceFixtureCreatesWorldResolution → ⊥
fixtureDoesNotCreateWorldResolution ()

repetitionDoesNotCreateIndependentCorroboration :
  RepeatedClaimCreatesIndependentCorroboration → ⊥
repetitionDoesNotCreateIndependentCorroboration ()

record FriendlyjordiesSensibLawBoundary : Set where
  constructor friendlyjordies-sensiblaw-boundary
  field
    usesPersistentM12Trace : Bool
    usesS28PropositionClaimSeparation : Bool
    contestationTypedNotScalar : Bool
    attributionRetained : Bool
    sourceRevisionRetained : Bool
    externalWorldResolutionRequired : Bool
    comparisonContainsHiddenVerdict : Bool
    comparisonContainsTruthScore : Bool

canonicalFriendlyjordiesSensibLawBoundary : FriendlyjordiesSensibLawBoundary
canonicalFriendlyjordiesSensibLawBoundary =
  friendlyjordies-sensiblaw-boundary
    true true true true true true false false
