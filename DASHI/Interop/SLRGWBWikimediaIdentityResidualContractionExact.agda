module DASHI.Interop.SLRGWBWikimediaIdentityResidualContractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBReviewedWikimediaIdentityAndTieredTransportExact as Reviewed
import DASHI.Interop.SLRGWBWikimediaReplayableHandoffExact as Replay

------------------------------------------------------------------------
-- GWB WIKIMEDIA IDENTITY RESIDUAL CONTRACTION
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_gwb_identity_residual_contraction.py
--   tools/slr-discourse-reconstruct/run_gwb_identity_residual_contraction.sh
--
-- The successful Wikimedia graph pays a narrower residual than historical
-- truth: source-object identity for work-scoped seeds when an exact reviewed
-- QID or a reviewed Wikipedia title resolves to one paid QID.
--
-- Current specimen:
--   doc 8  Family of Secrets -> Q16156115  (runtime title resolution)
--   doc 10 Decision Points    -> Q942966    (reviewed exact work identity)
--
-- Documents 1-7 and 9 retain useful topic/person/family anchors but their
-- source-work identity remains unpaid.  Topic identity is not document identity.
------------------------------------------------------------------------

data SourceWorkIdentityState : Set where
  paidSourceWorkIdentity : SourceWorkIdentityState
  unpaidSourceWorkIdentity : SourceWorkIdentityState

record GWBIdentityContractionReceipt : Set where
  constructor gwbIdentityContractionReceipt
  field
    documentCount : Nat
    sourceWorkIdentityPaid : Nat
    sourceWorkIdentityUnpaid : Nat
    topicAnchorPaid : Nat
    runtimeResolvedWorkIdentities : Nat
    familyOfSecretsQid : String
    decisionPointsQid : String
    topicAnchorIsSourceObjectIdentity : Bool
    wikimediaIdentityCreatesClaimTruth : Bool
    wholeHistoricalClaimTruthPaid : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open GWBIdentityContractionReceipt public

canonicalGWBIdentityContractionReceipt : GWBIdentityContractionReceipt
canonicalGWBIdentityContractionReceipt =
  gwbIdentityContractionReceipt
    10 2 8 8 1
    "Q16156115"
    "Q942966"
    false false false true false

-- Shallow boundary consumed by downstream source-role/world consumers.  Keep
-- this distinct from the numeric runtime receipt so consumers do not have to
-- project a particular specimen count merely to state the semantic firewall.
record GWBIdentityContractionBoundary : Set where
  constructor gwbIdentityContractionBoundary
  field
    topicAnchorMayPaySourceWorkIdentity : Bool
    sourceWorkIdentityMayPayClaimTruth : Bool
    runtimeWikipediaResolutionMayPayHistoricalTruth : Bool
    exactWorkQidMayEraseSourceProvenance : Bool
    candidateOnlyBoundary : Bool
    semanticPromotionBoundary : Bool

open GWBIdentityContractionBoundary public

canonicalGWBIdentityContractionBoundary : GWBIdentityContractionBoundary
canonicalGWBIdentityContractionBoundary =
  gwbIdentityContractionBoundary false false false false true false

reviewedTransportAnchor : Reviewed.WikidataTieredTransportPolicy
reviewedTransportAnchor = Reviewed.canonicalWikidataTieredTransportPolicy

replayableHandoffAnchor : Replay.ReplayableAcquisitionBoundary
replayableHandoffAnchor = Replay.canonicalReplayableAcquisitionBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TopicAnchorPaysSourceWorkIdentity : Set where
data SourceWorkIdentityPaysClaimTruth : Set where
data RuntimeWikipediaResolutionPaysHistoricalTruth : Set where
data ExactWorkQidErasesSourceProvenance : Set where

topicAnchorDoesNotPaySourceWorkIdentity : TopicAnchorPaysSourceWorkIdentity → ⊥
topicAnchorDoesNotPaySourceWorkIdentity ()

sourceWorkIdentityDoesNotPayClaimTruth : SourceWorkIdentityPaysClaimTruth → ⊥
sourceWorkIdentityDoesNotPayClaimTruth ()

runtimeTitleResolutionDoesNotPayHistoricalTruth : RuntimeWikipediaResolutionPaysHistoricalTruth → ⊥
runtimeTitleResolutionDoesNotPayHistoricalTruth ()

exactWorkQidDoesNotEraseProvenance : ExactWorkQidErasesSourceProvenance → ⊥
exactWorkQidDoesNotEraseProvenance ()
