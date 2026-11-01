module DASHI.Interop.SLRLabelledSubspanWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LABELLED -> NOISY SUBSPAN WELD
--
-- Runtime companion:
--   tools/slr-discourse-reconstruct/slr_labelled_subspan_weld.py
--   schema = slr-labelled-subspan-weld-v1
--
-- A speaker-labelled source boundary is aligned into the noisy transcript.
-- Exact-neighbour word alignment may pay an exact boundary/subspan weld.
-- Local/weak alignment pays only a bounded candidate. Unmapped alignment pays
-- nothing. None of these states promotes claim truth.
------------------------------------------------------------------------

data WeldState : Set where
  exactWeld : WeldState
  boundedWeld : WeldState
  unpaidWeld : WeldState

data AlignmentClass : Set where
  exactNeighbour : AlignmentClass
  localAlignment : AlignmentClass
  weakAlignment : AlignmentClass
  unmappedAlignment : AlignmentClass

record LabelledSubspanWeldReceipt : Set where
  constructor labelledSubspanWeldReceipt
  field
    schemaReference : String
    noisySourceReference : String
    labelledSourceReference : String
    parserSentenceReference : String
    leftCanonicalClaimReference : String
    rightCanonicalClaimReference : String
    leftSpeakerReference : String
    rightSpeakerReference : String
    alignmentClass : AlignmentClass
    weldState : WeldState
    boundaryCharacterReference : String
    leftSubspanReference : String
    rightSubspanReference : String
    candidateOnly : Bool
    semanticPromotion : Bool
    claimTruthPromoted : Bool

open LabelledSubspanWeldReceipt public

record LabelledSubspanWeldBoundary : Set where
  constructor labelledSubspanWeldBoundary
  field
    exactRequiresExactNeighbour : Bool
    localMayPayExact : Bool
    weakMayPayExact : Bool
    unmappedMayPayBounded : Bool
    boundedWeldMayPromoteClaimTruth : Bool
    exactWeldMayPromoteClaimTruth : Bool
    historicalFixtureSpeakerStatusIsAuthority : Bool

open LabelledSubspanWeldBoundary public

canonicalLabelledSubspanWeldBoundary : LabelledSubspanWeldBoundary
canonicalLabelledSubspanWeldBoundary =
  labelledSubspanWeldBoundary true false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LocalAlignmentImpliesExactSubspan : Set where
data WeakAlignmentImpliesExactSubspan : Set where
data ExactSubspanImpliesClaimTruth : Set where
data GoldSpeakerBoundaryImpliesWorldTruth : Set where
data HistoricalFixtureStatusBecomesCurrentAuthority : Set where

localAlignmentDoesNotPayExact : LocalAlignmentImpliesExactSubspan → ⊥
localAlignmentDoesNotPayExact ()

weakAlignmentDoesNotPayExact : WeakAlignmentImpliesExactSubspan → ⊥
weakAlignmentDoesNotPayExact ()

exactSubspanDoesNotPromoteTruth : ExactSubspanImpliesClaimTruth → ⊥
exactSubspanDoesNotPromoteTruth ()

goldSpeakerBoundaryDoesNotPromoteWorldTruth : GoldSpeakerBoundaryImpliesWorldTruth → ⊥
goldSpeakerBoundaryDoesNotPromoteWorldTruth ()

historicalFixtureStatusIsNotCurrentAuthority :
  HistoricalFixtureStatusBecomesCurrentAuthority → ⊥
historicalFixtureStatusIsNotCurrentAuthority ()
