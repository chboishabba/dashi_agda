module DASHI.Interop.SLRLabelledDiscoursePathExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LABELLED -> NOISY MULTI-HOP DISCOURSE PATH
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_labelled_discourse_path.py
--   schema = slr-labelled-discourse-path-v1
--
-- A requested canonical-claim transition may contain an intervening labelled
-- speaker turn inside one noisy parser sentence.  Such an intermediate turn
-- must be preserved; it may not be silently collapsed into a direct edge.
------------------------------------------------------------------------

data WeldState : Set where
  exact : WeldState
  bounded : WeldState
  unpaid : WeldState

record LabelledHop : Set where
  constructor labelledHop
  field
    goldBoundaryReference : String
    leftSpeakerReference : String
    rightSpeakerReference : String
    alignmentReference : String
    weldState : WeldState
    boundaryCharacterReference : String
    candidateOnly : Bool

open LabelledHop public

record LabelledDiscoursePath : Set where
  constructor labelledDiscoursePath
  field
    parserSentenceReference : String
    leftCanonicalClaimReference : String
    rightCanonicalClaimReference : String
    hops : List LabelledHop
    intermediateSpeakerReferences : List String
    directHandoff : Bool
    skipIntermediateSpeakerPermitted : Bool
    semanticPromotion : Bool
    claimTruthPromoted : Bool

open LabelledDiscoursePath public

------------------------------------------------------------------------
-- Concrete ABC 7.30 path shapes discovered by the gold/noisy alignment.
------------------------------------------------------------------------

sentence42Path : LabelledDiscoursePath
sentence42Path = labelledDiscoursePath
  "spaCy-42"
  "ABC730-2026-09-09-C029"
  "ABC730-2026-09-09-C030"
  (labelledHop
    "gold-speaker-017"
    "Penny Wong"
    "Jacob Greber"
    "exact-neighbour"
    exact
    "noisy boundary position paid by gold alignment"
    true
  ∷ labelledHop
    "gold-speaker-018"
    "Jacob Greber"
    "Ed Husic"
    "local"
    bounded
    "noisy boundary position retained as bounded"
    true
  ∷ [])
  ("Jacob Greber" ∷ [])
  false
  false
  false
  false

sentence45Path : LabelledDiscoursePath
sentence45Path = labelledDiscoursePath
  "spaCy-45"
  "ABC730-2026-09-09-C032"
  "ABC730-2026-09-09-C033"
  (labelledHop
    "gold-speaker-020"
    "David Shoebridge"
    "Julian Leeser"
    "local"
    bounded
    "b45-7 / local labelled alignment"
    true
  ∷ [])
  []
  true
  true
  false
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MultiHopMayCollapseToDirectEdge : Set where
data BoundedHopIsExactSubspanWeld : Set where
data ExactBoundaryPromotesClaimTruth : Set where
data ReporterInterpositionMayBeDropped : Set where

multiHopMayNotCollapse : MultiHopMayCollapseToDirectEdge → ⊥
multiHopMayNotCollapse ()

boundedIsNotExact : BoundedHopIsExactSubspanWeld → ⊥
boundedIsNotExact ()

exactBoundaryDoesNotPromoteTruth : ExactBoundaryPromotesClaimTruth → ⊥
exactBoundaryDoesNotPromoteTruth ()

reporterInterpositionMayNotBeDropped : ReporterInterpositionMayBeDropped → ⊥
reporterInterpositionMayNotBeDropped ()
