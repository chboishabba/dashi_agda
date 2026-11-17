module DASHI.Moonshine.OggSSP2BAugmentationArrowEliminationExact where

------------------------------------------------------------------------
-- PROOF-BEARING AUGMENTATION-ARROW ELIMINATION
--
-- For P ~= F2^24 normal in 2^24.Co1, a nontrivial P-action on a finite-length
-- module with Co1 composition factors drawn from {1,274} has a first nonzero
-- augmentation-filtration layer.  That layer supplies a nonzero Co1-equivariant
-- arrow 24 tensor X -> Y for X,Y in {1,274}.
--
-- The GAP screen computes that all four possible Hom spaces vanish.  This file
-- makes the logical promotion explicit: once the standard filtration extraction
-- has produced a relevant arrow, a zero-Hom receipt eliminates every possible
-- nontrivial normal-2^24 action.  The actual Hom calculation remains an external
-- runtime receipt; it is not manufactured here.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

-- The only simple kinds occurring in the candidate actual Tate Co1 profile.
data Co1FactorKind : Set where
  trivial1 simple274 : Co1FactorKind

-- The four possible first augmentation arrows 24 tensor X -> Y.
data RelevantAugmentationArrow : Set where
  arrow1to1       : RelevantAugmentationArrow
  arrow1to274     : RelevantAugmentationArrow
  arrow274to1     : RelevantAugmentationArrow
  arrow274to274   : RelevantAugmentationArrow

-- Proof-relevant output of the standard first-nonzero-layer extraction.
record NontrivialNormalActionEvidence : Set where
  constructor nontrivial-normal-action-evidence
  field
    firstNonzeroAugmentationArrow : RelevantAugmentationArrow

open NontrivialNormalActionEvidence public

-- Runtime Hom=0 results are promoted only through an eliminator for each
-- possible arrow.  This prevents a Boolean screen result from becoming a
-- theorem without a proof-bearing bridge.
record AllRelevantAugmentationHomsZero : Set where
  constructor all-relevant-augmentation-homs-zero
  field
    eliminateRelevantArrow : RelevantAugmentationArrow → ⊥

open AllRelevantAugmentationHomsZero public

nontrivialActionProducesRelevantArrow :
  NontrivialNormalActionEvidence → RelevantAugmentationArrow
nontrivialActionProducesRelevantArrow = firstNonzeroAugmentationArrow

zeroRelevantArrowsForceTrivialNormalAction :
  AllRelevantAugmentationHomsZero →
  NontrivialNormalActionEvidence →
  ⊥
zeroRelevantArrowsForceTrivialNormalAction zero action =
  eliminateRelevantArrow zero (nontrivialActionProducesRelevantArrow action)

------------------------------------------------------------------------
-- Same-object boundary.
--
-- To apply the theorem to the actual Tate head one still needs:
--   1. the actual Co1 factor profile {1,274,1};
--   2. the augmentation-filtration extraction for that actual module;
--   3. proof-bearing ingestion of the four runtime Hom-space zeros.
-- No literal Tate<->Co1 module identification is asserted here.
------------------------------------------------------------------------
