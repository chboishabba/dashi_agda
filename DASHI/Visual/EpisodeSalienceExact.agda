module DASHI.Visual.EpisodeSalienceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- EPISODE SALIENCE
--
-- Salience is a deterministic presentation policy over already-observed
-- semantic change counts. It may order candidate videos; it never changes the
-- history graph, semantic graph, or proof authority.
------------------------------------------------------------------------

record EpisodeChangeCounts : Set where
  constructor episodeChangeCounts
  field
    branchNodeChurn : Nat
    branchEdgeChurn : Nat
    branchStepCount : Nat
    mergeOnlyNodeCount : Nat
    mergeOnlyEdgeCount : Nat

open EpisodeChangeCounts public

record EpisodeSalienceWeights : Set where
  constructor episodeSalienceWeights
  field
    nodeWeight : Nat
    edgeWeight : Nat
    stepWeight : Nat
    mergeNodeBonus : Nat
    mergeEdgeBonus : Nat

open EpisodeSalienceWeights public

canonicalEpisodeSalienceWeights : EpisodeSalienceWeights
canonicalEpisodeSalienceWeights =
  episodeSalienceWeights
    5
    1
    1
    3
    1

episodeSalience :
  EpisodeSalienceWeights →
  EpisodeChangeCounts →
  Nat
episodeSalience weights counts =
    nodeWeight weights * branchNodeChurn counts
  + edgeWeight weights * branchEdgeChurn counts
  + stepWeight weights * branchStepCount counts
  + mergeNodeBonus weights * mergeOnlyNodeCount counts
  + mergeEdgeBonus weights * mergeOnlyEdgeCount counts

canonicalSimpleEpisode :
  EpisodeChangeCounts
canonicalSimpleEpisode =
  episodeChangeCounts
    2
    0
    2
    1
    0

canonicalSimpleEpisodeScore :
  episodeSalience
    canonicalEpisodeSalienceWeights
    canonicalSimpleEpisode
  ≡ 15
canonicalSimpleEpisodeScore = refl

record EpisodeSalienceBoundary : Set where
  constructor episodeSalienceBoundary
  field
    salienceMayRewriteHistory : Bool
    salienceMayRewriteHistoryIsFalse :
      salienceMayRewriteHistory ≡ false

    salienceMayInventSemanticChange : Bool
    salienceMayInventSemanticChangeIsFalse :
      salienceMayInventSemanticChange ≡ false

    salienceDefinesProofPriority : Bool
    salienceDefinesProofPriorityIsFalse :
      salienceDefinesProofPriority ≡ false

    salienceMayOrderPresentationCandidates : Bool
    salienceMayOrderPresentationCandidatesIsTrue :
      salienceMayOrderPresentationCandidates ≡ true

canonicalEpisodeSalienceBoundary :
  EpisodeSalienceBoundary
canonicalEpisodeSalienceBoundary =
  episodeSalienceBoundary
    false refl
    false refl
    false refl
    true refl
