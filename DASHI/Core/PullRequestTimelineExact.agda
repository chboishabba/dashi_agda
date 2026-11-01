module DASHI.Core.PullRequestTimelineExact where

open import DASHI.Core.Prelude

record PullRequestEvent : Set where
  constructor pullRequestEvent
  field
    pullRequestNumber : Nat
    pullRequestTitle : String
    pullRequestHead : String
    pullRequestBase : String
    pullRequestMergeCommit : String

open PullRequestEvent public

record PullRequestTimelineBoundary : Set where
  constructor pullRequestTimelineBoundary
  field
    pullRequestMetadataMayInventSemanticGraphEdge : Bool
    pullRequestMetadataMayInventSemanticGraphEdgeIsFalse :
      pullRequestMetadataMayInventSemanticGraphEdge ≡ false

    pullRequestMetadataMayNameNarrativeEpisode : Bool
    pullRequestMetadataMayNameNarrativeEpisodeIsTrue :
      pullRequestMetadataMayNameNarrativeEpisode ≡ true

    gitCommitParentageRemainsHistoryAuthority : Bool
    gitCommitParentageRemainsHistoryAuthorityIsTrue :
      gitCommitParentageRemainsHistoryAuthority ≡ true

canonicalPullRequestTimelineBoundary : PullRequestTimelineBoundary
canonicalPullRequestTimelineBoundary =
  pullRequestTimelineBoundary
    false refl
    true refl
    true refl
