module DASHI.Core.VersionedStateGraphExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact

------------------------------------------------------------------------
-- VERSIONED-STATE / BRANCH / MERGE SURFACE
--
-- Git is one producer of this structure.  Casey-style candidate/workspace
-- histories can inhabit the more general VersionedStateProvider below.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record CommitNode : Set where
  constructor commitNode
  field
    commitId : String
    commitParents : List String

open CommitNode public

data CommitShape : Set where
  rootCommit : CommitShape
  linearCommit : CommitShape
  mergeCommit : CommitShape

commitShape : CommitNode → CommitShape
commitShape (commitNode _ []) = rootCommit
commitShape (commitNode _ (_ ∷ [])) = linearCommit
commitShape (commitNode _ (_ ∷ _ ∷ _)) = mergeCommit

record BranchRef : Set where
  constructor branchRef
  field
    branchName : String
    branchTip : String

open BranchRef public

record HistoryGraph : Set where
  constructor historyGraph
  field
    historyCommits : List CommitNode
    historyRefs : List BranchRef

open HistoryGraph public

------------------------------------------------------------------------
-- Explicit evidence for a fork and a later merge.
------------------------------------------------------------------------

record ForkWitness : Set where
  constructor forkWitness
  field
    forkBase : CommitNode
    forkLeft : CommitNode
    forkRight : CommitNode

    leftLeavesBase :
      commitId forkBase ∈ commitParents forkLeft

    rightLeavesBase :
      commitId forkBase ∈ commitParents forkRight

open ForkWitness public

record MergeWitness : Set where
  constructor mergeWitness
  field
    mergeLeft : CommitNode
    mergeRight : CommitNode
    mergeResult : CommitNode

    leftEntersMerge :
      commitId mergeLeft ∈ commitParents mergeResult

    rightEntersMerge :
      commitId mergeRight ∈ commitParents mergeResult

open MergeWitness public

------------------------------------------------------------------------
-- Parent-evidenced paths.  These are the formal counterpart of the concrete
-- fork-to-tip commit paths serialized by the Python history extractor.
------------------------------------------------------------------------

data ParentPath : CommitNode → CommitNode → Set where
  pathRoot :
    ∀ commit →
    ParentPath commit commit

  pathStep :
    ∀ {base parent child} →
    commitId parent ∈ commitParents child →
    ParentPath base parent →
    ParentPath base child

record BranchMergeEpisode : Set where
  constructor branchMergeEpisode
  field
    fork : ForkWitness
    merge : MergeWitness

    leftBranchPath :
      ParentPath
        (forkBase fork)
        (mergeLeft merge)

    rightBranchPath :
      ParentPath
        (forkBase fork)
        (mergeRight merge)

open BranchMergeEpisode public

------------------------------------------------------------------------
-- Generic history provider.  The materialization multiplicity is deliberate:
-- ordinary Git usually exposes one checkout view per commit, while a
-- coexistence-first system can expose several workspace/build/candidate views.
------------------------------------------------------------------------

record VersionedStateProvider : Set₁ where
  field
    VersionState : Set
    MaterializedView : Set
    parentStates : VersionState → List VersionState
    materializations : VersionState → List MaterializedView

record SemanticMaterializer
  (provider : VersionedStateProvider) : Set₁ where
  open VersionedStateProvider provider
  field
    extractSemanticGraph : MaterializedView → SemanticGraph

open VersionedStateProvider public
open SemanticMaterializer public

------------------------------------------------------------------------
-- History events compile to a small renderer-neutral lane vocabulary.
------------------------------------------------------------------------

data HistoryEvent : Set where
  commitObserved : CommitNode → HistoryEvent
  forkObserved : ForkWitness → HistoryEvent
  mergeObserved : MergeWitness → HistoryEvent
  refObserved : BranchRef → HistoryEvent

data HistoryIntent : Set where
  commitPointAppears : HistoryIntent
  branchLaneSplits : HistoryIntent
  branchLanesJoin : HistoryIntent
  branchTipGetsLabel : HistoryIntent

historyIntent : HistoryEvent → HistoryIntent
historyIntent (commitObserved _) = commitPointAppears
historyIntent (forkObserved _) = branchLaneSplits
historyIntent (mergeObserved _) = branchLanesJoin
historyIntent (refObserved _) = branchTipGetsLabel

data HistoryVisualPrimitive : Set where
  drawCommitPoint : CommitNode → HistoryVisualPrimitive
  splitHistoryLane : ForkWitness → HistoryVisualPrimitive
  joinHistoryLanes : MergeWitness → HistoryVisualPrimitive
  labelHistoryTip : BranchRef → HistoryVisualPrimitive

historyPrimitiveIntent : HistoryVisualPrimitive → HistoryIntent
historyPrimitiveIntent (drawCommitPoint _) = commitPointAppears
historyPrimitiveIntent (splitHistoryLane _) = branchLaneSplits
historyPrimitiveIntent (joinHistoryLanes _) = branchLanesJoin
historyPrimitiveIntent (labelHistoryTip _) = branchTipGetsLabel

compileHistoryEvent : HistoryEvent → HistoryVisualPrimitive
compileHistoryEvent (commitObserved commit) = drawCommitPoint commit
compileHistoryEvent (forkObserved forkWitnessValue) =
  splitHistoryLane forkWitnessValue
compileHistoryEvent (mergeObserved mergeWitnessValue) =
  joinHistoryLanes mergeWitnessValue
compileHistoryEvent (refObserved ref) = labelHistoryTip ref

compileHistoryIntentExact :
  ∀ event →
  historyPrimitiveIntent (compileHistoryEvent event) ≡ historyIntent event
compileHistoryIntentExact (commitObserved _) = refl
compileHistoryIntentExact (forkObserved _) = refl
compileHistoryIntentExact (mergeObserved _) = refl
compileHistoryIntentExact (refObserved _) = refl

------------------------------------------------------------------------
-- Canonical fork/merge specimen.
------------------------------------------------------------------------

canonicalRoot : CommitNode
canonicalRoot = commitNode "root" []

canonicalLeft : CommitNode
canonicalLeft = commitNode "feature-a" ("root" ∷ [])

canonicalRight : CommitNode
canonicalRight = commitNode "feature-b" ("root" ∷ [])

canonicalMerge : CommitNode
canonicalMerge =
  commitNode "merge" ("feature-a" ∷ "feature-b" ∷ [])

canonicalRootShape :
  commitShape canonicalRoot ≡ rootCommit
canonicalRootShape = refl

canonicalLeftShape :
  commitShape canonicalLeft ≡ linearCommit
canonicalLeftShape = refl

canonicalMergeShape :
  commitShape canonicalMerge ≡ mergeCommit
canonicalMergeShape = refl

canonicalForkWitness : ForkWitness
canonicalForkWitness =
  forkWitness
    canonicalRoot
    canonicalLeft
    canonicalRight
    here
    here

canonicalMergeWitness : MergeWitness
canonicalMergeWitness =
  mergeWitness
    canonicalLeft
    canonicalRight
    canonicalMerge
    here
    (there here)

canonicalLeftPath :
  ParentPath canonicalRoot canonicalLeft
canonicalLeftPath =
  pathStep here (pathRoot canonicalRoot)

canonicalRightPath :
  ParentPath canonicalRoot canonicalRight
canonicalRightPath =
  pathStep here (pathRoot canonicalRoot)

canonicalBranchMergeEpisode : BranchMergeEpisode
canonicalBranchMergeEpisode =
  branchMergeEpisode
    canonicalForkWitness
    canonicalMergeWitness
    canonicalLeftPath
    canonicalRightPath
