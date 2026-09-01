module DASHI.Reasoning.AristotleBranchMergeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

------------------------------------------------------------------------
-- ARISTOTLE BRANCH MERGE CALCULUS
--
-- Cross-pollination boundary:
--
-- Aristotle's paper owns the MCGS AND/OR search hypergraph, observer fibres,
-- quotient-sound proof reuse, and monotone proved-lemma feedback.  The merge
-- strategies below are DASHI constructions layered on that substrate.  They
-- are not attributed to the Harmonic Team paper.
--
-- The central distinction is:
--
--   union of discoveries
--   != proof-valid merge
--   != dependency-compatible merge
--   != provenance-preserving merge.
------------------------------------------------------------------------

data MergeStrategy : Set where
  fastForward
  threeWay
  monotoneKnowledgeJoin
  guardedReconcile
  : MergeStrategy

------------------------------------------------------------------------
-- Monotone branch-local proved knowledge.
------------------------------------------------------------------------

record Knowledge (Item : Set) : Set₁ where
  constructor knowledge
  field
    Knows : Item → Set

open Knowledge public

joinKnowledge : ∀ {Item : Set} → Knowledge Item → Knowledge Item → Knowledge Item
joinKnowledge left right =
  knowledge (λ item → Knows left item ⊎ Knows right item)

KnowledgeExtension : ∀ {Item : Set} → Knowledge Item → Knowledge Item → Set
KnowledgeExtension old new = ∀ item → Knows old item → Knows new item

leftKnowledgeSurvivesJoin :
  ∀ {Item : Set} (left right : Knowledge Item) →
  KnowledgeExtension left (joinKnowledge left right)
leftKnowledgeSurvivesJoin left right item proof = inj₁ proof

rightKnowledgeSurvivesJoin :
  ∀ {Item : Set} (left right : Knowledge Item) →
  KnowledgeExtension right (joinKnowledge left right)
rightKnowledgeSurvivesJoin left right item proof = inj₂ proof

joinKnowledgeCommutativePointwise :
  ∀ {Item : Set} (left right : Knowledge Item) (item : Item) →
  Knows (joinKnowledge left right) item →
  Knows (joinKnowledge right left) item
joinKnowledgeCommutativePointwise left right item (inj₁ proof) = inj₂ proof
joinKnowledgeCommutativePointwise left right item (inj₂ proof) = inj₁ proof

joinKnowledgeIdempotentPointwise :
  ∀ {Item : Set} (branch : Knowledge Item) (item : Item) →
  Knows (joinKnowledge branch branch) item →
  Knows branch item
joinKnowledgeIdempotentPointwise branch item (inj₁ proof) = proof
joinKnowledgeIdempotentPointwise branch item (inj₂ proof) = proof

------------------------------------------------------------------------
-- A branch snapshot keeps visible state separate from hidden dependency and
-- provenance coordinates.  This is the minimum information needed to stop
-- observer equality from silently becoming merge authority.
------------------------------------------------------------------------

record BranchSnapshot
    (Visible Dependency Provenance Item : Set) : Set₁ where
  constructor branchSnapshot
  field
    visible : Visible
    dependency : Dependency
    provenance : Provenance
    provedKnowledge : Knowledge Item
    branchReference : String

open BranchSnapshot public

record BranchExtension
    {Visible Dependency Provenance Item : Set}
    (old new : BranchSnapshot Visible Dependency Provenance Item) : Set₁ where
  constructor branchExtension
  field
    sameVisible : visible old ≡ visible new
    sameDependency : dependency old ≡ dependency new
    sameProvenance : provenance old ≡ provenance new
    preservesKnowledge :
      KnowledgeExtension (provedKnowledge old) (provedKnowledge new)

open BranchExtension public

-- Fast-forward is the special case in which one branch already extends the
-- other without changing the guarded coordinates.
fastForwardMerge :
  ∀ {Visible Dependency Provenance Item : Set}
    {old new : BranchSnapshot Visible Dependency Provenance Item} →
  BranchExtension old new →
  BranchSnapshot Visible Dependency Provenance Item
fastForwardMerge {new = new} extension = new

------------------------------------------------------------------------
-- Guarded reconciliation.
------------------------------------------------------------------------

record MergeGuard
    {Visible Dependency Provenance Item : Set}
    (left right : BranchSnapshot Visible Dependency Provenance Item) : Set where
  constructor mergeGuard
  field
    visibleCompatible : visible left ≡ visible right
    dependencyCompatible : dependency left ≡ dependency right
    provenanceCompatible : provenance left ≡ provenance right

open MergeGuard public

guardedMerge :
  ∀ {Visible Dependency Provenance Item : Set}
    {left right : BranchSnapshot Visible Dependency Provenance Item} →
  MergeGuard left right →
  BranchSnapshot Visible Dependency Provenance Item
guardedMerge {left = left} {right = right} guard =
  branchSnapshot
    (visible left)
    (dependency left)
    (provenance left)
    (joinKnowledge (provedKnowledge left) (provedKnowledge right))
    "guarded Aristotle branch reconciliation: visible/dependency/provenance compatible; proved knowledge joined monotonically"

leftKnowledgeSurvivesGuardedMerge :
  ∀ {Visible Dependency Provenance Item : Set}
    {left right : BranchSnapshot Visible Dependency Provenance Item}
    (guard : MergeGuard left right) →
  KnowledgeExtension
    (provedKnowledge left)
    (provedKnowledge (guardedMerge guard))
leftKnowledgeSurvivesGuardedMerge {left = left} {right = right} guard =
  leftKnowledgeSurvivesJoin (provedKnowledge left) (provedKnowledge right)

rightKnowledgeSurvivesGuardedMerge :
  ∀ {Visible Dependency Provenance Item : Set}
    {left right : BranchSnapshot Visible Dependency Provenance Item}
    (guard : MergeGuard left right) →
  KnowledgeExtension
    (provedKnowledge right)
    (provedKnowledge (guardedMerge guard))
rightKnowledgeSurvivesGuardedMerge {left = left} {right = right} guard =
  rightKnowledgeSurvivesJoin (provedKnowledge left) (provedKnowledge right)

------------------------------------------------------------------------
-- Three-way reconciliation requires an explicit common ancestor and branch
-- extension receipts before the sibling merge guard is even considered.
------------------------------------------------------------------------

record ThreeWayMergeReceipt
    {Visible Dependency Provenance Item : Set}
    (base left right : BranchSnapshot Visible Dependency Provenance Item) : Set₁ where
  constructor threeWayMergeReceipt
  field
    leftExtendsBase : BranchExtension base left
    rightExtendsBase : BranchExtension base right
    siblingGuard : MergeGuard left right

open ThreeWayMergeReceipt public

threeWayMergeResult :
  ∀ {Visible Dependency Provenance Item : Set}
    {base left right : BranchSnapshot Visible Dependency Provenance Item} →
  ThreeWayMergeReceipt base left right →
  BranchSnapshot Visible Dependency Provenance Item
threeWayMergeResult receipt = guardedMerge (siblingGuard receipt)

------------------------------------------------------------------------
-- Aristotle feedback bridge.
--
-- The paper-level `FeedbackRefinement` remains the authority for monotonicity
-- across formal-feedback iterations.  This lemma simply re-exports that exact
-- fact in the merge lane: branch reconciliation may preserve proved knowledge,
-- but it does not replace Aristotle's refinement witness.
------------------------------------------------------------------------

aristotleFeedbackStillMonotone :
  ∀ {old new : Aristotle.LemmaLedger}
    (refinement : Aristotle.FeedbackRefinement old new)
    (lemma : Aristotle.LemmaId old) →
  Aristotle.ProvedIn old lemma →
  Aristotle.ProvedIn new (Aristotle.castId refinement lemma)
aristotleFeedbackStillMonotone = Aristotle.provedKnowledgeMonotone

------------------------------------------------------------------------
-- Finite regressions: same observer surface is not enough for merge.
------------------------------------------------------------------------

data Surface : Set where
  sameGoalSurface : Surface

data DependencyCode : Set where
  localDependency globalSensitiveDependency : DependencyCode

data ProvenanceCode : Set where
  inheritedHistory introducedHistory : ProvenanceCode

data Lemma : Set where
  lemmaA lemmaB : Lemma

knowledgeA : Knowledge Lemma
knowledgeA = knowledge λ
  { lemmaA → ⊤
  ; lemmaB → ⊥
  }

knowledgeB : Knowledge Lemma
knowledgeB = knowledge λ
  { lemmaA → ⊥
  ; lemmaB → ⊤
  }

leftBranch : BranchSnapshot Surface DependencyCode ProvenanceCode Lemma
leftBranch =
  branchSnapshot sameGoalSurface localDependency inheritedHistory knowledgeA
    "left branch"

compatibleRightBranch : BranchSnapshot Surface DependencyCode ProvenanceCode Lemma
compatibleRightBranch =
  branchSnapshot sameGoalSurface localDependency inheritedHistory knowledgeB
    "compatible right branch"

hiddenDependencyBranch : BranchSnapshot Surface DependencyCode ProvenanceCode Lemma
hiddenDependencyBranch =
  branchSnapshot sameGoalSurface globalSensitiveDependency inheritedHistory knowledgeB
    "same visible state, different hidden dependency"

reintroducedProvenanceBranch : BranchSnapshot Surface DependencyCode ProvenanceCode Lemma
reintroducedProvenanceBranch =
  branchSnapshot sameGoalSurface localDependency introducedHistory knowledgeB
    "same visible state, different provenance lineage"

sameVisibleCompatibleBranches :
  visible leftBranch ≡ visible compatibleRightBranch
sameVisibleCompatibleBranches = refl

sameVisibleHiddenDependencyBranches :
  visible leftBranch ≡ visible hiddenDependencyBranch
sameVisibleHiddenDependencyBranches = refl

sameVisibleDifferentProvenanceBranches :
  visible leftBranch ≡ visible reintroducedProvenanceBranch
sameVisibleDifferentProvenanceBranches = refl

localIsNotGlobalSensitive :
  localDependency ≡ globalSensitiveDependency → ⊥
localIsNotGlobalSensitive ()

inheritedIsNotIntroduced :
  inheritedHistory ≡ introducedHistory → ⊥
inheritedIsNotIntroduced ()

sameObservedStateDoesNotDetermineDependency :
  dependency leftBranch ≡ dependency hiddenDependencyBranch → ⊥
sameObservedStateDoesNotDetermineDependency = localIsNotGlobalSensitive

sameObservedStateDoesNotDetermineProvenance :
  provenance leftBranch ≡ provenance reintroducedProvenanceBranch → ⊥
sameObservedStateDoesNotDetermineProvenance = inheritedIsNotIntroduced

sameObservedStateIsInsufficientForHiddenDependencyMerge :
  MergeGuard leftBranch hiddenDependencyBranch → ⊥
sameObservedStateIsInsufficientForHiddenDependencyMerge guard =
  localIsNotGlobalSensitive (dependencyCompatible guard)

sameObservedStateIsInsufficientForProvenanceMerge :
  MergeGuard leftBranch reintroducedProvenanceBranch → ⊥
sameObservedStateIsInsufficientForProvenanceMerge guard =
  inheritedIsNotIntroduced (provenanceCompatible guard)

canonicalCompatibleGuard : MergeGuard leftBranch compatibleRightBranch
canonicalCompatibleGuard = mergeGuard refl refl refl

mergedCompatibleBranches : BranchSnapshot Surface DependencyCode ProvenanceCode Lemma
mergedCompatibleBranches = guardedMerge canonicalCompatibleGuard

lemmaASurvivesCompatibleMerge :
  Knows (provedKnowledge mergedCompatibleBranches) lemmaA
lemmaASurvivesCompatibleMerge = inj₁ tt

lemmaBSurvivesCompatibleMerge :
  Knows (provedKnowledge mergedCompatibleBranches) lemmaB
lemmaBSurvivesCompatibleMerge = inj₂ tt

------------------------------------------------------------------------
-- Boundary / provenance.
------------------------------------------------------------------------

record AristotleBranchMergeBoundary : Set where
  constructor aristotleBranchMergeBoundary
  field
    sameObservedStateAutomaticallyMergeable : Bool
    sameObservedStateAutomaticallyMergeableIsFalse :
      sameObservedStateAutomaticallyMergeable ≡ false

    locallyValidBranchesAlwaysNaivelyUnion : Bool
    locallyValidBranchesAlwaysNaivelyUnionIsFalse :
      locallyValidBranchesAlwaysNaivelyUnion ≡ false

    compatibleProvedKnowledgeCanJoinMonotonically : Bool
    compatibleProvedKnowledgeCanJoinMonotonicallyIsTrue :
      compatibleProvedKnowledgeCanJoinMonotonically ≡ true

    threeWayMergeRequiresCommonAncestorReceipts : Bool
    threeWayMergeRequiresCommonAncestorReceiptsIsTrue :
      threeWayMergeRequiresCommonAncestorReceipts ≡ true

    mergeCalculusIsClaimedByAristotlePaper : Bool
    mergeCalculusIsClaimedByAristotlePaperIsFalse :
      mergeCalculusIsClaimedByAristotlePaper ≡ false

    reading : String

canonicalAristotleBranchMergeBoundary : AristotleBranchMergeBoundary
canonicalAristotleBranchMergeBoundary =
  aristotleBranchMergeBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    "DASHI branch merge layer over Aristotle MCGS: fast-forward, three-way ancestry, monotone knowledge join and guarded reconciliation are separated; observer equality alone never manufactures dependency or provenance compatibility."
