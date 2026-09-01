module DASHI.Core.BidiResidualEvidenceMergeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi

------------------------------------------------------------------------
-- BIDI RESIDUAL EVIDENCE MERGE
--
-- Merge means combining independently warranted constraints on the same hidden
-- carrier.  It is not blind union.  Conjunctive merge intersects admissible
-- fibres; fast-forward applies when one branch already refines the other.
------------------------------------------------------------------------

JointResidualFibre :
  ∀ {Hidden} →
  Bidi.ResidualFibre Hidden →
  Bidi.ResidualFibre Hidden →
  Bidi.ResidualFibre Hidden
JointResidualFibre left right hidden = left hidden × right hidden

jointRefinesLeft :
  ∀ {Hidden}
    (left right : Bidi.ResidualFibre Hidden) →
  Bidi.FibreRefines (JointResidualFibre left right) left
jointRefinesLeft left right hidden joint = proj₁ joint

jointRefinesRight :
  ∀ {Hidden}
    (left right : Bidi.ResidualFibre Hidden) →
  Bidi.FibreRefines (JointResidualFibre left right) right
jointRefinesRight left right hidden joint = proj₂ joint

------------------------------------------------------------------------
-- Fast-forward: if one branch is already stronger, no synthetic reconciliation
-- is needed to recover its information content.
------------------------------------------------------------------------

record FastForwardResidualMerge
    {Hidden : Set}
    (stronger weaker : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor fastForwardResidualMerge
  field
    alreadyRefines : Bidi.FibreRefines stronger weaker
    ancestryReference : String
    provenanceReference : String

open FastForwardResidualMerge public

fastForwardPreservesStronger :
  ∀ {Hidden}
    {stronger weaker : Bidi.ResidualFibre Hidden} →
  FastForwardResidualMerge stronger weaker →
  Bidi.FibreRefines stronger weaker
fastForwardPreservesStronger = alreadyRefines

------------------------------------------------------------------------
-- Three-way/conjunctive reconciliation.  The common ancestor is retained as an
-- explicit provenance coordinate; both descendants must independently refine it.
------------------------------------------------------------------------

record ThreeWayResidualMerge
    {Hidden : Set}
    (ancestor left right : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor threeWayResidualMerge
  field
    leftRefinesAncestor : Bidi.FibreRefines left ancestor
    rightRefinesAncestor : Bidi.FibreRefines right ancestor
    leftProvenanceReference : String
    rightProvenanceReference : String
    ancestorReference : String
    compatibilityReference : String

open ThreeWayResidualMerge public

threeWayJointRefinesAncestor :
  ∀ {Hidden}
    {ancestor left right : Bidi.ResidualFibre Hidden} →
  ThreeWayResidualMerge ancestor left right →
  Bidi.FibreRefines (JointResidualFibre left right) ancestor
threeWayJointRefinesAncestor merge hidden joint =
  leftRefinesAncestor merge hidden (proj₁ joint)

------------------------------------------------------------------------
-- Conflict is emptiness of the conjunctive fibre, not merely branch difference.
------------------------------------------------------------------------

ResidualConflict :
  ∀ {Hidden} →
  Bidi.ResidualFibre Hidden →
  Bidi.ResidualFibre Hidden → Set
ResidualConflict left right =
  (Σ _ λ hidden → JointResidualFibre left right hidden) → ⊥

record CompatibleResidualMerge
    {Hidden : Set}
    (left right : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor compatibleResidualMerge
  field
    witness : Σ Hidden λ hidden → JointResidualFibre left right hidden
    compatibilityReference : String
    provenanceReference : String

open CompatibleResidualMerge public

compatibleMergeIsNotConflict :
  ∀ {Hidden}
    {left right : Bidi.ResidualFibre Hidden} →
  CompatibleResidualMerge left right →
  ResidualConflict left right → ⊥
compatibleMergeIsNotConflict merge conflict = conflict (witness merge)

------------------------------------------------------------------------
-- Boundary: information merge is intersection/refinement, while monotone
-- knowledge ledgers may have separate join-like semantics.  Do not infer that
-- arbitrary proof states/actions form a CRDT merely from this construction.
------------------------------------------------------------------------

record BidiResidualEvidenceMergeBoundary : Set where
  constructor bidiResidualEvidenceMergeBoundary
  field
    independentConstraintMergeUsesBlindUnion : Bool
    independentConstraintMergeUsesBlindUnionIsFalse :
      independentConstraintMergeUsesBlindUnion ≡ false
    conjunctiveMergeRefinesBothParents : Bool
    conjunctiveMergeRefinesBothParentsIsTrue :
      conjunctiveMergeRefinesBothParents ≡ true
    fastForwardAvailableWhenOneBranchAlreadyRefinesOther : Bool
    fastForwardAvailableWhenOneBranchAlreadyRefinesOtherIsTrue :
      fastForwardAvailableWhenOneBranchAlreadyRefinesOther ≡ true
    branchDifferenceAloneMeansConflict : Bool
    branchDifferenceAloneMeansConflictIsFalse :
      branchDifferenceAloneMeansConflict ≡ false
    arbitraryProofSearchStateIsCRDTJoinable : Bool
    arbitraryProofSearchStateIsCRDTJoinableIsFalse :
      arbitraryProofSearchStateIsCRDTJoinable ≡ false

canonicalBidiResidualEvidenceMergeBoundary : BidiResidualEvidenceMergeBoundary
canonicalBidiResidualEvidenceMergeBoundary =
  bidiResidualEvidenceMergeBoundary
    false refl true refl true refl false refl false refl
