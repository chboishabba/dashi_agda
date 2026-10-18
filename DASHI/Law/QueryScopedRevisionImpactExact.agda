module DASHI.Law.QueryScopedRevisionImpactExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- S15 × S18: query-relative revision impact.
--
-- A world may change outside the dependency slice of Q without changing Q's
-- projection or answer.  A change to a coordinate inside the slice is visible
-- to Q.  This is the finite exact core behind:
--
--   RevisionChangedConsumerInvariant
--   RevisionChangedConsumerResidual
------------------------------------------------------------------------

data ARevision : Set where
  a₀ a₁ : ARevision

data BRevision : Set where
  b₀ b₁ : BRevision

record World : Set where
  constructor world
  field
    aRevision : ARevision
    bRevision : BRevision

open World public

data AQuery : Set where
  askA : AQuery

queryProject : World → ARevision
queryProject = aRevision

queryAnswer : AQuery → World → ARevision
queryAnswer askA w = aRevision w

querySemantics :
  Query.QuerySemantics World AQuery ARevision
querySemantics =
  Query.querySemantics queryAnswer

queryProjectAdequate :
  Query.AdequateFor queryProject querySemantics askA
queryProjectAdequate =
  Query.factorsForQuery
    (λ observedA → observedA)
    (λ w → refl)

oldWorld : World
oldWorld = world a₀ b₀

irrelevantRevisionWorld : World
irrelevantRevisionWorld = world a₀ b₁

relevantRevisionWorld : World
relevantRevisionWorld = world a₁ b₀

irrelevantRevisionPreservesQueryProjection :
  queryProject oldWorld ≡ queryProject irrelevantRevisionWorld
irrelevantRevisionPreservesQueryProjection = refl

irrelevantRevisionPreservesQueryAnswer :
  queryAnswer askA oldWorld ≡
  queryAnswer askA irrelevantRevisionWorld
irrelevantRevisionPreservesQueryAnswer = refl

a₀≠a₁ : a₀ ≡ a₁ → ⊥
a₀≠a₁ ()

relevantRevisionChangesQueryProjection :
  queryProject oldWorld ≡ queryProject relevantRevisionWorld → ⊥
relevantRevisionChangesQueryProjection =
  a₀≠a₁

relevantRevisionChangesQueryAnswer :
  queryAnswer askA oldWorld ≡
  queryAnswer askA relevantRevisionWorld → ⊥
relevantRevisionChangesQueryAnswer =
  a₀≠a₁

data QueryRevisionImpactKind : Set where
  noWorldRevisionChange : QueryRevisionImpactKind
  revisionChangedConsumerInvariant : QueryRevisionImpactKind
  revisionChangedConsumerResidual : QueryRevisionImpactKind

classifyIrrelevantRevision :
  QueryRevisionImpactKind
classifyIrrelevantRevision =
  revisionChangedConsumerInvariant

classifyRelevantRevision :
  QueryRevisionImpactKind
classifyRelevantRevision =
  revisionChangedConsumerResidual

record QueryScopedRevisionImpactBoundary : Set where
  constructor queryScopedRevisionImpactBoundary
  field
    worldChangeOutsideQuerySliceMayPreserveProjection : Bool
    worldChangeOutsideQuerySliceMayPreserveProjectionIsTrue :
      worldChangeOutsideQuerySliceMayPreserveProjection ≡ true

    worldChangeOutsideQuerySliceReopensConsumerResearch : Bool
    worldChangeOutsideQuerySliceReopensConsumerResearchIsFalse :
      worldChangeOutsideQuerySliceReopensConsumerResearch ≡ false

    worldChangeInsideQuerySliceMayChangeProjection : Bool
    worldChangeInsideQuerySliceMayChangeProjectionIsTrue :
      worldChangeInsideQuerySliceMayChangeProjection ≡ true

    worldChangeInsideQuerySliceMayReopenConsumerResearch : Bool
    worldChangeInsideQuerySliceMayReopenConsumerResearchIsTrue :
      worldChangeInsideQuerySliceMayReopenConsumerResearch ≡ true

    queryScopedImpactCreatesSemanticAuthority : Bool
    queryScopedImpactCreatesSemanticAuthorityIsFalse :
      queryScopedImpactCreatesSemanticAuthority ≡ false

    queryScopedImpactCreatesClaimTruth : Bool
    queryScopedImpactCreatesClaimTruthIsFalse :
      queryScopedImpactCreatesClaimTruth ≡ false

open QueryScopedRevisionImpactBoundary public

canonicalQueryScopedRevisionImpactBoundary :
  QueryScopedRevisionImpactBoundary
canonicalQueryScopedRevisionImpactBoundary =
  queryScopedRevisionImpactBoundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
