module DASHI.Core.QueryIndexedProjectionSpineAdapterExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Indexed
import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.FactorisationSpineCrosswalkExact as Crosswalk

------------------------------------------------------------------------
-- QUERY-INDEXED ADEQUACY -> CANONICAL PROJECTION/COLLISION SPINE
--
-- QueryIndexedProjectionAdequacyExact already reuses the repository's
-- NonFactorabilityWitness carrier.  This adapter exposes that existing witness
-- directly through the canonical ProjectionCollision / repair surface used by
-- the repo-wide consolidation programme.
--
-- The query index is retained at the type boundary: the consumer is exactly
-- `answer semantics query`.  No intrinsic observer adequacy Boolean and no new
-- observer-geometry ontology are introduced here.
------------------------------------------------------------------------

queryAdequacyDefectToProjectionCollision :
  ∀ {State Observation Query Answer : Set}
    {project : State → Observation}
    {semantics : Indexed.QuerySemantics State Query Answer}
    {query : Query} →
  Indexed.QueryAdequacyDefect project semantics query →
  Coarse.ProjectionCollision project (Indexed.answer semantics query)
queryAdequacyDefectToProjectionCollision =
  Crosswalk.nonFactorabilityToProjectionCollision

projectionCollisionToQueryAdequacyDefect :
  ∀ {State Observation Query Answer : Set}
    {project : State → Observation}
    {semantics : Indexed.QuerySemantics State Query Answer}
    {query : Query} →
  Coarse.ProjectionCollision project (Indexed.answer semantics query) →
  Indexed.QueryAdequacyDefect project semantics query
projectionCollisionToQueryAdequacyDefect =
  Crosswalk.projectionCollisionToNonFactorability

queryAdequacyDefectRepairRequiresSeparation :
  ∀ {State Observation Query Answer Refinement : Set}
    {project : State → Observation}
    {semantics : Indexed.QuerySemantics State Query Answer}
    {query : Query}
    {refine : State → Refinement} →
  (defect : Indexed.QueryAdequacyDefect project semantics query) →
  Repair.RefinementRepairs project refine (Indexed.answer semantics query) →
  refine
      (Coarse.left (queryAdequacyDefectToProjectionCollision defect))
    ≡ refine
      (Coarse.right (queryAdequacyDefectToProjectionCollision defect)) →
  ⊥
queryAdequacyDefectRepairRequiresSeparation defect =
  Crosswalk.projectionCollisionRepairRequiresSeparation
    (queryAdequacyDefectToProjectionCollision defect)

------------------------------------------------------------------------
-- Boundary: observer identity/axis/protocol can be a retained coordinate for a
-- particular consumer without becoming a complete-state reconstruction claim.
------------------------------------------------------------------------

record QueryIndexedProjectionSpineBoundary : Set where
  constructor query-indexed-projection-spine-boundary
  field
    queryIndexRetained : Bool
    queryIndexRetainedIsTrue : queryIndexRetained ≡ true

    queryDefectUsesCanonicalCollisionSpine : Bool
    queryDefectUsesCanonicalCollisionSpineIsTrue :
      queryDefectUsesCanonicalCollisionSpine ≡ true

    sufficientRepairMustSeparateWitness : Bool
    sufficientRepairMustSeparateWitnessIsTrue :
      sufficientRepairMustSeparateWitness ≡ true

    oneQueryAdequacyImpliesAllQueries : Bool
    oneQueryAdequacyImpliesAllQueriesIsFalse :
      oneQueryAdequacyImpliesAllQueries ≡ false

    retainedObserverCoordinateImpliesCompleteStateReconstruction : Bool
    retainedObserverCoordinateImpliesCompleteStateReconstructionIsFalse :
      retainedObserverCoordinateImpliesCompleteStateReconstruction ≡ false

canonicalQueryIndexedProjectionSpineBoundary :
  QueryIndexedProjectionSpineBoundary
canonicalQueryIndexedProjectionSpineBoundary =
  query-indexed-projection-spine-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
