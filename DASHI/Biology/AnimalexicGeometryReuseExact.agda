module DASHI.Biology.AnimalexicGeometryReuseExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AnimalexicFormalSystemExact as Animal
import DASHI.Core.QuantitativeNonlinearSparsity as Sparse
import DASHI.Core.FiniteWeightedThresholdGraph as Weighted
import DASHI.Core.ThresholdKernelRenormalisation as Renorm
import DASHI.Core.NonlinearExplodedSparsity as Nonlinear
import DASHI.Core.ExplodedGraphGeometry as Graph

------------------------------------------------------------------------
-- 1. Animalexic's application-supplied defect-localisation statement has an
--    immediate exact counting consequence.  This does NOT manufacture the
--    premise that real runtime defects are low-margin; that remains empirical.
------------------------------------------------------------------------

animalDefectCount≤LowMarginCount :
  ∀ {Candidate : Set}
    {Defect LowMargin : Candidate → Set} →
  (counting : Sparse.FiniteCounting Candidate) →
  Animal.DefectLocalizedToLowMargin Defect LowMargin →
  Sparse.count counting Defect ≤ Sparse.count counting LowMargin
animalDefectCount≤LowMarginCount counting localized =
  Sparse.monotone counting (Animal.confined localized)

animalSparseLowMarginImpliesSparseDefect :
  ∀ {Candidate : Set}
    {Defect LowMargin : Candidate → Set}
    {budget : Nat} →
  (counting : Sparse.FiniteCounting Candidate) →
  Animal.DefectLocalizedToLowMargin Defect LowMargin →
  Sparse.SparseAtMost counting LowMargin budget →
  Sparse.SparseAtMost counting Defect budget
animalSparseLowMarginImpliesSparseDefect counting localized lowSparse =
  record
    { bounded =
        ≤-trans
          (animalDefectCount≤LowMarginCount counting localized)
          (Sparse.bounded lowSparse)
    }

------------------------------------------------------------------------
-- 2. The runtime weighted-support implementation can be required to match the
--    already-existing abstract weighted threshold graph exactly.
------------------------------------------------------------------------

AnimalWeightedGraph : Set → Set → Set₁
AnimalWeightedGraph = Weighted.FiniteWeightedGraph

AnimalGraphGeometry : Set → Set₁
AnimalGraphGeometry = Graph.GraphGeometry

record AnimalWeightedKernelContract
    {Node Scalar : Set}
    (graph : Weighted.FiniteWeightedGraph Node Scalar)
    (deadzone : Weighted.GraphDeadzone graph) : Set₁ where
  constructor animalWeightedKernelContract
  field
    implementation : Weighted.GraphKernelImplementation graph deadzone

open AnimalWeightedKernelContract public

implementedAnimalKernelClosedIffAbstractClosed :
  ∀ {Node Scalar}
    {graph : Weighted.FiniteWeightedGraph Node Scalar}
    {deadzone : Weighted.GraphDeadzone graph} →
  (contract : AnimalWeightedKernelContract graph deadzone) →
  (state : Nonlinear.State Node) →
  ((node : Node) →
    Weighted.GraphKernelImplementation.implemented
      (implementation contract) state node ≡ state node) →
  Nonlinear.KernelClosed (Weighted.graphThresholdKernel graph deadzone) state
implementedAnimalKernelClosedIffAbstractClosed contract state closed =
  Weighted.implementedClosedImpliesAbstractClosed
    (implementation contract) state closed

------------------------------------------------------------------------
-- 3. Locality preservation and operator commutation remain separate proof
--    obligations.  A geometry implementation must not infer one from the other.
------------------------------------------------------------------------

record AnimalCoarseningAuditBoundary : Set where
  constructor animalCoarseningAuditBoundary
  field
    boundedGridAdjacencyMustNotWrap : Bool
    spatialHashMembershipMustTrackAnchorCell : Bool
    localityPreservationDoesNotProveKernelCommutation : Bool
    coarseningDefectNeedsConsumerOrOperatorWitness : Bool
    marginLiteratureDoesNotSupplyRuntimeDefectConfinement : Bool

open AnimalCoarseningAuditBoundary public

canonicalAnimalCoarseningAuditBoundary : AnimalCoarseningAuditBoundary
canonicalAnimalCoarseningAuditBoundary =
  animalCoarseningAuditBoundary true true true true true
