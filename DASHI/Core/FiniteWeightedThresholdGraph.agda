module DASHI.Core.FiniteWeightedThresholdGraph where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Core.NonlinearExplodedSparsity
open import Data.List using (map; foldr)

------------------------------------------------------------------------
-- Scalar and finite weighted graph data
------------------------------------------------------------------------

record ScalarStructure (R : Set) : Set₁ where
  field
    zeroR : R
    _+R_  : R → R → R
    _-R_  : R → R → R
    _*R_  : R → R → R

open ScalarStructure public

record FiniteWeightedGraph (X R : Set) : Set₁ where
  field
    nodes      : List X
    scalar     : ScalarStructure R
    adjacency  : X → X → R
    baseline   : X → X → R
    embedTrit  : Trit → R

open FiniteWeightedGraph public

------------------------------------------------------------------------
-- Concrete degree-corrected residual
------------------------------------------------------------------------

edgeResidual :
  {X R : Set} → FiniteWeightedGraph X R → State X → X → X → R
edgeResidual G s x y =
  let S = scalar G in
  _*R_ S
    (_-R_ S (adjacency G x y) (baseline G x y))
    (embedTrit G (s y))

localResidual :
  {X R : Set} → FiniteWeightedGraph X R → State X → X → R
localResidual G s x =
  foldr (_+R_ (scalar G)) (zeroR (scalar G))
    (map (edgeResidual G s x) (nodes G))

------------------------------------------------------------------------
-- Deadzone classifier and graph-kernel instance
------------------------------------------------------------------------

record GraphDeadzone
  {X R : Set}
  (G : FiniteWeightedGraph X R) : Set₁ where
  field
    residualPartition : TritPartition R

open GraphDeadzone public

graphThresholdKernel :
  {X R : Set} (G : FiniteWeightedGraph X R) →
  GraphDeadzone G → ThresholdKernel X R
graphThresholdKernel G D = record
  { localField = localResidual G
  ; partition = residualPartition D
  }

graphKernel :
  {X R : Set} (G : FiniteWeightedGraph X R) →
  GraphDeadzone G → State X → State X
graphKernel G D = applyKernel (graphThresholdKernel G D)

graphKernelComputesResidual :
  {X R : Set} (G : FiniteWeightedGraph X R) (D : GraphDeadzone G) →
  (s : State X) (x : X) →
  graphKernel G D s x ≡
  TritPartition.classify (residualPartition D) (localResidual G s x)
graphKernelComputesResidual G D s x = refl

graphKernelClosedIffThresholdCSP :
  {X R : Set} (G : FiniteWeightedGraph X R) (D : GraphDeadzone G) →
  (s : State X) →
  KernelClosed (graphThresholdKernel G D) s ↔
  SatisfiesAllLocalConstraints (graphThresholdKernel G D) s
graphKernelClosedIffThresholdCSP G D s =
  kernelClosureIffCSP (graphThresholdKernel G D) s

------------------------------------------------------------------------
-- Implementation correspondence boundary
------------------------------------------------------------------------

record GraphKernelImplementation
  {X R : Set}
  (G : FiniteWeightedGraph X R)
  (D : GraphDeadzone G) : Set₁ where
  field
    implemented : State X → State X
    exact : (s : State X) (x : X) →
      implemented s x ≡ graphKernel G D s x

open GraphKernelImplementation public

implementedClosedImpliesAbstractClosed :
  {X R : Set} {G : FiniteWeightedGraph X R} {D : GraphDeadzone G} →
  (I : GraphKernelImplementation G D) (s : State X) →
  ((x : X) → implemented I s x ≡ s x) →
  KernelClosed (graphThresholdKernel G D) s
implementedClosedImpliesAbstractClosed I s closed x =
  trans (sym (exact I s x)) (closed x)

abstractClosedImpliesImplementedClosed :
  {X R : Set} {G : FiniteWeightedGraph X R} {D : GraphDeadzone G} →
  (I : GraphKernelImplementation G D) (s : State X) →
  KernelClosed (graphThresholdKernel G D) s →
  (x : X) → implemented I s x ≡ s x
abstractClosedImpliesImplementedClosed I s closed x =
  trans (exact I s x) (closed x)
