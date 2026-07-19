module DASHI.Core.L1Separation where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Core.NonlinearExplodedSparsity

------------------------------------------------------------------------
-- Abstract ordered objective and l1-style proximal solver
------------------------------------------------------------------------

record OrderedScalar (R : Set) : Set₁ where
  field
    _≤R_ : R → R → Set
    reflexiveR : (r : R) → r ≤R r
    transitiveR : {a b c : R} → a ≤R b → b ≤R c → a ≤R c

record L1Objective (X R : Set) : Set₁ where
  field
    order : OrderedScalar R
    dataTerm : State X → R
    normOne : State X → R
    lambda : R
    combine : R → R → R

    objective : State X → R
    objectiveExact : (s : State X) →
      objective s ≡ combine (dataTerm s) (normOne s)

------------------------------------------------------------------------
-- Coordinate-separable proximal maps
------------------------------------------------------------------------

record SeparableProximal
  {X R L : Set}
  (J : L1Objective X R)
  (K : ThresholdKernel X L) : Set₁ where
  field
    proxAtom : Trit → Trit
    solvesCoordinatewise : (s : State X) (x : X) →
      applyKernel K s x ≡ proxAtom (s x)

open SeparableProximal public

separableProximal→CoordinateRepresentation :
  {X R L : Set}
  {J : L1Objective X R}
  {K : ThresholdKernel X L} →
  SeparableProximal J K → CoordinateRepresentation K
separableProximal→CoordinateRepresentation P = record
  { coordinateRule = proxAtom P
  ; represents = solvesCoordinatewise P
  }

nonCoordinateKernelHasNoSeparableL1Proximal :
  {X R L : Set}
  {J : L1Objective X R}
  {K : ThresholdKernel X L} →
  NonCoordinateWitness K → ¬ SeparableProximal J K
nonCoordinateKernelHasNoSeparableL1Proximal witness proximal =
  nonCoordinateWitnessRulesOutCoordinateRepresentation witness
    (separableProximal→CoordinateRepresentation proximal)

------------------------------------------------------------------------
-- ReLU/scalar threshold rules are the same coordinate-only boundary
------------------------------------------------------------------------

record ScalarThresholdRepresentation
  {X L : Set}
  (K : ThresholdKernel X L) : Set₁ where
  field
    threshold : Trit → Trit
    pointwiseExact : (s : State X) (x : X) →
      applyKernel K s x ≡ threshold (s x)

scalarThreshold→CoordinateRepresentation :
  {X L : Set} {K : ThresholdKernel X L} →
  ScalarThresholdRepresentation K → CoordinateRepresentation K
scalarThreshold→CoordinateRepresentation T = record
  { coordinateRule = ScalarThresholdRepresentation.threshold T
  ; represents = ScalarThresholdRepresentation.pointwiseExact T
  }

nonCoordinateKernelHasNoScalarThreshold :
  {X L : Set} {K : ThresholdKernel X L} →
  NonCoordinateWitness K → ¬ ScalarThresholdRepresentation K
nonCoordinateKernelHasNoScalarThreshold witness threshold =
  nonCoordinateWitnessRulesOutCoordinateRepresentation witness
    (scalarThreshold→CoordinateRepresentation threshold)

-- The theorem excludes separable/coordinate l1 proximal maps.  It does not
-- exclude graph-coupled convex objectives whose proximal operator itself uses
-- adjacency; those require a different comparison theorem.
