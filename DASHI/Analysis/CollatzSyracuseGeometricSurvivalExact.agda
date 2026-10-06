module DASHI.Analysis.CollatzSyracuseGeometricSurvivalExact where

------------------------------------------------------------------------
-- GEOMETRIC SURVIVAL COMPILER FOR THE SAME-OBJECT CYLINDER ROUTE
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.FiniteUniformBranchingHittingTailExact as Tail
import DASHI.Analysis.CollatzSyracuseUniformHittingBlockExact as Hitting

record SyracuseGeometricSurvivalSource : Set₁ where
  field
    hitting : Hitting.SyracuseFiniteHittingSource
    compiler : Tail.UniformBranchingTailCompiler
    exactBranchCountPaid : Set
    killedContinuationPaid : Set
    aggregateRecurrencePaid : Set

open SyracuseGeometricSurvivalSource public

genericSurvivorBound :
  (source : SyracuseGeometricSurvivalSource) →
  (q : Nat) →
  Tail.survivors (compiler source) q
  Tail.≤
  Tail.Decay.powNat
    (Tail.branchFactor (Tail.family (compiler source)) Tail.- 1) q
    Tail.* Tail.survivors (compiler source) 0
genericSurvivorBound source q =
  Tail.genericGeometricSurvivorBound (compiler source) q

record GeometricSurvivalBoundary : Set where
  constructor geometricSurvivalBoundary
  field
    spectralGapRequired : Nat
    killedContinuationRequired : Nat
    aggregateRecurrenceRequired : Nat
    universalIntegerStoppingAutomatic : Nat

canonicalGeometricSurvivalBoundary : GeometricSurvivalBoundary
canonicalGeometricSurvivalBoundary = geometricSurvivalBoundary 0 1 1 0
