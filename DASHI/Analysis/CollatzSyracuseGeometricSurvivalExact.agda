module DASHI.Analysis.CollatzSyracuseGeometricSurvivalExact where

------------------------------------------------------------------------
-- GEOMETRIC SURVIVAL COMPILER FOR THE SAME-OBJECT CYLINDER ROUTE
--
-- The generic numerical bound itself remains owned by
-- FiniteUniformBranchingHittingTailExact.  This module records exactly the
-- Syracuse-specific producers required before that theorem may be consumed.
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
    sampledStartTransportPaid : Set

open SyracuseGeometricSurvivalSource public

record GeometricSurvivalBoundary : Set where
  constructor geometricSurvivalBoundary
  field
    genericBoundAlreadyOwnedByRepo : Nat
    spectralGapRequired : Nat
    killedContinuationRequired : Nat
    aggregateRecurrenceRequired : Nat
    universalIntegerStoppingAutomatic : Nat

canonicalGeometricSurvivalBoundary : GeometricSurvivalBoundary
canonicalGeometricSurvivalBoundary = geometricSurvivalBoundary 1 0 1 1 0
