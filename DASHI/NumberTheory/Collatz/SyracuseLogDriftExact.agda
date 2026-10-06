module DASHI.NumberTheory.Collatz.SyracuseLogDriftExact where

------------------------------------------------------------------------
-- STOPPED LOG-DRIFT COMPILER
--
-- This module owns the same-object stopping geometry and the theorem shape.
-- The real-log inequalities remain explicit inputs from the analysis boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseLogDriftBoundaryExact as Boundary

record StoppingRegion : Set where
  constructor stoppingRegion
  field
    threshold : Nat

open StoppingRegion public

record BeforeStopping (region : StoppingRegion)
                      (m : Nat)
                      (x : Syracuse.PositiveNat) : Set where
  field
    orbitAboveThreshold : (j : Nat) → Set

open BeforeStopping public

record SyracuseStoppedLogDriftSource
    (analysis : Boundary.SyracuseLogAnalysisSource) : Set₁ where
  field
    affineSource : Affine.SyracuseAffineIterateSource

    remainder :
      Nat → Syracuse.PositiveNat → Boundary.Real analysis

    remainderNonnegative :
      (m : Nat) → (x : Syracuse.PositiveNat) → Set

    exactLogDecomposition :
      (m : Nat) → (x : Syracuse.PositiveNat) → Set

    stoppedRemainderBound :
      (region : StoppingRegion) →
      (m : Nat) →
      (x : Syracuse.PositiveNat) →
      BeforeStopping region m x → Set

open SyracuseStoppedLogDriftSource public

record StoppedLogDriftBoundary : Set where
  constructor stoppedLogDriftBoundary
  field
    finiteResidueLogUsed : Nat
    remainderAttachedToLiteralOrbit : Nat
    sharpBoundMayBeAssumedSilently : Nat
    missingAnalysisExposedAsTypedSource : Nat

canonicalStoppedLogDriftBoundary : StoppedLogDriftBoundary
canonicalStoppedLogDriftBoundary = stoppedLogDriftBoundary 0 1 0 1
