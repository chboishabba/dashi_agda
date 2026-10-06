module DASHI.Analysis.CollatzSyracuseStoppingConcentrationExact where

------------------------------------------------------------------------
-- INTEGER STOPPING/CONCENTRATION COMPILER
--
-- This packages the exact dependency cut.  It is intentionally conditional:
-- concentration, stopped log drift, and sampled-start pushforward must each be
-- supplied as theorem-bearing sources before an integer stopping tail exists.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseLogDriftBoundaryExact as LogBoundary
import DASHI.NumberTheory.Collatz.SyracuseLogDriftExact as LogDrift
import DASHI.Analysis.CollatzSyracuseMixingConcentrationCompilerExact as Concentration
import DASHI.Analysis.CollatzSyracuseSamplingPushforwardExact as Sampling
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

record SyracuseStoppingConcentrationSource
    (analysis : LogBoundary.SyracuseLogAnalysisSource) : Set₁ where
  field
    cylinders : Cylinder.ParityCylinderSource
    sampling : Sampling.SamplingPushforwardSource cylinders
    concentration : Concentration.SyracuseConcentrationSource
    logDrift : LogDrift.SyracuseStoppedLogDriftSource analysis

    threshold : Nat
    horizon : Nat
    sampledIntegerStoppingTail : Set

open SyracuseStoppingConcentrationSource public

record StoppingConcentrationBoundary : Set where
  constructor stoppingConcentrationBoundary
  field
    concentrationHypothesesExplicit : Nat
    samplingLawExplicit : Nat
    stoppedRemainderExplicit : Nat
    provesUniversalCollatz : Nat

canonicalStoppingConcentrationBoundary : StoppingConcentrationBoundary
canonicalStoppingConcentrationBoundary =
  stoppingConcentrationBoundary 1 1 1 0
