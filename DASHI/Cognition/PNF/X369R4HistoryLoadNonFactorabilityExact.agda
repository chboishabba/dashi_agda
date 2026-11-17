{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.X369R4HistoryLoadNonFactorabilityExact where

-- ORIGINAL DASHI owner reuse: Core.IntersectionalNonFactorability.
-- Fixed synthetic R4 coherent source parameter fixture, source algebra:
-- two two-step original HistoryOrbitMoE trajectories
--  prefix t=0 -> common probe t=2: selected [0,2], Nat 0
--  prefix t=3 -> common probe t=2: selected [1,0], Nat 9
-- Both probe steps have the SAME activation and clock index 1.
-- Hence the source-shaped observed Nat response is not a function of
-- load alone once the original per-expert retained histories matter.
--
-- CONDITIONAL / FINITE ONLY. This module does NOT certify exact Torch
-- selected execution, actual trained weights, hardware roundoff, or
-- arbitrary recurrent hysteresis. The native source witness belongs to
-- LeechTransformer scripts/check_x369_r4_native_topk_kink.py.
-- Original Leech-LILA architectural attribution: Anatolii Kornienko.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF

data R4ProbeHistoryPath : Set where
  lowerLoadFirst higherLoadFirst : R4ProbeHistoryPath

sameSecondStepLoad : R4ProbeHistoryPath → Nat
sameSecondStepLoad _ = 2

sameSecondStepClock : R4ProbeHistoryPath → Nat
sameSecondStepClock _ = 1

sourceFixtureHistoryDependentResponse : R4ProbeHistoryPath → Nat
sourceFixtureHistoryDependentResponse lowerLoadFirst = 0
sourceFixtureHistoryDependentResponse higherLoadFirst = 9

-- The original non-factorability carrier must include history.
-- Post-composing a load-only observer cannot reconstruct this
-- second-step difference; it must retain richer state information.
sourceFixtureLoadOnlyNonFactorability :
  NF.NonFactorabilityWitness
    sameSecondStepLoad
    sourceFixtureHistoryDependentResponse
sourceFixtureLoadOnlyNonFactorability =
  NF.nonFactorabilityWitness
    lowerLoadFirst higherLoadFirst refl (λ ())

sourceFixtureResponseCannotFactorThroughLoad :
  NF.FactorsThrough
    sameSecondStepLoad sourceFixtureHistoryDependentResponse → ⊥
sourceFixtureResponseCannotFactorThroughLoad =
  NF.witnessRulesOutEveryFlatFactorisation
    sourceFixtureLoadOnlyNonFactorability

sourceFixtureLoadRechartCannotRecoverHistory :
  ∀ {Rechart : Set} →
  (rechart : Nat → Rechart) →
  NF.FactorsThrough
    (λ state → rechart (sameSecondStepLoad state))
    sourceFixtureHistoryDependentResponse → ⊥
sourceFixtureLoadRechartCannotRecoverHistory rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart sourceFixtureLoadOnlyNonFactorability

-- Reusing the single-axis nonfactorability theorem does NOT
-- identify actual Leech recurrent-state dimensions or prove that
-- a fitted model exhibits this fixture. The original source must
-- instantiate the declared outputs and equal-clock conditions.
