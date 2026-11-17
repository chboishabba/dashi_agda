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

-- MATCHED SOURCE SELECTED-SUBSET INTERVENTION.
-- The original native selected response at the shared probe is 0 vs 9,
-- but holding the second-step pair fixed at (0,2) (and recalculating
-- its weights from each path's original logits, with its own histories)
-- yields Nat 0 on BOTH paths in the disclosed finite fixture.
-- This is a mathematically admissible restricted/ablation consumer,
-- not a theorem about fitted learned parameter values.
fixedProbePairResponse : R4ProbeHistoryPath → Nat
fixedProbePairResponse lowerLoadFirst = 0
fixedProbePairResponse higherLoadFirst = 0

fixedProbePairDoesFactorThroughCurrentLoad :
  NF.FactorsThrough sameSecondStepLoad fixedProbePairResponse
fixedProbePairDoesFactorThroughCurrentLoad =
  NF.factorsThrough (λ _ → 0) (λ _ → refl)

-- The positive fixed-pair factorisation and negative native-response
-- factorisation coexist on precisely the SAME two situated states.
-- This distinguishes a selected-set-induced effect in the witness
-- from a generic statement that every expert FFN must suppress.

-- Reusing the single-axis nonfactorability theorem does NOT
-- identify actual Leech recurrent-state dimensions or prove that
-- a fitted model exhibits this fixture. The original source must
-- instantiate the declared outputs and equal-clock conditions.
