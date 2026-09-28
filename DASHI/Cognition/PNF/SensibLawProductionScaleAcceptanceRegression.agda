{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.SensibLawProductionScaleAcceptanceRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Cognition.PNF.SensibLawProductionScaleAcceptanceExact as Scale

fixtureWorkers : Scale.WorkerScalingAcceptance
fixtureWorkers =
  Scale.worker-scaling-acceptance
    "runtime:fixture"
    "workload:fixture"
    true refl
    true refl
    true refl
    true refl
    true refl

fixtureArchive : Scale.ArchiveScaleAcceptance
fixtureArchive =
  Scale.archive-scale-acceptance
    "runtime:fixture"
    "parser_tokens"
    true refl
    true refl
    true refl
    true refl
    true refl

fixtureClosure : Scale.ProductionScaleClosure
fixtureClosure =
  Scale.production-scale-closure
    "runtime:fixture"
    true refl
    fixtureWorkers
    fixtureArchive
    true refl
    false refl
    false refl

fixtureParallelEvidenceIsNotBaselineOnly :
  Scale.parallelObservationUsesMoreThanOneWorker fixtureWorkers ≡ true
fixtureParallelEvidenceIsNotBaselineOnly = refl

fixtureArchiveUsesDeclaredBudget :
  Scale.declaredWorkPerCarrierBudgetMet fixtureArchive ≡ true
fixtureArchiveUsesDeclaredBudget = refl

fixtureArchiveUsesNontrivialSpan :
  Scale.declaredMinimumSpanRatioMet fixtureArchive ≡ true
fixtureArchiveUsesNontrivialSpan = refl

fixtureClosureDoesNotCreateAuthority :
  Scale.createsSemanticAuthority fixtureClosure ≡ false
fixtureClosureDoesNotCreateAuthority = refl
