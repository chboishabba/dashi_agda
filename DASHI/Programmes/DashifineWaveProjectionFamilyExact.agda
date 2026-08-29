module DASHI.Programmes.DashifineWaveProjectionFamilyExact where

open import DASHI.Core.Prelude
import DASHI.Programmes.DashifineBenchmarkCorrectionExact as Benchmark

------------------------------------------------------------------------
-- Literal task family matching `newtest/wave_krr_family.py`.
--
-- The family is frozen before evaluating the new stress test.  It contains the
-- original two-coordinate observation and two deliberately information-reducing
-- coordinate projections.  The theorem below says exactly what a family claim
-- requires; it does not predict that the dashifine kernel will win all three.
------------------------------------------------------------------------

data WaveProjectionTask : Set where
  fullXY : WaveProjectionTask
  xOnly : WaveProjectionTask
  yOnly : WaveProjectionTask

record WaveProjectionFamilyReceipt
    {Model Score : Set}
    (comparison : Benchmark.TaskIndexedComparison
      WaveProjectionTask Model Score)
    (dashifineModel baseline : Model) : Set where
  constructor waveProjectionFamilyReceipt
  field
    fullReceipt :
      Benchmark.TaskDominates comparison fullXY dashifineModel baseline
    xOnlyReceipt :
      Benchmark.TaskDominates comparison xOnly dashifineModel baseline
    yOnlyReceipt :
      Benchmark.TaskDominates comparison yOnly dashifineModel baseline

open WaveProjectionFamilyReceipt public

waveProjectionReceiptYieldsFamilyDominance :
  ∀ {Model Score : Set}
    {comparison : Benchmark.TaskIndexedComparison
      WaveProjectionTask Model Score}
    {dashifineModel baseline : Model} →
  WaveProjectionFamilyReceipt comparison dashifineModel baseline →
  Benchmark.FamilyDominanceReceipt comparison dashifineModel baseline
waveProjectionReceiptYieldsFamilyDominance receipt =
  Benchmark.familyDominanceReceipt all
  where
    all :
      (task : WaveProjectionTask) →
      Benchmark.TaskDominates comparison task dashifineModel baseline
    all fullXY = fullReceipt receipt
    all xOnly = xOnlyReceipt receipt
    all yOnly = yOnlyReceipt receipt

record DashifineWaveProjectionBoundary : Set where
  constructor dashifineWaveProjectionBoundary
  field
    familyWasDeclaredBeforeFamilyEvaluation : Bool
    familyWasDeclaredBeforeFamilyEvaluationIsTrue :
      familyWasDeclaredBeforeFamilyEvaluation ≡ true

    originalWaveWinFillsProjectedTaskReceipts : Bool
    originalWaveWinFillsProjectedTaskReceiptsIsFalse :
      originalWaveWinFillsProjectedTaskReceipts ≡ false

    projectedTaskFailureIsUsefulBoundaryEvidence : Bool
    projectedTaskFailureIsUsefulBoundaryEvidenceIsTrue :
      projectedTaskFailureIsUsefulBoundaryEvidence ≡ true

canonicalDashifineWaveProjectionBoundary : DashifineWaveProjectionBoundary
canonicalDashifineWaveProjectionBoundary =
  dashifineWaveProjectionBoundary
    true refl
    false refl
    true refl
