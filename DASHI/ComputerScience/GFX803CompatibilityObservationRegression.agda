module DASHI.ComputerScience.GFX803CompatibilityObservationRegression where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GPUCompatibilityObservationExact as Compat
import DASHI.ComputerScience.GFX803CompatibilityReceiptExact as GFX803

------------------------------------------------------------------------
-- Focused regression root for query-indexed GPU compatibility.
--
-- Intended local command:
--   agda -i . DASHI/ComputerScience/GFX803CompatibilityObservationRegression.agda
------------------------------------------------------------------------

visibilityDoesNotDetermineCorrectness :
  Compat.QueryAdequacyBoundary.gpuVisibilityDeterminesNumericalCorrectness
    Compat.canonicalQueryAdequacyBoundary
  ≡ false
visibilityDoesNotDetermineCorrectness = refl

summaryDoesNotDetermineResetSafety :
  Compat.QueryAdequacyBoundary.summaryProjectionDeterminesResetSafety
    Compat.canonicalQueryAdequacyBoundary
  ≡ false
summaryDoesNotDetermineResetSafety = refl

upgradeIsNotMonotone :
  Compat.UpgradeBoundary.newerComponentsPreserveCompatibilityMonotonically
    Compat.canonicalUpgradeBoundary
  ≡ false
upgradeIsNotMonotone = refl

mitigationDoesNotProveMechanism :
  Compat.InterventionBoundary.successfulMitigationEstablishesRootCause
    Compat.canonicalInterventionBoundary
  ≡ false
mitigationDoesNotProveMechanism = refl

visibilityCollisionWitnessed : Compat.VisibilityCorrectnessDefect
visibilityCollisionWitnessed = Compat.visibilityCorrectnessDefect

summaryResetCollisionWitnessed : Compat.SummaryResetSafetyDefect
summaryResetCollisionWitnessed = Compat.summaryResetSafetyDefect

correctnessRepairedByEnrichment : Compat.CorrectnessAdequateAfterEnrichment
correctnessRepairedByEnrichment = Compat.correctnessAdequateAfterEnrichment

resetSafetyRepairedByEnrichment : Compat.ResetSafetyAdequateAfterEnrichment
resetSafetyRepairedByEnrichment = Compat.resetSafetyAdequateAfterEnrichment

gfx803ReceiptIsProjectBound :
  GFX803.GFX803Boundary.projectReceiptCreatesVendorGuarantee
    GFX803.canonicalGFX803Boundary
  ≡ false
gfx803ReceiptIsProjectBound = refl

gfx803BlockingSuccessDoesNotProveAsyncRootCause :
  GFX803.GFX803Boundary.blockingSuccessProvesAsyncSchedulingRootCause
    GFX803.canonicalGFX803Boundary
  ≡ false
gfx803BlockingSuccessDoesNotProveAsyncRootCause = refl

gfx803OldAbiLaneIsScoped :
  GFX803.GFX803Boundary.oldABIPreservationIsScopedCompatibilityEvidence
    GFX803.canonicalGFX803Boundary
  ≡ true
gfx803OldAbiLaneIsScoped = refl
