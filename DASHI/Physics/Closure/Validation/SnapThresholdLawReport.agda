module DASHI.Physics.Closure.Validation.SnapThresholdLawReport where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL

record SnapThresholdReport {ℓ : Level} : Set (lsuc ℓ) where
  field
    harness : STL.SnapThresholdHarness {ℓ}
    facts : STL.SnapThresholdFacts harness
    verdict : STL.SnapThresholdVerdict

buildReport :
  ∀ {ℓ} (harness : STL.SnapThresholdHarness {ℓ}) →
  SnapThresholdReport
buildReport harness =
  let facts = STL.computeFacts harness
  in
  record
    { harness = harness
    ; facts = facts
    ; verdict = STL.classify facts
    }
