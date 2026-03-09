module DASHI.Physics.Closure.Validation.SnapThresholdLaw where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.SeverityGuard.Core as SG

data SnapThresholdVerdict : Set where
  snapThresholdWitnessed : SnapThresholdVerdict

record SnapThresholdHarness {ℓ : Level} : Set (lsuc ℓ) where
  field
    label : String
    X : Set ℓ
    policy : SG.SeverityPolicy X
    witnessState : X
    witnessSnap : SG.Snap policy witnessState

record SnapThresholdFacts {ℓ : Level}
  (harness : SnapThresholdHarness {ℓ}) : Set (lsuc ℓ) where
  field
    snapWitness :
      SG.Snap
        (SnapThresholdHarness.policy harness)
        (SnapThresholdHarness.witnessState harness)

computeFacts :
  ∀ {ℓ} (harness : SnapThresholdHarness {ℓ}) →
  SnapThresholdFacts harness
computeFacts harness =
  record
    { snapWitness = SnapThresholdHarness.witnessSnap harness
    }

classify : ∀ {ℓ} {harness : SnapThresholdHarness {ℓ}} →
  SnapThresholdFacts harness → SnapThresholdVerdict
classify _ = snapThresholdWitnessed
