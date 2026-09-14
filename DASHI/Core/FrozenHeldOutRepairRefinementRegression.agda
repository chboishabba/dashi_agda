module DASHI.Core.FrozenHeldOutRepairRefinementRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.Core.FrozenHeldOutRepairRefinementExact as Adapter

parentHeldOutRepairRetained :
  ∀ {Rule Repair Training HeldOut Prediction : Set} →
  Adapter.FrozenHeldOutRepair Rule Repair Training HeldOut Prediction →
  Robust.HeldOutRepair Repair Training HeldOut Prediction
parentHeldOutRepairRetained = Adapter.retainsHeldOutRepair

frozenSelectionRetained :
  ∀ {Rule Repair Training HeldOut Prediction : Set} →
  Adapter.FrozenHeldOutRepair Rule Repair Training HeldOut Prediction →
  Frozen.FrozenSelectionReceipt Rule
frozenSelectionRetained = Adapter.retainsFrozenSelection

heldOutRepairAloneDoesNotProveFrozenSelection :
  Adapter.HeldOutRepairAutomaticallyFrozen → ⊥
heldOutRepairAloneDoesNotProveFrozenSelection =
  Adapter.heldOutRepairDoesNotAutomaticallyFreezeSelection

frozenSelectionAloneDoesNotCreateHeldOutRepair :
  Adapter.FrozenSelectionAutomaticallyCreatesHeldOutRepair → ⊥
frozenSelectionAloneDoesNotCreateHeldOutRepair =
  Adapter.frozenSelectionDoesNotAutomaticallyCreateHeldOutRepair
