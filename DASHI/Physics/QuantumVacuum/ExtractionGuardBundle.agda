module DASHI.Physics.QuantumVacuum.ExtractionGuardBundle where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- Explicit blocked claims.  These are proof obligations against accidental
-- promotion, not scientific assertions that future experiments must fail.
------------------------------------------------------------------------

record ExtractionGuardBundle : Set where
  constructor extractionGuardBundle
  field
    noEffectToPowerLeap :
      (m : Surface.Mechanism) →
      Surface.promotable?
        (Surface.mkExtractionClaim m Surface.transient
          Surface.preliminaryExperiment true true false false false)
      ≡ false

    noResetFreeContinuousMachine :
      (m : Surface.Mechanism) →
      Surface.promotable?
        (Surface.mkExtractionClaim m Surface.continuous
          Surface.replicatedExperiment true true true false true)
      ≡ false

    noUnreplicatedPowerPromotion :
      (m : Surface.Mechanism) →
      Surface.promotable?
        (Surface.mkExtractionClaim m Surface.continuous
          Surface.closedEngineeringCycle true true true true false)
      ≡ false

canonicalExtractionGuards : ExtractionGuardBundle
canonicalExtractionGuards =
  extractionGuardBundle
    (λ m → refl)
    (λ m → refl)
    (λ m → refl)

reactionlessPropulsionPromoted : Bool
reactionlessPropulsionPromoted = false

perpetualVacuumPowerPromoted : Bool
perpetualVacuumPowerPromoted = false

guardNoReactionlessPropulsion : reactionlessPropulsionPromoted ≡ false
guardNoReactionlessPropulsion = refl

guardNoPerpetualVacuumPower : perpetualVacuumPowerPromoted ≡ false
guardNoPerpetualVacuumPower = refl
