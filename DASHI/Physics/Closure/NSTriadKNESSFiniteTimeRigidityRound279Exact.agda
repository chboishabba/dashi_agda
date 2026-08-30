module DASHI.Physics.Closure.NSTriadKNESSFiniteTimeRigidityRound279Exact where

------------------------------------------------------------------------
-- ROUND279 / ESS BACKWARD UNIQUENESS ON THE FINITE-TIME BRANCH
--
-- R278 is responsible for manufacturing the terminal vorticity and coefficient
-- hypotheses.  Once those are present, the published ESS mechanism rules out
-- the nontrivial critical element by backward uniqueness / unique continuation.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record ESSFiniteTimeRigidity {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics
    terminalVorticityVanishingInESSClass : Set ℓ
    essParabolicCoefficientClass : Set ℓ
    backwardUniquenessForcesZeroVorticity : Set ℓ
    zeroVorticityPlusDivergenceFreeDecayForcesZeroVelocity : Set ℓ
    mixedDefectCriticalElementNonzero : Set ℓ
    zeroVelocityContradictsCriticalElement :
      zeroVorticityPlusDivergenceFreeDecayForcesZeroVelocity →
      mixedDefectCriticalElementNonzero → ⊥

open ESSFiniteTimeRigidity public

finiteTimeCriticalElementImpossible :
  ∀ {ℓ} {CriticalDynamics : Set ℓ} →
  ESSFiniteTimeRigidity CriticalDynamics → ⊥
finiteTimeCriticalElementImpossible A =
  zeroVelocityContradictsCriticalElement A
    (zeroVorticityPlusDivergenceFreeDecayForcesZeroVelocity A)
    (mixedDefectCriticalElementNonzero A)

round279ESSIsConditionalOnRound278TerminalGeometry : Bool
round279ESSIsConditionalOnRound278TerminalGeometry = true

round279BackwardUniquenessMechanismSourceOwned : Bool
round279BackwardUniquenessMechanismSourceOwned = true

round279PhysicalESSInstanceClosed : Bool
round279PhysicalESSInstanceClosed = false

round279PackageAClosed : Bool
round279PackageAClosed = false

round279PhysicalESSInstanceClosedIsFalse : round279PhysicalESSInstanceClosed ≡ false
round279PhysicalESSInstanceClosedIsFalse = refl
