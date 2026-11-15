module DASHI.Physics.Motors.ReluctancePermeancePulseBoundaryExact where

-- Conditional physical bridge and actual Nat energy-budget no-surplus proof.
-- These are NOT a motor-specific Maxwell/FEA construction and NOT a
-- calibration of @madscience369 V2, Holmstrom, or Slobodian hardware.
-- Original physics: Maxwell, Faraday, electromagnetic coenergy, reluctance
-- torque. Modern finite phase/MDL organisation: DASHI; no historical Tesla
-- claim of DASHI Base369 mathematics or universal 369 physical privilege.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (false)

import DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary as Tesla
import DASHI.Physics.Motors.MadScience369V2FinitePowerDiscriminatorsExact as V2

-- The reciprocal of reluctance is defined on a supported scalar domain;
-- this record does not assert a single-valued linear B-H law for hysteresis.
record ReciprocalPermeance : Set₁ where
  field
    Scalar : Set
    one : Scalar
    _×_ : Scalar → Scalar → Scalar
    reluctance permeance : Scalar
    reciprocalLaw : _×_ reluctance permeance ≡ one

-- Linear single-coil relation L = N² * permeance. In a real machine the
-- effective flux path, leakage and saturation must be source-calibrated.
record LinearCoilPermeance : Set₁ where
  field
    magnetic : ReciprocalPermeance
    turns inductance : ReciprocalPermeance.Scalar magnetic
    linearTurnsLaw :
      ReciprocalPermeance._×_ magnetic
        (ReciprocalPermeance._×_ magnetic turns turns)
        (ReciprocalPermeance.permeance magnetic)
      ≡ inductance

-- Actual conservation lemma over energies in the SAME physical boundary.
-- 'otherExternal' includes any undisclosed pulse, driver, controller, Earth
-- or auxiliary port. 'storageRise' is signed here only when nonnegative;
-- for a decreasing storage state one must reclassify depletion as an input
-- or use a signed additive energy carrier instead.
record NonnegativeCycleBudget : Set where
  constructor cycle-budget
  field
    input otherExternal load loss storageRise : Nat
    balanced : input + otherExternal ≡ load + loss + storageRise

open NonnegativeCycleBudget public

plusRightZero : (a : Nat) → a + zero ≡ a
plusRightZero zero = refl
plusRightZero (suc a) rewrite plusRightZero a = refl

-- No external input or positive storage increase: the input is exactly
-- load plus nonnegative loss. This is conditional on the *actual* balance.
closedCycleBalance :
  (b : NonnegativeCycleBudget) →
  otherExternal b ≡ zero → storageRise b ≡ zero →
  input b ≡ load b + loss b
closedCycleBalance b noExternal noStorage
  rewrite noExternal | noStorage
        | plusRightZero (input b)
        | plusRightZero (load b + loss b) = balanced b

-- Explicit Nat ordering, no oracle or undefined physical constant.
data _≤_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ n
  suc≤ : ∀ {a b} → a ≤ b → suc a ≤ suc b

loadWithinLoadPlusLoss : (load loss : Nat) → load ≤ load + loss
loadWithinLoadPlusLoss zero loss = zero≤
loadWithinLoadPlusLoss (suc load) loss = suc≤ (loadWithinLoadPlusLoss load loss)

transportBack :
  (P : Nat → Set) {x y : Nat} → x ≡ y → P y → P x
transportBack P refl py = py

-- In particular, an observed positive load cannot be bigger than actual
-- supplied input for this closed, stored-energy-nondepleting physical budget.
closedCycleLoadWithinInput :
  (b : NonnegativeCycleBudget) →
  otherExternal b ≡ zero → storageRise b ≡ zero →
  load b ≤ input b
closedCycleLoadWithinInput b noExternal noStorage =
  transportBack (λ n → load b ≤ n)
    (closedCycleBalance b noExternal noStorage)
    (loadWithinLoadPlusLoss (load b) (loss b))

-- Finite V2 coarse display is intentionally not that full boundary.
reelPulseTopologyStillUnverified :
  V2.AttributedV2Claim.pulseTopologyEstablished V2.reelClaim ≡ false
reelPulseTopologyStillUnverified = V2.pulseTopologyNotEstablished

sameDisplayAllowsDifferentLossPartition :
  V2.NonnegativePowerPartition.input V2.unloadedIllustration
  ≡ V2.NonnegativePowerPartition.input V2.loadedIllustration
sameDisplayAllowsDifferentLossPartition = V2.sameDisplayedInput

-- Historical source firewall reused from the canonical repo owner.
base369NotHistoricallyAttributedToTesla :
  Tesla.base369AttributedToTesla Tesla.teslaPolyphaseBoundary ≡ false
base369NotHistoricallyAttributedToTesla = Tesla.base369-is-modern-extension