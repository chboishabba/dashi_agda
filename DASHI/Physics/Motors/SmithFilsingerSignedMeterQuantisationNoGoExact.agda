module DASHI.Physics.Motors.SmithFilsingerSignedMeterQuantisationNoGoExact where

-- Strict F10/F13 quantisation NO-GO, exact Agda conditional theorem.
-- Reuses the original signed Nat-pair setoid and its parity obstruction.
-- Does NOT invent a second real-field algebra, replace C3.RealField or
-- claim that any original Filsinger meter samples physical SI work.
--
-- If a source carrier contains a half h with h + h = one native unit,
-- an additive EXACT integer-work meter cannot map that native unit to
-- ONE integer quantum while preserving the cross-sum signed work.
-- This defeats an invalid exact field-to-Nat handoff; real/rational
-- flux must instead remain native or carry lattice/rounding evidence.
--
-- Authoritative owners: SmithFilsingerSignedBoundaryGroupCompletionExact
-- and original MidpointTwoPortWorkExact. No physical power promotion.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Motors.SmithFilsingerSignedBoundaryGroupCompletionExact as Signed
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

workEqualityFromLiteralEquality :
  {a b : Signed.DirectedSignedWork} →
  a ≡ b → Signed.sameSignedWork a b
workEqualityFromLiteralEquality {a = a} refl =
  Signed.sameSignedReflexive a

-- No continuous physics is needed for this exact algebraic impossibility.
-- The actual source A may be a rational, a real field, or a selected
-- half-closed subcarrier; its operation and half identity are supplied.
--
-- It is not a statement that every physical meter uses one-unit counts.
-- It rules out ONE unjustified exact calibration contract.
additiveExactMeterCannotSendHalvedUnitToOneQuantum :
  ∀ {ℓ : Level} {A : Set ℓ} →
  (_⊕_ : A → A → A)
  (half full : A) →
  half ⊕ half ≡ full →
  (meter : A → Signed.DirectedSignedWork) →
  ((x y : A) →
    Signed.sameSignedWork
      (meter (x ⊕ y))
      (Signed.combinedPorts (meter x) (meter y))) →
  Signed.sameSignedWork
    (meter full)
    (Signed.directedSignedWork (suc zero) zero) →
  Port.Contradiction
additiveExactMeterCannotSendHalvedUnitToOneQuantum
  _⊕_ half full doubleHalfIsFull meter additive meterUnit =
  Signed.oneWorkQuantumHasNoExactSignedHalf a b
    (Signed.sameSignedTransitive
      (Signed.combinedPorts halfMeter halfMeter)
      (meter (half ⊕ half))
      (Signed.directedSignedWork (suc zero) zero)
      (Signed.sameSignedSymmetric
        (meter (half ⊕ half))
        (Signed.combinedPorts halfMeter halfMeter)
        (additive half half))
      (Signed.sameSignedTransitive
        (meter (half ⊕ half))
        (meter full)
        (Signed.directedSignedWork (suc zero) zero)
        (workEqualityFromLiteralEquality
          (Agda.Builtin.Equality.cong meter doubleHalfIsFull))
        meterUnit))
  where
    halfMeter : Signed.DirectedSignedWork
    halfMeter = meter half

    a : Nat
    a = Signed.DirectedSignedWork.incoming halfMeter

    b : Nat
    b = Signed.DirectedSignedWork.outgoing halfMeter
