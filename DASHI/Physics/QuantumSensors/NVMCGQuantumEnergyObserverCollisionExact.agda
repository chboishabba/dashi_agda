module DASHI.Physics.QuantumSensors.NVMCGQuantumEnergyObserverCollisionExact where

-- Consume existing MCG axial Hamiltonian and existing same-object
-- C3/qutrit chart from stacked PR #1269, without reimplementing either.
-- Cross-pollination: observer-collision / factorisation methodology used
-- in Agda #1266, while keeping this an independent physical-model result.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as NV
import DASHI.Physics.QuantumSensors.NVMCGQuantumComputingSameObjectWeldExact as Weld

-- Exactly the two distinct spin-one branches that are degenerate at B=0.
plusDifferentFromMinus : C3.c0 ≡ C3.c2 → ⊥
plusDifferentFromMinus ()

zeroField : ℚ → ℚ → NV.AxialNV
zeroField d gamma = NV.axial-nv d gamma 0ℚ

-- Source-native rational axial NV energy: an explicitly non-injective
-- observer on the true label carrier, not an abstract or invented model.
zeroFieldEnergyCollision :
  ∀ (d gamma : ℚ) →
  Weld.levelEnergy (zeroField d gamma) C3.c0
  ≡ Weld.levelEnergy (zeroField d gamma) C3.c2
zeroFieldEnergyCollision d gamma = refl

-- No exact recovery of ALL spin-state labels from a single scalar energy
-- observation at B=0. This is a constructive finite identification no-go.
noExactLabelDecoderFromZeroFieldEnergy :
  ∀ (d gamma : ℚ) →
  (decode : ℚ → C3.C3) →
  ((x : C3.C3) →
    decode (Weld.levelEnergy (zeroField d gamma) x) ≡ x) →
  ⊥
noExactLabelDecoderFromZeroFieldEnergy d gamma decode roundtrip =
  plusDifferentFromMinus
    (trans (sym (roundtrip C3.c0))
      (trans (cong decode (zeroFieldEnergyCollision d gamma))
             (roundtrip C3.c2)))

-- Evidence boundary: this rules out *energy-only* decoding at B=0.
-- Optical spin contrast, microwave-frequency discrimination, magnetic
-- splitting and additional context are richer measurements; the theorem
-- does not rule them out, nor does it imply a calibrated detector.
