module DASHI.Physics.QuantumSensors.NVPhotonObserverRefinementExact where

-- A measurement-conditional refinement of the existing same-object
-- zero-field axial-energy collision, not an empirical fluorescence claim.
-- Source owner: NVPhotonBinaryLikelihoodExact for normalized outcome pairs.
-- Methodological neighbour: Agda observer collision PR #1266.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Rational.Base using (ℚ)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as NV
import DASHI.Physics.QuantumSensors.NVMCGQuantumComputingSameObjectWeldExact as Weld
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVMCGQuantumEnergyObserverCollisionExact as Collision

-- Photon response is indexed by *prepared spin state*, with the
-- existing calibrated/nonnegative likelihood object supplied by a caller.
record ConditionalPhotonModel : Set₁ where
  field
    response : C3.C3 → Photon.BinaryPhotonLikelihood
open ConditionalPhotonModel public

-- A minimally sufficient observable fingerprint retains actual energy
-- and the Bernoulli photon fraction; no independent parameters invented.
record EnergyPhotonObservation : Set where
  constructor energy-photon
  field
    energy : ℚ
    photonFraction : ℚ
open EnergyPhotonObservation public

observe :
  NV.AxialNV → ConditionalPhotonModel →
  C3.C3 → EnergyPhotonObservation
observe p model x =
  energy-photon (Weld.levelEnergy p x)
                (Photon.photon (response model x))

-- Even after adding this particular readout, identical photon fractions
-- leave the zero-field ±1 collision unseparated.
photonCollisionPersists :
  ∀ (d gamma : ℚ) (model : ConditionalPhotonModel) →
  Photon.photon (response model C3.c0) ≡
  Photon.photon (response model C3.c2) →
  observe (Collision.zeroField d gamma) model C3.c0 ≡
  observe (Collision.zeroField d gamma) model C3.c2
photonCollisionPersists d gamma model photonEqual
  rewrite Collision.zeroFieldEnergyCollision d gamma
        | photonEqual = refl

-- Thus no universal inverse observer exists when this response collides.
noUniversalDecoderForCollidingPhotonReadout :
  ∀ (d gamma : ℚ) (model : ConditionalPhotonModel) →
  Photon.photon (response model C3.c0) ≡
  Photon.photon (response model C3.c2) →
  (decode : EnergyPhotonObservation → C3.C3) →
  (∀ x → decode (observe (Collision.zeroField d gamma) model x) ≡ x) →
  ⊥
noUniversalDecoderForCollidingPhotonReadout d gamma model same decode leftInverse =
  Collision.plusDifferentFromMinus
    (trans (sym (leftInverse C3.c0))
      (trans (cong decode (photonCollisionPersists d gamma model same))
             (leftInverse C3.c2)))

-- Conversely, a supplied photon-fraction separation witness establishes
-- separation of the observation *distributions*. It does not imply
-- single-shot error-free classification or physical implementation.
photonDifferenceSeparatesObservation :
  ∀ (p : NV.AxialNV) (model : ConditionalPhotonModel) →
  (Photon.photon (response model C3.c0) ≡
   Photon.photon (response model C3.c2) → ⊥) →
  observe p model C3.c0 ≡ observe p model C3.c2 →
  ⊥
photonDifferenceSeparatesObservation p model fractionsDiffer equalObs =
  fractionsDiffer (cong photonFraction equalObs)

-- No claim that p(+1) and p(-1) differ for a real device. This is
-- a predeclared measurement discriminator whose truth must be paid
-- by device-specific source/calibration data and held-out experiments.
