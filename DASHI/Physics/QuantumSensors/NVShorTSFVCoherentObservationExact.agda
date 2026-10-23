module DASHI.Physics.QuantumSensors.NVShorTSFVCoherentObservationExact where

-- Reuses Shor's literal cyclic coefficient algebra and Born-weight authority
-- as a finite Feynman/TSFV optical observation *consumer*.
-- This is not an RSA algorithm, a physical NV calibration, a
-- TSFV Candidate256 S/hbar realization, or a continuum path integral.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Born

module FiniteOpticalAlternatives
  {Q : Nat} {Coefficient Weight : Set}
  (algebra : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
  (weights : Born.CoefficientBornWeightAuthority algebra Weight) where

  open Phase.CyclicPhaseCoefficientAuthority algebra
    using (zeroCoefficient; addCoefficient; multiplyCoefficient; phase)

  open Born.CoefficientBornWeightAuthority weights
    using (normSquared; addWeight)

  -- Two source-to-detector alternatives with a phase coefficient drawn
  -- from the same cyclic-character authority used by the Shor QFT.
  record AlternativePair : Set where
    constructor alternatives
    field
      upper lower : Coefficient
      phaseIndex pathIndex : Fin Q
  open AlternativePair public

  lowerWithPhase : AlternativePair → Coefficient
  lowerWithPhase a =
    multiplyCoefficient
      (phase (phaseIndex a) (pathIndex a))
      (lower a)

  coherentAmplitude : AlternativePair → Coefficient
  coherentAmplitude a = addCoefficient (upper a) (lowerWithPhase a)

  -- Amplitudes must combine before squared norm for indistinguishable
  -- alternatives; distinguishable-path detection sums their weights.
  coherentWeight : AlternativePair → Weight
  coherentWeight a = normSquared (coherentAmplitude a)

  distinguishableWeight : AlternativePair → Weight
  distinguishableWeight a =
    addWeight (normSquared (upper a))
              (normSquared (lowerWithPhase a))

  coherentWeightRespectsAmplitudeEquality :
    (a b : AlternativePair) →
    coherentAmplitude a ≡ coherentAmplitude b →
    coherentWeight a ≡ coherentWeight b
  coherentWeightRespectsAmplitudeEquality a b p = cong normSquared p

  -- Measurement ports and detector transfer must carry separate calibrated
  -- normalization/positivity witnesses; Shor's coefficient authority alone
  -- does not supply Born probabilities or a photon-count likelihood.

  record PhotonPort : Set where
    constructor photon-port
    field
      observeWeight : Weight → Weight
  open PhotonPort public

  observedCoherentWeight : PhotonPort → AlternativePair → Weight
  observedCoherentWeight port a =
    observeWeight port (coherentWeight a)

  observationRespectsCoherentEquality :
    (port : PhotonPort) (a b : AlternativePair) →
    coherentAmplitude a ≡ coherentAmplitude b →
    observedCoherentWeight port a ≡ observedCoherentWeight port b
  observationRespectsCoherentEquality port a b equal =
    cong (observeWeight port)
         (coherentWeightRespectsAmplitudeEquality a b equal)
