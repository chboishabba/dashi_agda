module DASHI.Crypto.ShorFiniteVectorFourierObservationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin; toℕ)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorCertifiedFourierSamplingExact as Certified
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFiniteVectorFourierObservationExact as Observation

------------------------------------------------------------------------
-- RED regression.
--
-- The preferred finite-vector Shor route must not leave FourierSample as a
-- caller-chosen numerator/denominator pair.  Once an exponent outcome k : Fin Q
-- is selected, the raw Fourier sample is exactly (toℕ k)/Q.  Selection of k,
-- candidate extraction and probability remain separate inputs.
------------------------------------------------------------------------

canonicalSampleNumerator :
  ∀ {Q} (outcome : Fin Q) →
  QFT.numerator (Observation.canonicalFourierSample Q outcome)
  ≡ toℕ outcome
canonicalSampleNumerator outcome = refl

canonicalSampleDenominator :
  ∀ {Q} (outcome : Fin Q) →
  QFT.denominator (Observation.canonicalFourierSample Q outcome)
  ≡ Q
canonicalSampleDenominator outcome = refl

observationUsesSelectedExponentExactly :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
    (seedState : Nat →
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A)
    (selectObservedExponent :
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A →
      Fin Q)
    (candidateExtractor : QFT.FourierSample → Nat)
    (extractorReference : String)
    (state :
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A) →
  Certified.rawFourierSample
    (Certified.observeFourierState
      (Observation.vectorFourierObservationSemantics
        P qNonZero A I
        seedState
        selectObservedExponent
        candidateExtractor
        extractorReference)
      state)
  ≡ Observation.canonicalFourierSample Q (selectObservedExponent state)
observationUsesSelectedExponentExactly
  P qNonZero A I seedState selectObservedExponent candidateExtractor extractorReference state =
  refl
