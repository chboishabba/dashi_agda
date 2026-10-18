module DASHI.Crypto.ShorFiniteVectorSupportedObservationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported

------------------------------------------------------------------------
-- RED regression.
--
-- Preferred observation semantics must not select an arbitrary exponent from a
-- post-QFT state.  The selected Fin Q outcome carries evidence that at least one
-- target column at that exponent is classified nonzero by the supplied
-- coefficient-support authority.  No probability statement is required.
------------------------------------------------------------------------

selectedOutcomeIsSupported :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (support : Supported.CoefficientSupportAuthority A)
    (state :
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A)
    (selected : Supported.SupportedExponentOutcome support state) →
  Supported.ExponentSupported support state (fst selected)
selectedOutcomeIsSupported P qNonZero A support state selected = snd selected

supportedSampleUsesSelectedExponent :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (support : Supported.CoefficientSupportAuthority A)
    (state :
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A)
    (selected : Supported.SupportedExponentOutcome support state) →
  QFT.numerator (Supported.supportedFourierSample Q selected)
  ≡ Data.Fin.Base.toℕ (fst selected)
supportedSampleUsesSelectedExponent P qNonZero A support state selected = refl
