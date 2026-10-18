module DASHI.Crypto.ShorFiniteVectorCanonicalMachineRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorCanonicalCoefficientSupportExact as CanonicalSupport
import DASHI.Crypto.ShorFiniteVectorCanonicalMachineExact as Machine

------------------------------------------------------------------------
-- RED regression.
--
-- The preferred logical Shor route must not require a caller-selected support
-- predicate or a caller-selected FourierSample -> Nat extractor.  Support is
-- coefficient != zero, and candidate extraction is the concrete continued-
-- fraction producer.  The only observation-side input is selection of an
-- actually supported exponent outcome.
------------------------------------------------------------------------

canonicalMachineExists :
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
    (selectSupportedOutcome :
      (state :
        VectorPrefix.VectorRegisterState
          qNonZero
          (PowModWeld.orderModulusNonZero P)
          a A) →
      Supported.SupportedExponentOutcome
        (CanonicalSupport.canonicalCoefficientSupport A)
        state) →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
canonicalMachineExists = Machine.compileFiniteVectorCanonicalMachine
