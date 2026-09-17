module DASHI.Crypto.ShorFiniteVectorContinuedFractionMachineRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorFiniteVectorContinuedFractionMachineExact as Machine

------------------------------------------------------------------------
-- RED regression.
--
-- The preferred vector route should no longer require a free
-- FourierSample -> Nat candidate function once the concrete Shor continued-
-- fraction producer is available.
------------------------------------------------------------------------

continuedFractionMachineExists :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
    (support : Supported.CoefficientSupportAuthority A)
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
      Supported.SupportedExponentOutcome support state) →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
continuedFractionMachineExists =
  Machine.compileFiniteVectorContinuedFractionMachine
