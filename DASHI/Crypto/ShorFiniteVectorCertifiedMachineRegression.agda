module DASHI.Crypto.ShorFiniteVectorCertifiedMachineRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorFiniteVectorCertifiedMachineExact as Machine

------------------------------------------------------------------------
-- RED regression.
--
-- Once the literal vector QFT inversion theorem and supported-observation ABI
-- are supplied, the existing Shor period-machine compiler should be reachable
-- directly on the preferred finite-vector route.
------------------------------------------------------------------------

preferredMachineExists :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
    (support : Supported.CoefficientSupportAuthority A) →
  Supported.FiniteVectorSupportedObservationABI P qNonZero A support →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
preferredMachineExists = Machine.compileFiniteVectorCertifiedMachine
