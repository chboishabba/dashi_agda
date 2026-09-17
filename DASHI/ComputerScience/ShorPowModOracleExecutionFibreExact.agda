module DASHI.ComputerScience.ShorPowModOracleExecutionFibreExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Oracle
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as Weld
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as Exec

------------------------------------------------------------------------
-- EXACT REVERSIBLE powMod PREFIX -> EXISTING QUANTUM EXECUTION FIBRE
--
-- Q1 already supplies the reversible clean-ancilla graph circuit and proves
-- that its loaded value is definitionally the oracle in the modular hidden-
-- period problem.  This owner only packages that circuit into the repository's
-- existing finite quantum execution fibre.
--
-- A Fourier transform and cost profile remain explicit inputs.  In particular,
-- this adapter does not manufacture a QFT by choosing the identity transform.
------------------------------------------------------------------------

powModOracleExecutionFibre :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (B : Finite.FiniteBasis) →
  (F : QFT.FiniteFourierTransform
    (Oracle.powModGraphRegister B a N (Weld.orderModulusNonZero P))) →
  (b : Finite.Basis B) →
  (cost : Exec.QuantumCostProfile) →
  Exec.FiniteQuantumExecutionFibre
powModOracleExecutionFibre {N} {a} P B F b cost =
  Exec.finiteQuantumExecutionFibre
    B
    register
    circuit
    F
    b
    (Finite.prepare register b)
    refl
    (Finite.run circuit (Finite.prepare register b))
    refl
    b
    refl
    cost
  where
    register : Finite.FiniteQuantumRegister B
    register =
      Oracle.powModGraphRegister B a N (Weld.orderModulusNonZero P)

    circuit : Finite.ReversibleCircuit register
    circuit = Weld.reversiblePowModCircuit P B

powModOracleExecutionLoadsHiddenPeriodValue :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (B : Finite.FiniteBasis) →
  (F : QFT.FiniteFourierTransform
    (Oracle.powModGraphRegister B a N (Weld.orderModulusNonZero P))) →
  (b : Finite.Basis B) →
  (cost : Exec.QuantumCostProfile) →
  Exec.transportedState (powModOracleExecutionFibre P B F b cost)
  ≡
  Oracle.loaded
    b
    (Order.oracle (Order.asHiddenPeriodProblem P) (Finite.encode B b))
    refl
powModOracleExecutionLoadsHiddenPeriodValue P B F b cost =
  Weld.reversiblePowModLoadsHiddenPeriodValue P B b

record ShorPowModExecutionPrefixBoundary : Set where
  constructor shorPowModExecutionPrefixBoundary
  field
    reversiblePowModCircuitIntegrated : Bool
    hiddenPeriodSameObjectPreserved : Bool
    existingExecutionFibreReused : Bool
    fourierTransformManufactured : Bool
    samplingSemanticsManufactured : Bool
    costDerivedFromSuccessEvidence : Bool

canonicalShorPowModExecutionPrefixBoundary : ShorPowModExecutionPrefixBoundary
canonicalShorPowModExecutionPrefixBoundary =
  shorPowModExecutionPrefixBoundary
    true true true false false false
