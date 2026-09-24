module DASHI.ComputerScience.ShorPowModOracleExecutionFibreRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Oracle
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as Weld
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as Exec
import DASHI.ComputerScience.ShorPowModOracleExecutionFibreExact as Adapter

------------------------------------------------------------------------
-- RED regression: the exact reversible powMod circuit should inhabit the
-- existing finite quantum execution fibre without inventing new execution
-- semantics.  Fourier semantics and cost remain explicit inputs.
------------------------------------------------------------------------

oraclePrefixUsesExistingExecutionFibre :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (B : Finite.FiniteBasis) →
  (F : QFT.FiniteFourierTransform
    (Oracle.powModGraphRegister B a N (Weld.orderModulusNonZero P))) →
  (b : Finite.Basis B) →
  (cost : Exec.QuantumCostProfile) →
  Exec.FiniteQuantumExecutionFibre
oraclePrefixUsesExistingExecutionFibre = Adapter.powModOracleExecutionFibre
