module DASHI.ComputerScience.ShorCertifiedRunExecutionFibreExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as Exec

------------------------------------------------------------------------
-- Certified modular order-finding run -> existing quantum execution fibre.
--
-- This is deliberately an adapter, not a new execution semantics.  The seed,
-- sample, success evidence and recovered-order theorem all come from the
-- existing `CertifiedOrderFindingRun`; the cost profile is supplied separately
-- because successful execution evidence does not by itself determine a gate or
-- depth accounting.
------------------------------------------------------------------------

certifiedOrderFindingRunExecutionFibre :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (R : Order.CertifiedOrderFindingRun P) →
  Exec.QuantumCostProfile →
  Exec.ShorExecutionFibre (Order.asHiddenPeriodProblem P)
certifiedOrderFindingRunExecutionFibre P R cost = record
  { machine = Order.machine R
  ; seed = Shor.seed (Order.successEvidence R)
  ; sample =
      Shor.periodExecute
        (Order.machine R)
        (Shor.seed (Order.successEvidence R))
  ; sampleExact = refl
  ; successful = Shor.success (Order.successEvidence R)
  ; recovered =
      Shor.recoverPeriod
        (Order.machine R)
        (Shor.periodExecute
          (Order.machine R)
          (Shor.seed (Order.successEvidence R)))
  ; recoveredExact = refl
  ; recoveredPeriodExact = Order.orderFindingRecoversExactOrder P R
  ; cost = cost
  }
