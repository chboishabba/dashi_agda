module DASHI.ComputerScience.ShorCertifiedRunExecutionFibreRegression where

open import DASHI.ComputerScience.ShorCertifiedRunExecutionFibreExact

------------------------------------------------------------------------
-- Regression surface: a certified modular order-finding run must retain its
-- exact executed seed/sample and recovered-order proof when viewed through the
-- existing quantum execution-fibre/cost interface.
------------------------------------------------------------------------

open import DASHI.Crypto.ShorOrderFinding
open import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact

certifiedRunExecutionFibreRegression :
  ∀ {N a r} →
  (P : ModularOrderProblem N a r) →
  (R : CertifiedOrderFindingRun P) →
  QuantumCostProfile →
  ShorExecutionFibre (asHiddenPeriodProblem P)
certifiedRunExecutionFibreRegression = certifiedOrderFindingRunExecutionFibre
