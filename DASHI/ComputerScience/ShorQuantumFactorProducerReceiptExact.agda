module DASHI.ComputerScience.ShorQuantumFactorProducerReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.ShorQuantumRunFactorTransportExact as QuantumFactor
import DASHI.ComputerScience.FactorProducerReceiptExact as Receipt
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as Exec
import DASHI.ComputerScience.ShorCertifiedRunExecutionFibreExact as RunFibre

------------------------------------------------------------------------
-- CERTIFIED SHOR RUN -> EXISTING FACTOR-PRODUCER RECEIPT
--
-- The repository already owns the cross-producer receipt ontology.  This file
-- only compiles an actual certified Shor factoring run into that existing
-- carrier, using the recovered-order factor path rather than the old
-- run-ignoring factoring definition.
------------------------------------------------------------------------

quantumShorRunFactorReceipt :
  ∀ {N} →
  (P : Shor.ShorFactoringProblem N) →
  Shor.QuantumShorFactoringRun P →
  Receipt.FactorProducerReceipt
quantumShorRunFactorReceipt {N} P R
  with QuantumFactor.quantumShorFactorFromRecoveredOrder P R
... | d , C =
  Receipt.factorProducerReceipt
    (Receipt.certifiedFactorEvidence N d C)
    Receipt.quantumShorProducer
    Receipt.kernelFactorCertificate
    Receipt.executionPathKnown
    Receipt.partialCostReceipt
    "DASHI.Crypto.ShorQuantumRunFactorTransportExact.quantumShorFactorFromRecoveredOrder"
    "certified Shor order-finding run; recovered order transported into certified split"
    "quantum cost coordinates remain supplied by the separate quantum execution fibre"

quantumShorRunReceiptProducerClass :
  ∀ {N} →
  (P : Shor.ShorFactoringProblem N) →
  (R : Shor.QuantumShorFactoringRun P) →
  Receipt.producerClass (quantumShorRunFactorReceipt P R)
  ≡ Receipt.quantumShorProducer
quantumShorRunReceiptProducerClass {N} P R
  with QuantumFactor.quantumShorFactorFromRecoveredOrder P R
... | d , C = refl

------------------------------------------------------------------------
-- The same certified run also lands in the existing execution/cost fibre.
-- The factor receipt and execution fibre intentionally remain distinct
-- projections of one run: equal arithmetic output does not identify costs or
-- execution semantics.
------------------------------------------------------------------------

quantumShorRunExecutionFibre :
  ∀ {N} →
  (P : Shor.ShorFactoringProblem N) →
  (R : Shor.QuantumShorFactoringRun P) →
  Exec.QuantumCostProfile →
  Exec.ShorExecutionFibre
    (Shor.asHiddenPeriodProblem (Shor.modularOrderProblem R))
quantumShorRunExecutionFibre P R cost =
  RunFibre.certifiedOrderFindingRunExecutionFibre
    (Shor.modularOrderProblem R)
    (Shor.orderFindingRun R)
    cost
