module DASHI.ComputerScience.ShorQuantumFactorProducerReceiptRegression where

open import DASHI.ComputerScience.ShorQuantumFactorProducerReceiptExact

------------------------------------------------------------------------
-- Regression surface: an actual certified Shor factoring run must compile to
-- the already-canonical factor-producer receipt fibre via recovered-order
-- factor extraction, without inventing a second receipt ontology.
------------------------------------------------------------------------

import DASHI.Crypto.ShorFactoring as Shor
import DASHI.ComputerScience.FactorProducerReceiptExact as Receipt

quantumRunReceiptRegression :
  ∀ {N} →
  (P : Shor.ShorFactoringProblem N) →
  Shor.QuantumShorFactoringRun P →
  Receipt.FactorProducerReceipt
quantumRunReceiptRegression = quantumShorRunFactorReceipt
