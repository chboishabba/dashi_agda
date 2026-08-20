module DASHI.Core.ConsumerSafeFidelityEscalationExact where

------------------------------------------------------------------------
-- CONSUMER-SAFE FIDELITY ESCALATION
--
-- AdaptiveFidelityConsumerMarginExact proves the positive theorem:
-- certified discrepancy inside a decision-stable margin => the low- and
-- high-fidelity decisions agree.  This module adds the complementary typed
-- execution rule: absence of that proof creates an escalation obligation, not
-- evidence that the low-fidelity answer is false.
--
-- Literature calibration:
-- Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon,
-- "A trust-region framework for managing the use of approximation models in
-- optimization", Structural Optimization 15 (1998), 16-23.
-- DOI: 10.1007/BF01197433.
-- Marc C. Kennedy and Anthony O'Hagan,
-- "Predicting the output from a complex computer code when fast approximations
-- are available", Biometrika 87(1), 2000. DOI: 10.1093/biomet/87.1.1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity

------------------------------------------------------------------------
-- Per-input evidence: either we possess a decision-invariance proof for this
-- low/high pair or we possess a proof that such a margin certificate is not
-- currently available under the declared relation.
------------------------------------------------------------------------

data FidelityDecisionAt
    {Input Summary Decision : Set}
    (pair : Fidelity.FidelityPair Input Summary)
    (decide : Summary → Decision)
    (margin : Fidelity.ConsumerDecisionMargin decide)
    (input : Input) : Set where
  certifiedLow :
    Fidelity.InsideMargin margin
      (Fidelity.low pair input)
      (Fidelity.high pair input) →
    FidelityDecisionAt pair decide margin input
  mustEscalate :
    (Fidelity.InsideMargin margin
      (Fidelity.low pair input)
      (Fidelity.high pair input) → ⊥) →
    FidelityDecisionAt pair decide margin input

certifiedLowPreservesDecision :
  ∀ {Input Summary Decision}
    {pair : Fidelity.FidelityPair Input Summary}
    {decide : Summary → Decision}
    {margin : Fidelity.ConsumerDecisionMargin decide}
    {input : Input} →
  Fidelity.InsideMargin margin
    (Fidelity.low pair input)
    (Fidelity.high pair input) →
  decide (Fidelity.low pair input)
  ≡ decide (Fidelity.high pair input)
certifiedLowPreservesDecision {margin = margin} inside =
  Fidelity.decisionStable margin inside

------------------------------------------------------------------------
-- The execution disposition is proof-relevant.  Escalation has no constructor
-- carrying a refutation of the low-fidelity result.
------------------------------------------------------------------------

data FidelityExecutionDisposition : Set where
  useLow : FidelityExecutionDisposition
  runHigh : FidelityExecutionDisposition

dispositionFromEvidence :
  ∀ {Input Summary Decision}
    {pair : Fidelity.FidelityPair Input Summary}
    {decide : Summary → Decision}
    {margin : Fidelity.ConsumerDecisionMargin decide}
    {input : Input} →
  FidelityDecisionAt pair decide margin input →
  FidelityExecutionDisposition
dispositionFromEvidence (certifiedLow inside) = useLow
dispositionFromEvidence (mustEscalate missing) = runHigh

record FidelityEscalationBoundary : Set where
  constructor fidelityEscalationBoundary
  field
    escalationIsInformationObligation : Agda.Builtin.Bool.Bool
    escalationDoesNotRefuteLowFidelity : Agda.Builtin.Bool.Bool
    acceptedLowRequiresDecisionMarginEvidence : Agda.Builtin.Bool.Bool

canonicalFidelityEscalationBoundary : FidelityEscalationBoundary
canonicalFidelityEscalationBoundary =
  fidelityEscalationBoundary
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
