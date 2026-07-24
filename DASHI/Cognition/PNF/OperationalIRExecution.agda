module DASHI.Cognition.PNF.OperationalIRExecution where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.OperationalIR as IR

record IRRule : Set₁ where
  constructor irRule
  field
    ruleId : String
    AppliesTo : IR.DomainIR → Set
    renderOutput : IR.DomainIR → String

open IRRule public

executeOperationalIR :
  (rule : IRRule) →
  (input : IR.DomainIR) →
  IR.validationState input ≡ IR.operationallyValid →
  AppliesTo rule input →
  String →
  IR.IRExecutionReceipt
executeOperationalIR rule input valid applies receiptId =
  IR.irExecutionReceipt
    input
    (ruleId rule)
    (renderOutput rule input)
    IR.executed
    ("operational validity witnessed" ∷ "rule applicability witnessed" ∷ [])
    receiptId

refuseInvalidIR :
  (input : IR.DomainIR) →
  String →
  String →
  IR.IRExecutionReceipt
refuseInvalidIR input reason receiptId =
  IR.irExecutionReceipt
    input
    "fail-closed IR gate"
    "no operational output"
    IR.refused
    (reason ∷ [])
    receiptId

record RuleExecutionBoundary : Set where
  constructor ruleExecutionBoundary
  field
    semanticSimilarityAloneExecutesRule : Bool
    semanticSimilarityAloneExecutesRuleIsFalse :
      semanticSimilarityAloneExecutesRule ≡ false
    validIRAndApplicabilityWitnessRequired : Bool
    validIRAndApplicabilityWitnessRequiredIsTrue :
      validIRAndApplicabilityWitnessRequired ≡ true

canonicalRuleExecutionBoundary : RuleExecutionBoundary
canonicalRuleExecutionBoundary =
  ruleExecutionBoundary false refl true refl
