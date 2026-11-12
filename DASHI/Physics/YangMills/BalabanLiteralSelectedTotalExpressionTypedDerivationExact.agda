module DASHI.Physics.YangMills.BalabanLiteralSelectedTotalExpressionTypedDerivationExact where

-- Original recursive DiagramExpression + original proof-producing
-- Typed.ExpressionInterval derivation. Shows the newly selected total
-- backend EVALUATES TO THE SAME ACTUAL INTERVAL as the original
-- positive-indexed typed derivation at every AST constructor.
--
-- The quotient clause consumes the existing original denominator
-- strict-positivity witness, never the zero fallback.
-- This theorem does not produce the original source's physical derivation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralTotalRationalBackendExact as Selected

selectedTotalRecursionIdentifiesTypedDerivation :
  (environment : Eval.BoxTrigEnvironment) →
  ∀ {expression box} →
  Typed.ExpressionInterval (Eval.atomInterval environment) expression box →
  Eval.evaluateExpression Selected.selectedArithmetic environment expression
    ≡ box
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.constant value) = refl
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.trig atom) = refl
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.plus left right)
  rewrite selectedTotalRecursionIdentifiesTypedDerivation environment left
        | selectedTotalRecursionIdentifiesTypedDerivation environment right
  = refl
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.minus left right)
  rewrite selectedTotalRecursionIdentifiesTypedDerivation environment left
        | selectedTotalRecursionIdentifiesTypedDerivation environment right
  = refl
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.times left right)
  rewrite selectedTotalRecursionIdentifiesTypedDerivation environment left
        | selectedTotalRecursionIdentifiesTypedDerivation environment right
  = refl
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.quotient numerator denominator positive)
  rewrite selectedTotalRecursionIdentifiesTypedDerivation environment numerator
        | selectedTotalRecursionIdentifiesTypedDerivation environment denominator
  = Selected.totalDivideEqualsTypedWhenPositive _ _ positive
selectedTotalRecursionIdentifiesTypedDerivation environment
  (Typed.negative value)
  rewrite selectedTotalRecursionIdentifiesTypedDerivation environment value
  = refl

-- Contract: construct the corresponding actual source-owned Typed.ExpressionInterval
-- derivation for Eval.regularIntegrand scalarData by recursively enclosing
-- its trigonometric atoms and paying all quotient denominator proofs.
-- The theorem then yields the EXACT original recursive evaluator result.
selectedLiteralRegularExpressionIdentified :
  ∀ {expressions ward}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward)
    (environment : Eval.BoxTrigEnvironment)
    (box : Eval.RationalInterval) →
  Typed.ExpressionInterval
    (Eval.atomInterval environment)
    (Eval.regularIntegrand scalarData) box →
  Eval.evaluateExpression Selected.selectedArithmetic environment
    (Eval.regularIntegrand scalarData) ≡ box
selectedLiteralRegularExpressionIdentified scalarData environment box derivation =
  selectedTotalRecursionIdentifiesTypedDerivation environment derivation
