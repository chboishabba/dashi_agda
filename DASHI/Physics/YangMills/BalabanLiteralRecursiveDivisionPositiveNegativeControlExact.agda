module DASHI.Physics.YangMills.BalabanLiteralRecursiveDivisionPositiveNegativeControlExact where

-- Exact original-AST regression:
--   1/1 is admitted by the recursive typed denominator compiler;
--   1/0 is REFUTED. The total backend's explicit zero fallback
-- cannot be misreported as a positive-denominator source certificate.
--
-- No physical trigonometric atoms are needed for this negative control.
-- It does not instantiate the full literal Yang-Mills scalar.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (0ℚ; 1ℚ; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralTotalRationalBackendExact as Selected
import DASHI.Physics.YangMills.BalabanLiteralRecursivePositiveDivisionCompilerExact as Compiler

oneOverOne : Eval.DiagramExpression
oneOverOne = Eval.divide
  (Eval.rationalConstant 1ℚ)
  (Eval.rationalConstant 1ℚ)

oneOverZero : Eval.DiagramExpression
oneOverZero = Eval.divide
  (Eval.rationalConstant 1ℚ)
  (Eval.rationalConstant 0ℚ)

oneOverOneHasPositiveTypedWitness :
  ∀ environment →
  Compiler.AllDivisionsPositive environment oneOverOne
oneOverOneHasPositiveTypedWitness environment =
  Compiler.dividePositive
    (Compiler.constantPositive 1ℚ)
    (Compiler.constantPositive 1ℚ)
    (ℚP.positive⁻¹ 1ℚ)

oneOverOneOriginalTypedDerivation :
  ∀ environment →
  Typed.ExpressionInterval
    (Eval.atomInterval environment)
    oneOverOne
    (Eval.evaluateExpression Selected.selectedArithmetic
      environment oneOverOne)
oneOverOneOriginalTypedDerivation environment =
  Compiler.compilePositiveDerivation environment
    (oneOverOneHasPositiveTypedWitness environment)

oneOverZeroHasNoPositiveTypedWitness :
  ∀ environment →
  Compiler.AllDivisionsPositive environment oneOverZero →
  ⊥
oneOverZeroHasNoPositiveTypedWitness environment
  (Compiler.dividePositive _ _ positive) =
  ℚP.<-irrefl refl positive

-- If the selected total backend returns [0,0] for a zero denominator,
-- the failed branch is intentionally NOT accepted by AllDivisionsPositive.
