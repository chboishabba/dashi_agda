module DASHI.Physics.YangMills.BalabanLiteralRecursivePositiveDivisionCompilerExact where

-- Executable rational-positivity admission for EVERY actual division node
-- of the original Eval.DiagramExpression.
--
-- A successful checker result constructs an ORIGINAL Typed.ExpressionInterval
-- derivation automatically. In particular, it uses Typed.quotient only after
-- proving that the recursively evaluated denominator interval has a
-- STRICTLY POSITIVE lower rational endpoint.
--
-- No postulates, generic division axioms, or substitute source expression.
-- This does NOT produce physical sine/cosine atom enclosures.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (0ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralTotalRationalBackendExact as Selected

-- The proposition inspected by the executable checker is tied to the
-- SAME original source environment and original recursive evaluator.
data AllDivisionsPositive
    (environment : Eval.BoxTrigEnvironment) :
    Eval.DiagramExpression → Set where
  constantPositive : ∀ value →
    AllDivisionsPositive environment (Eval.rationalConstant value)

  atomPositive : ∀ atom →
    AllDivisionsPositive environment (Eval.atom atom)

  addPositive : ∀ {left right} →
    AllDivisionsPositive environment left →
    AllDivisionsPositive environment right →
    AllDivisionsPositive environment (Eval.add left right)

  subtractPositive : ∀ {left right} →
    AllDivisionsPositive environment left →
    AllDivisionsPositive environment right →
    AllDivisionsPositive environment (Eval.subtract left right)

  multiplyPositive : ∀ {left right} →
    AllDivisionsPositive environment left →
    AllDivisionsPositive environment right →
    AllDivisionsPositive environment (Eval.multiply left right)

  dividePositive : ∀ {numerator denominator} →
    AllDivisionsPositive environment numerator →
    AllDivisionsPositive environment denominator →
    (0ℚ < Eval.lower
      (Eval.evaluateExpression Selected.selectedArithmetic
        environment denominator)) →
    AllDivisionsPositive environment (Eval.divide numerator denominator)

  negatePositive : ∀ {expression} →
    AllDivisionsPositive environment expression →
    AllDivisionsPositive environment (Eval.negate expression)

-- Turn the POSITIVE node certificates into original typed derivations.
-- The quotient branch uses 'subst' to rewrite from the original typed
-- quotient interval to the *extensionally identical* selected total
-- evaluator interval; nonpositive fallback is never taken.

compilePositiveDerivation :
  (environment : Eval.BoxTrigEnvironment) →
  ∀ {expression} →
  AllDivisionsPositive environment expression →
  Typed.ExpressionInterval
    (Eval.atomInterval environment)
    expression
    (Eval.evaluateExpression Selected.selectedArithmetic
      environment expression)
compilePositiveDerivation environment (constantPositive value) =
  Typed.constant value
compilePositiveDerivation environment (atomPositive atom) =
  Typed.trig atom
compilePositiveDerivation environment (addPositive left right) =
  Typed.plus
    (compilePositiveDerivation environment left)
    (compilePositiveDerivation environment right)
compilePositiveDerivation environment (subtractPositive left right) =
  Typed.minus
    (compilePositiveDerivation environment left)
    (compilePositiveDerivation environment right)
compilePositiveDerivation environment (multiplyPositive left right) =
  Typed.times
    (compilePositiveDerivation environment left)
    (compilePositiveDerivation environment right)
compilePositiveDerivation environment
  (dividePositive {numerator} {denominator} numeratorProof denominatorProof positive) =
  let
    numeratorBox =
      Eval.evaluateExpression Selected.selectedArithmetic environment numerator
    denominatorBox =
      Eval.evaluateExpression Selected.selectedArithmetic environment denominator
    typedCertificate = Typed.quotient
      (compilePositiveDerivation environment numeratorProof)
      (compilePositiveDerivation environment denominatorProof)
      positive
    equal = Selected.totalDivideEqualsTypedWhenPositive
      numeratorBox denominatorBox positive
  in
  subst
    (Typed.ExpressionInterval
      (Eval.atomInterval environment)
      (Eval.divide numerator denominator))
    (sym equal)
    typedCertificate
compilePositiveDerivation environment (negatePositive proof) =
  Typed.negative (compilePositiveDerivation environment proof)

-- Decision procedure on original AST syntax.
-- On failure, returns a refutation of the exact proposition at that
-- expression node. Thus "unchecked" does not count as "positive".

pairAdd? :
  ∀ environment left right →
  Dec (AllDivisionsPositive environment left) →
  Dec (AllDivisionsPositive environment right) →
  Dec (AllDivisionsPositive environment (Eval.add left right))
pairAdd? environment left right (yes lp) (yes rp) =
  yes (addPositive lp rp)
pairAdd? environment left right (no notL) _ =
  no (λ { (addPositive lp _) → notL lp })
pairAdd? environment left right (yes _) (no notR) =
  no (λ { (addPositive _ rp) → notR rp })

pairSubtract? :
  ∀ environment left right →
  Dec (AllDivisionsPositive environment left) →
  Dec (AllDivisionsPositive environment right) →
  Dec (AllDivisionsPositive environment (Eval.subtract left right))
pairSubtract? environment left right (yes lp) (yes rp) =
  yes (subtractPositive lp rp)
pairSubtract? environment left right (no notL) _ =
  no (λ { (subtractPositive lp _) → notL lp })
pairSubtract? environment left right (yes _) (no notR) =
  no (λ { (subtractPositive _ rp) → notR rp })

pairMultiply? :
  ∀ environment left right →
  Dec (AllDivisionsPositive environment left) →
  Dec (AllDivisionsPositive environment right) →
  Dec (AllDivisionsPositive environment (Eval.multiply left right))
pairMultiply? environment left right (yes lp) (yes rp) =
  yes (multiplyPositive lp rp)
pairMultiply? environment left right (no notL) _ =
  no (λ { (multiplyPositive lp _) → notL lp })
pairMultiply? environment left right (yes _) (no notR) =
  no (λ { (multiplyPositive _ rp) → notR rp })

pairDivide? :
  ∀ environment numerator denominator →
  Dec (AllDivisionsPositive environment numerator) →
  Dec (AllDivisionsPositive environment denominator) →
  Dec (0ℚ < Eval.lower
    (Eval.evaluateExpression Selected.selectedArithmetic
      environment denominator)) →
  Dec (AllDivisionsPositive environment
    (Eval.divide numerator denominator))
pairDivide? environment numerator denominator
  (yes np) (yes dp) (yes positive) =
  yes (dividePositive np dp positive)
pairDivide? environment numerator denominator
  (no notN) _ _ =
  no (λ { (dividePositive np _ _) → notN np })
pairDivide? environment numerator denominator
  (yes _) (no notD) _ =
  no (λ { (dividePositive _ dp _) → notD dp })
pairDivide? environment numerator denominator
  (yes _) (yes _) (no notPositive) =
  no (λ { (dividePositive _ _ p) → notPositive p })

negate? : ∀ environment expression →
  Dec (AllDivisionsPositive environment expression) →
  Dec (AllDivisionsPositive environment (Eval.negate expression))
negate? environment expression (yes certificate) =
  yes (negatePositive certificate)
negate? environment expression (no contradiction) =
  no (λ { (negatePositive certificate) → contradiction certificate })

checkAllDivisionsPositive :
  (environment : Eval.BoxTrigEnvironment) →
  (expression : Eval.DiagramExpression) →
  Dec (AllDivisionsPositive environment expression)
checkAllDivisionsPositive environment (Eval.rationalConstant value) =
  yes (constantPositive value)
checkAllDivisionsPositive environment (Eval.atom atom) =
  yes (atomPositive atom)
checkAllDivisionsPositive environment (Eval.add left right) =
  pairAdd? environment left right
    (checkAllDivisionsPositive environment left)
    (checkAllDivisionsPositive environment right)
checkAllDivisionsPositive environment (Eval.subtract left right) =
  pairSubtract? environment left right
    (checkAllDivisionsPositive environment left)
    (checkAllDivisionsPositive environment right)
checkAllDivisionsPositive environment (Eval.multiply left right) =
  pairMultiply? environment left right
    (checkAllDivisionsPositive environment left)
    (checkAllDivisionsPositive environment right)
checkAllDivisionsPositive environment (Eval.divide numerator denominator) =
  pairDivide? environment numerator denominator
    (checkAllDivisionsPositive environment numerator)
    (checkAllDivisionsPositive environment denominator)
    (ℚP._<?_ 0ℚ
      (Eval.lower
        (Eval.evaluateExpression Selected.selectedArithmetic
          environment denominator)))
checkAllDivisionsPositive environment (Eval.negate expression) =
  negate? environment expression
    (checkAllDivisionsPositive environment expression)

-- The actual source literal is accepted only if EVERY literal
-- denominator node passes the exact rational check. This removes the
-- old need to postulate one typed derivation per source expression.
literalRegularPositiveDerivation :
  ∀ {expressions ward}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward)
    (environment : Eval.BoxTrigEnvironment) →
  AllDivisionsPositive environment (Eval.regularIntegrand scalarData) →
  Typed.ExpressionInterval
    (Eval.atomInterval environment)
    (Eval.regularIntegrand scalarData)
    (Eval.evaluateExpression Selected.selectedArithmetic
      environment (Eval.regularIntegrand scalarData))
literalRegularPositiveDerivation scalarData environment proof =
  compilePositiveDerivation environment proof
