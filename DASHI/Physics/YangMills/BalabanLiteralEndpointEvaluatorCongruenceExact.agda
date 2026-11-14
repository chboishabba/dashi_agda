module DASHI.Physics.YangMills.BalabanLiteralEndpointEvaluatorCongruenceExact where

-- Same-source endpoint semantics for the original DiagramExpression AST.
-- The literal recursive interval evaluator is reused without changing
-- its Wilson/ghost/Haar expression or the selected atom environment.
--
-- Equality here means exactly equal rational interval endpoints,
-- not equality of the proof of lower ≤ upper. Operation-level
-- congruence must be established on the selected concrete backend.
-- In particular division is deliberately not granted for free.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Data.Rational.Base as ℚ using (_*_; -_)
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End

-- Strict endpoint equality is stable under arbitrary concrete rational
-- addition and multiplication because the original operations are
-- obtained by endpoint sums and the four products' min/max.
min2Cong : ∀ {a b c d} →
  a ≡ b → c ≡ d → Typed.min2 a c ≡ Typed.min2 b d
min2Cong refl refl = refl

max2Cong : ∀ {a b c d} →
  a ≡ b → c ≡ d → Typed.max2 a c ≡ Typed.max2 b d
max2Cong refl refl = refl

min4Cong : ∀ {a b c d a′ b′ c′ d′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
  Typed.min4 a b c d ≡ Typed.min4 a′ b′ c′ d′
min4Cong refl refl refl refl = refl

max4Cong : ∀ {a b c d a′ b′ c′ d′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
  Typed.max4 a b c d ≡ Typed.max4 a′ b′ c′ d′
max4Cong refl refl refl refl = refl

typedMultiplyStable : ∀ {a b c d} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  End.SameEndpoints
    (Typed.multiplyInterval a c)
    (Typed.multiplyInterval b d)
typedMultiplyStable ab cd = End.sameEndpoints
  (min4Cong
    (cong₂ ℚ._*_ (End.lowerEqual ab) (End.lowerEqual cd))
    (cong₂ ℚ._*_ (End.lowerEqual ab) (End.upperEqual cd))
    (cong₂ ℚ._*_ (End.upperEqual ab) (End.lowerEqual cd))
    (cong₂ ℚ._*_ (End.upperEqual ab) (End.upperEqual cd)))
  (max4Cong
    (cong₂ ℚ._*_ (End.lowerEqual ab) (End.lowerEqual cd))
    (cong₂ ℚ._*_ (End.lowerEqual ab) (End.upperEqual cd))
    (cong₂ ℚ._*_ (End.upperEqual ab) (End.lowerEqual cd))
    (cong₂ ℚ._*_ (End.upperEqual ab) (End.upperEqual cd)))

typedNegateStable : ∀ {a b} →
  End.SameEndpoints a b →
  End.SameEndpoints (Typed.negateInterval a) (Typed.negateInterval b)
typedNegateStable ab = End.sameEndpoints
  (cong ℚ.-_ (End.upperEqual ab))
  (cong ℚ.-_ (End.lowerEqual ab))

typedSubtractStable : ∀ {a b c d} →
  End.SameEndpoints a b → End.SameEndpoints c d →
  End.SameEndpoints
    (Typed.subtractInterval a c) (Typed.subtractInterval b d)
typedSubtractStable ab cd =
  End.addCongruence ab (typedNegateStable cd)

-- Selected RationalIntervalArithmetic lacks such congruence fields.
-- Keep them as explicit requirements rather than silently treating
-- soundness of an operation as equality-respectfulness.
record EndpointStableBackend
  (arithmetic : Eval.RationalIntervalArithmetic) : Set₁ where
  field
    addStable : ∀ {a b c d} →
      End.SameEndpoints a b → End.SameEndpoints c d →
      End.SameEndpoints (Eval.addInterval arithmetic a c)
                        (Eval.addInterval arithmetic b d)
    subtractStable : ∀ {a b c d} →
      End.SameEndpoints a b → End.SameEndpoints c d →
      End.SameEndpoints (Eval.subtractInterval arithmetic a c)
                        (Eval.subtractInterval arithmetic b d)
    multiplyStable : ∀ {a b c d} →
      End.SameEndpoints a b → End.SameEndpoints c d →
      End.SameEndpoints (Eval.multiplyInterval arithmetic a c)
                        (Eval.multiplyInterval arithmetic b d)
    divideStable : ∀ {a b c d} →
      End.SameEndpoints a b → End.SameEndpoints c d →
      End.SameEndpoints (Eval.divideInterval arithmetic a c)
                        (Eval.divideInterval arithmetic b d)
    negateStable : ∀ {a b} →
      End.SameEndpoints a b →
      End.SameEndpoints (Eval.negateInterval arithmetic a)
                        (Eval.negateInterval arithmetic b)
open EndpointStableBackend public

-- Original expression recursion. This theorem handles ALL original
-- constructors, including DIVIDE, only when its actual backend
-- provides the independent endpoint congruence certificate.
record AtomEndpointAgreement
  (source target : Eval.BoxTrigEnvironment) : Set where
  field
    atomAgree : ∀ atom →
      End.SameEndpoints
        (Eval.atomInterval source atom)
        (Eval.atomInterval target atom)
open AtomEndpointAgreement public

expressionEndpointEnvironmentCongruence :
  (arithmetic : Eval.RationalIntervalArithmetic) →
  EndpointStableBackend arithmetic →
  (source target : Eval.BoxTrigEnvironment) →
  AtomEndpointAgreement source target →
  (expression : Eval.DiagramExpression) →
  End.SameEndpoints
    (Eval.evaluateExpression arithmetic source expression)
    (Eval.evaluateExpression arithmetic target expression)
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.rationalConstant _) =
  End.endpointsRefl _
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.atom atom) =
  atomAgree agreement atom
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.add left right) =
  addStable backend
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement left)
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement right)
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.subtract left right) =
  subtractStable backend
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement left)
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement right)
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.multiply left right) =
  multiplyStable backend
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement left)
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement right)
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.divide left right) =
  divideStable backend
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement left)
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement right)
expressionEndpointEnvironmentCongruence arithmetic backend
  source target agreement (Eval.negate expression) =
  negateStable backend
    (expressionEndpointEnvironmentCongruence arithmetic backend
      source target agreement expression)

-- The actual original regular integrand, not a proxy expression.
literalRegularIntegrandEndpointTransport :
  ∀ {expressions ward}
  (scalar : Eval.LiteralScalarIntegrandExpression expressions ward)
  (arithmetic : Eval.RationalIntervalArithmetic)
  (backend : EndpointStableBackend arithmetic)
  (source target : Eval.BoxTrigEnvironment) →
  AtomEndpointAgreement source target →
  End.SameEndpoints
    (Eval.evaluateExpression arithmetic source
      (Eval.regularIntegrand scalar))
    (Eval.evaluateExpression arithmetic target
      (Eval.regularIntegrand scalar))
literalRegularIntegrandEndpointTransport scalar arithmetic backend
  source target atoms =
  expressionEndpointEnvironmentCongruence arithmetic backend
    source target atoms (Eval.regularIntegrand scalar)

-- Precise remaining proof: the actual source B4 generator generally
-- TRANSFORMS atoms (sine signs, axis permutations), so this same-atom
-- environment transport is not itself the full seven-generator lemma.
