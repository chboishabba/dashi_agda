module DASHI.Physics.YangMills.BalabanLiteralSemanticGeneratorTransportExact where

-- Original DASHI P0 bridge: semantic evaluation equality, not an
-- equality between raw ordered DiagramExpression syntax trees.
-- Source inputs: the real literal AST, original recursive interval
-- evaluator, joint momentum action, and atom covariance theorem.
--
-- This module proves the algebraic assembly. It does NOT assert that
-- interval addition is commutative for every arithmetic backend, that
-- the actual four Wilson/ghost/Haar terms have been normalized, or
-- that any chosen physical scalar already satisfies these hypotheses.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact as Transport
import DASHI.Physics.YangMills.BalabanLiteralExpressionSyntaxPermutationBoundaryExact as Negative

-- An evaluator equality is a *semantic* relation for a chosen backend
-- and box environment. It is not a quotient of the source syntax.
SemanticInvariant :
  (arithmetic : Eval.RationalIntervalArithmetic) →
  (environment : Eval.BoxTrigEnvironment) →
  Orbit.HyperoctahedralGenerator →
  Eval.DiagramExpression → Set
SemanticInvariant arithmetic environment generator expression =
  Eval.evaluateExpression arithmetic environment
    (Joint.transformExpression generator expression)
  ≡ Eval.evaluateExpression arithmetic environment expression

-- Given actual atom/environment covariance and a semantic
-- generator certificate in the TARGET environment, the original
-- recursive evaluator has identical interval values on paired boxes.
semanticGeneratorBoxTransport :
  (arithmetic : Eval.RationalIntervalArithmetic) →
  (generator : Orbit.HyperoctahedralGenerator) →
  (source target : Eval.BoxTrigEnvironment) →
  (expression : Eval.DiagramExpression) →
  Transport.GeneratorEnvironmentCompatibility
    arithmetic generator source target →
  SemanticInvariant arithmetic target generator expression →
  Eval.evaluateExpression arithmetic target expression
    ≡ Eval.evaluateExpression arithmetic source expression
semanticGeneratorBoxTransport arithmetic generator source target
  expression compatible semantic =
  trans (sym semantic)
    (Transport.transformEvaluationExact compatible expression)

-- Exact counterexample repair on the already established AST boundary.
-- Swapping axis0/axis1 yields a reversed ADD TREE. If the *selected*
-- interval-arithmetic backend actually has commutative addition, its
-- EVALUATION is equal even though raw AST equality is impossible.
cosinePairSemanticallySwapInvariant :
  (arithmetic : Eval.RationalIntervalArithmetic) →
  (environment : Eval.BoxTrigEnvironment) →
  (addCommutative :
    (x y : Eval.RationalInterval) →
    Eval.addInterval arithmetic x y
      ≡ Eval.addInterval arithmetic y x) →
  SemanticInvariant arithmetic environment Orbit.swap01
    Negative.axis01CosinePair
cosinePairSemanticallySwapInvariant arithmetic environment addCommutative =
  addCommutative
    (Eval.atomInterval environment
      (Eval.cosineFull Eval.loopMomentum Eval.axis1))
    (Eval.atomInterval environment
      (Eval.cosineFull Eval.loopMomentum Eval.axis0))

-- Actual cosine-pair box transport, using BOTH independently paid
-- premises: original finite-atom environmental covariance and the
-- selected interval addition's semantic commutativity.
cosinePairPairedBoxesAgree :
  (arithmetic : Eval.RationalIntervalArithmetic) →
  (source target : Eval.BoxTrigEnvironment) →
  (compatible : Transport.GeneratorEnvironmentCompatibility
    arithmetic Orbit.swap01 source target) →
  (addCommutative :
    (x y : Eval.RationalInterval) →
    Eval.addInterval arithmetic x y
      ≡ Eval.addInterval arithmetic y x) →
  Eval.evaluateExpression arithmetic target Negative.axis01CosinePair
    ≡ Eval.evaluateExpression arithmetic source Negative.axis01CosinePair
cosinePairPairedBoxesAgree arithmetic source target compatible addCommutative =
  semanticGeneratorBoxTransport arithmetic Orbit.swap01 source target
    Negative.axis01CosinePair compatible
    (cosinePairSemanticallySwapInvariant
      arithmetic target addCommutative)

-- The most important source-specific open leaf is still to construct
-- SemanticInvariant on Eval.regularIntegrand scalarData for all seven
-- actual generators, plus environment compatibility on generated boxes.
-- This example is NOT the complete source scalar certificate.
