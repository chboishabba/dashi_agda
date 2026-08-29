module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact where

------------------------------------------------------------------------
-- CROSS-POLLINATED FROM PR #574 / ROUND57
--
-- METHOD / PHYSICAL CONTEXT
--
-- Stefano Capitani,
-- "Lattice Perturbation Theory", Physics Reports 382 (2003), 113--302.
-- DOI: 10.1016/S0370-1573(03)00211-4.  arXiv: hep-lat/0211036.
--
-- Martin Luescher and Peter Weisz,
-- "Coordinate space methods for the evaluation of Feynman diagrams in
-- lattice field theories", Nuclear Physics B 445 (1995), 429--450.
-- DOI: 10.1016/0550-3213(95)00185-U.  arXiv: hep-lat/9502017.
--
-- DASHI CONTRIBUTION
--
-- A hypercubic generator acts on the literal DiagramExpression, while the
-- target box supplies transformed trigonometric atom bounds.  Compatibility on
-- the finite TrigAtom vocabulary is enough: structural recursion proves that
-- evaluating the transformed complete expression on the transformed box gives
-- exactly the same RationalInterval as evaluating the source expression on the
-- source box.
--
-- This transports the SAME recursive evaluator; it does not assign equal
-- opaque receipts by orbit label.  Therefore L3's physical analytic surface is
-- primitive generated-box atom covariance plus literal source equivariance,
-- not 240 unrelated whole-expression interval proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint

record GeneratorEnvironmentCompatibility
    (arithmetic : Eval.RationalIntervalArithmetic)
    (generator : Orbit.HyperoctahedralGenerator)
    (source target : Eval.BoxTrigEnvironment) : Set₁ where
  field
    transformedAtomEvaluationExact : ∀ trigAtom →
      Eval.evaluateExpression arithmetic target
        (Joint.transformAtom generator trigAtom)
      ≡ Eval.evaluateExpression arithmetic source (Eval.atom trigAtom)
open GeneratorEnvironmentCompatibility public

transformEvaluationExact :
  ∀ {arithmetic generator source target} →
  GeneratorEnvironmentCompatibility arithmetic generator source target →
  (expression : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic target
    (Joint.transformExpression generator expression)
  ≡ Eval.evaluateExpression arithmetic source expression
transformEvaluationExact compatibility (Eval.rationalConstant value) = refl
transformEvaluationExact compatibility (Eval.atom trigAtom) =
  transformedAtomEvaluationExact compatibility trigAtom
transformEvaluationExact compatibility (Eval.add left right)
  rewrite transformEvaluationExact compatibility left
        | transformEvaluationExact compatibility right = refl
transformEvaluationExact compatibility (Eval.subtract left right)
  rewrite transformEvaluationExact compatibility left
        | transformEvaluationExact compatibility right = refl
transformEvaluationExact compatibility (Eval.multiply left right)
  rewrite transformEvaluationExact compatibility left
        | transformEvaluationExact compatibility right = refl
transformEvaluationExact compatibility (Eval.divide numerator denominator)
  rewrite transformEvaluationExact compatibility numerator
        | transformEvaluationExact compatibility denominator = refl
transformEvaluationExact compatibility (Eval.negate value)
  rewrite transformEvaluationExact compatibility value = refl

invariantExpressionEvaluationTransport :
  ∀ {arithmetic generator source target expression} →
  GeneratorEnvironmentCompatibility arithmetic generator source target →
  Joint.transformExpression generator expression ≡ expression →
  Eval.evaluateExpression arithmetic target expression
  ≡ Eval.evaluateExpression arithmetic source expression
invariantExpressionEvaluationTransport
  {arithmetic} {generator} {source} {target} {expression}
  compatibility invariantExact
  rewrite invariantExact = transformEvaluationExact compatibility expression

record LiteralGeneratorBoxTransport
    {expressions : Eval.LiteralDiagramExpressions}
    {ward : Eval.LiteralWardExpressionProofs expressions}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward)
    (arithmetic : Eval.RationalIntervalArithmetic)
    (generator : Orbit.HyperoctahedralGenerator)
    (source target : Eval.BoxTrigEnvironment) : Set₁ where
  field
    environmentCompatibility :
      GeneratorEnvironmentCompatibility arithmetic generator source target
    regularIntegrandGeneratorExact :
      Joint.transformExpression generator (Eval.regularIntegrand scalarData)
      ≡ Eval.regularIntegrand scalarData
open LiteralGeneratorBoxTransport public

literalRegularIntegrandIntervalTransportExact :
  ∀ {expressions ward scalarData arithmetic generator source target} →
  LiteralGeneratorBoxTransport
    {expressions = expressions} {ward = ward}
    scalarData arithmetic generator source target →
  Eval.evaluateExpression arithmetic target (Eval.regularIntegrand scalarData)
  ≡ Eval.evaluateExpression arithmetic source (Eval.regularIntegrand scalarData)
literalRegularIntegrandIntervalTransportExact certificate =
  invariantExpressionEvaluationTransport
    (environmentCompatibility certificate)
    (regularIntegrandGeneratorExact certificate)

record SameIntervalGeneratorEvaluation
    {arithmetic : Eval.RationalIntervalArithmetic}
    {generator : Orbit.HyperoctahedralGenerator}
    {source target : Eval.BoxTrigEnvironment}
    {expression : Eval.DiagramExpression}
    (compatibility : GeneratorEnvironmentCompatibility
      arithmetic generator source target)
    (invariantExact : Joint.transformExpression generator expression ≡ expression)
    (sourceEvaluation : Eval.CertifiedExpressionEvaluation
      arithmetic source expression) : Set₁ where
  field
    targetEvaluation : Eval.CertifiedExpressionEvaluation arithmetic target expression
    sameIntervalValue :
      Eval.intervalValue targetEvaluation ≡ Eval.intervalValue sourceEvaluation
open SameIntervalGeneratorEvaluation public

generatorEvaluationTransportLevel : ProofLevel
generatorEvaluationTransportLevel = machineChecked

literalRegularIntegrandIntervalTransportLevel : ProofLevel
literalRegularIntegrandIntervalTransportLevel = machineChecked

literalGeneratedBoxAtomCovarianceLevel : ProofLevel
literalGeneratedBoxAtomCovarianceLevel = conditional
