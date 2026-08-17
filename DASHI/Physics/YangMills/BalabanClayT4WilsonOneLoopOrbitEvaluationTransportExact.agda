module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact where

------------------------------------------------------------------------
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
-- Close the semantic gap between syntax equivariance and interval boxes.
-- A hypercubic generator acts on the literal DiagramExpression, while the
-- corresponding target box supplies transformed trigonometric atom bounds.
-- It is enough to prove compatibility on the finite TrigAtom vocabulary.
-- Structural recursion then proves that evaluating the transformed complete
-- Wilson/ghost/Haar expression on the transformed box gives exactly the same
-- RationalInterval as evaluating the original expression on the source box.
--
-- This is deliberately stronger than merely assigning equal orbit receipts:
-- the equality is inherited from the same recursive evaluator.  The remaining
-- analytic source obligation is atom-level enclosure covariance for the actual
-- paired boxes, plus the 7/6 literal-integrand generator equations isolated in
-- the Round57 generator certificate.
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

------------------------------------------------------------------------
-- Certification transport: if the target receipt is definitionally tied to
-- recursive evaluation, the same interval value may be transported across a
-- generator orbit without manufacturing a second opaque numerical enclosure.
------------------------------------------------------------------------

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

-- The finite analytic producer now lives at the atom/environment boundary:
-- prove transformed sine/cosine/shifted/hat-momentum interval equality on the
-- actual paired generated boxes.  No 240 independent whole-expression receipts
-- are mathematically necessary once this is instantiated.
literalGeneratedBoxAtomCovarianceLevel : ProofLevel
literalGeneratedBoxAtomCovarianceLevel = conditional
