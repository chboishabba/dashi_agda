module DASHI.Physics.YangMills.BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact where

------------------------------------------------------------------------
-- ROUND69: LITERAL RECURSIVE EVALUATOR 240 CELLS -> FOUR REPRESENTATIVES
--
-- PRIMARY / METHOD SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Stefano Capitani,
-- "Lattice Perturbation Theory", Physics Reports 382 (2003), 113--302.
-- DOI: 10.1016/S0370-1573(03)00211-4.
--
-- DASHI CONTRIBUTION
--
-- Round57 built an explicit path from every generated Brillouin cell to the
-- canonical representative of its outer-degree orbit.  PR #574 supplied exact
-- structural-recursion transport of the complete DiagramExpression interval
-- evaluator across one hypercubic generator.  Compose them.
--
-- Once the physical regularIntegrand has its seven literal generator
-- equalities and the finite TrigAtom environments transform covariantly, the
-- recursively evaluated interval on EVERY cell equals the interval on its
-- canonical representative.  Thus L3 has four representative analytic
-- evaluations, not 240 whole-expression receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopHyperoctahedralGeneratorCertificateExact as Cert
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact as Transport

asOrbitGenerator : Action.HypercubicGenerator → Orbit.HyperoctahedralGenerator
asOrbitGenerator Action.flip0 = Orbit.flip0
asOrbitGenerator Action.flip1 = Orbit.flip1
asOrbitGenerator Action.flip2 = Orbit.flip2
asOrbitGenerator Action.flip3 = Orbit.flip3
asOrbitGenerator Action.swap01 = Orbit.swap01
asOrbitGenerator Action.swap12 = Orbit.swap12
asOrbitGenerator Action.swap23 = Orbit.swap23

record LiteralFourRepresentativeTransport
    {expressions : Eval.LiteralDiagramExpressions}
    {ward : Eval.LiteralWardExpressionProofs expressions}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward) : Set₁ where
  field
    arithmetic : Eval.RationalIntervalArithmetic
    environmentAt : Grid.GridCell4 → Eval.BoxTrigEnvironment

    generatorCertificate :
      Cert.LiteralRegularIntegrandB4GeneratorCertificate scalarData

    -- Primitive analytic boundary: sine/cosine/shifted/hat-momentum intervals
    -- transform exactly on each paired generated box.
    environmentCompatibility : ∀ generator cell →
      Transport.GeneratorEnvironmentCompatibility
        arithmetic
        (asOrbitGenerator generator)
        (environmentAt cell)
        (environmentAt (Action.act generator cell))

open LiteralFourRepresentativeTransport public

regularIntegrandGeneratorInvariantExact :
  ∀ {expressions ward scalarData}
    (dataSet : LiteralFourRepresentativeTransport
      {expressions = expressions} {ward = ward} scalarData) →
    (generator : Action.HypercubicGenerator) →
  Joint.transformExpression (asOrbitGenerator generator)
    (Eval.regularIntegrand scalarData)
  ≡ Eval.regularIntegrand scalarData
regularIntegrandGeneratorInvariantExact dataSet Action.flip0 =
  Cert.flip0Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))
regularIntegrandGeneratorInvariantExact dataSet Action.flip1 =
  Cert.flip1Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))
regularIntegrandGeneratorInvariantExact dataSet Action.flip2 =
  Cert.flip2Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))
regularIntegrandGeneratorInvariantExact dataSet Action.flip3 =
  Cert.flip3Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))
regularIntegrandGeneratorInvariantExact dataSet Action.swap01 =
  Cert.swap01Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))
regularIntegrandGeneratorInvariantExact dataSet Action.swap12 =
  Cert.swap12Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))
regularIntegrandGeneratorInvariantExact dataSet Action.swap23 =
  Cert.swap23Exact (Cert.sevenGeneratorExact (generatorCertificate dataSet))

oneGeneratorEvaluationTransport :
  ∀ {expressions ward scalarData}
    (dataSet : LiteralFourRepresentativeTransport
      {expressions = expressions} {ward = ward} scalarData) →
    generator cell →
  Eval.evaluateExpression (arithmetic dataSet)
    (environmentAt dataSet (Action.act generator cell))
    (Eval.regularIntegrand scalarData)
  ≡ Eval.evaluateExpression (arithmetic dataSet)
    (environmentAt dataSet cell)
    (Eval.regularIntegrand scalarData)
oneGeneratorEvaluationTransport dataSet generator cell =
  Transport.invariantExpressionEvaluationTransport
    (environmentCompatibility dataSet generator cell)
    (regularIntegrandGeneratorInvariantExact dataSet generator)

pathEvaluationTransport :
  ∀ {expressions ward scalarData}
    (dataSet : LiteralFourRepresentativeTransport
      {expressions = expressions} {ward = ward} scalarData) →
    ∀ {source target} →
    Action.HypercubicPath source target →
  Eval.evaluateExpression (arithmetic dataSet)
    (environmentAt dataSet target)
    (Eval.regularIntegrand scalarData)
  ≡ Eval.evaluateExpression (arithmetic dataSet)
    (environmentAt dataSet source)
    (Eval.regularIntegrand scalarData)
pathEvaluationTransport dataSet Action.pathRefl = refl
pathEvaluationTransport dataSet (Action.pathStep generator cell) =
  oneGeneratorEvaluationTransport dataSet generator cell
pathEvaluationTransport dataSet (Action.pathTrans first second) =
  trans
    (pathEvaluationTransport dataSet second)
    (pathEvaluationTransport dataSet first)

cellEvaluationEqualsCanonicalRepresentative :
  ∀ {expressions ward scalarData}
    (dataSet : LiteralFourRepresentativeTransport
      {expressions = expressions} {ward = ward} scalarData) →
    cell →
  Eval.evaluateExpression (arithmetic dataSet)
    (environmentAt dataSet (Action.representative (Geometry.orbitClass cell)))
    (Eval.regularIntegrand scalarData)
  ≡ Eval.evaluateExpression (arithmetic dataSet)
    (environmentAt dataSet cell)
    (Eval.regularIntegrand scalarData)
cellEvaluationEqualsCanonicalRepresentative dataSet cell =
  pathEvaluationTransport dataSet (Action.cellPathToOrbitRepresentative cell)

literalEvaluatorFourRepresentativeReductionLevel : ProofLevel
literalEvaluatorFourRepresentativeReductionLevel = machineChecked

physicalFourRepresentativeAnalyticEnclosuresLevel : ProofLevel
physicalFourRepresentativeAnalyticEnclosuresLevel = conditional
