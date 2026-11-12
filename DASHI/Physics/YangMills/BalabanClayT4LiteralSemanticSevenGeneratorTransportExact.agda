module DASHI.Physics.YangMills.BalabanClayT4LiteralSemanticSevenGeneratorTransportExact where

------------------------------------------------------------------------
-- BAŁABAN P0 / SOURCE-PRESERVING SEMANTIC GENERATOR TRANSPORT.
--
-- Existing owners:
--   LiteralOneLoopBoxEvaluatorExact: the actual expression and interval AST
--   WilsonOneLoopJointMomentumEquivarianceExact: the actual B4 action
--   WilsonOneLoopOrbitEvaluationTransportExact: the all-expression fold
--   HypercubicGeneratedActionExact: paths from all cells to representatives.
--
-- The older seven-generator certificate demanded syntactic equality
-- transformExpression g E == E. This is too strong for ring-normalized
-- expressions, and may be physically false for an axis-selected kernel.
--
-- This owner instead accepts SEMANTIC equality only at the literal
-- transformed target-box evaluation; the existing atom-covariance
-- transport then establishes source-to-target equality. The seven
-- semantic equalities are genuine, concrete SOURCE obligations; no
-- arbitrary proof of them is fabricated.
--
-- Neither coordinate projections nor sine-half atoms are treated as
-- individually invariant under sign flips. Atoms transform COVARIANTLY.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact as Transport
import DASHI.Physics.YangMills.BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact as Four

------------------------------------------------------------------------
-- Exact source TrigAtom cases, not an unspecified atom oracle.
------------------------------------------------------------------------

record ConcreteAtomGeneratorCovariance
    (arithmetic : Eval.RationalIntervalArithmetic)
    (generator : Orbit.HyperoctahedralGenerator)
    (source target : Eval.BoxTrigEnvironment) : Set₁ where
  field
    sineHalfCovariant : ∀ role axis →
      Eval.evaluateExpression arithmetic target
        (Joint.transformAtom generator (Eval.sineHalf role axis))
      ≡ Eval.atomInterval source (Eval.sineHalf role axis)

    cosineFullCovariant : ∀ role axis →
      Eval.evaluateExpression arithmetic target
        (Joint.transformAtom generator (Eval.cosineFull role axis))
      ≡ Eval.atomInterval source (Eval.cosineFull role axis)

    hatSquaredCovariant : ∀ role →
      Eval.evaluateExpression arithmetic target
        (Joint.transformAtom generator (Eval.hatMomentumSquared role))
      ≡ Eval.atomInterval source (Eval.hatMomentumSquared role)

    colorCovariant :
      Eval.evaluateExpression arithmetic target
        (Joint.transformAtom generator Eval.colorCasimir)
      ≡ Eval.atomInterval source Eval.colorCasimir

    gaugeCovariant :
      Eval.evaluateExpression arithmetic target
        (Joint.transformAtom generator Eval.gaugeParameter)
      ≡ Eval.atomInterval source Eval.gaugeParameter

open ConcreteAtomGeneratorCovariance public

concreteAtomsBuildOriginalEnvironmentCompatibility :
  ∀ {arithmetic generator source target} →
  ConcreteAtomGeneratorCovariance arithmetic generator source target →
  Transport.GeneratorEnvironmentCompatibility
    arithmetic generator source target
concreteAtomsBuildOriginalEnvironmentCompatibility certificate =
  record
    { transformedAtomEvaluationExact = λ
        { (Eval.sineHalf role axis) →
            sineHalfCovariant certificate role axis
        ; (Eval.cosineFull role axis) →
            cosineFullCovariant certificate role axis
        ; (Eval.hatMomentumSquared role) →
            hatSquaredCovariant certificate role
        ; Eval.colorCasimir → colorCovariant certificate
        ; Eval.gaugeParameter → gaugeCovariant certificate
        }
    }

originalEnvironmentCompatibilityBuildsConcreteAtoms :
  ∀ {arithmetic generator source target} →
  Transport.GeneratorEnvironmentCompatibility
    arithmetic generator source target →
  ConcreteAtomGeneratorCovariance arithmetic generator source target
originalEnvironmentCompatibilityBuildsConcreteAtoms compatibility =
  record
    { sineHalfCovariant = λ role axis →
        Transport.transformedAtomEvaluationExact compatibility
          (Eval.sineHalf role axis)
    ; cosineFullCovariant = λ role axis →
        Transport.transformedAtomEvaluationExact compatibility
          (Eval.cosineFull role axis)
    ; hatSquaredCovariant = λ role →
        Transport.transformedAtomEvaluationExact compatibility
          (Eval.hatMomentumSquared role)
    ; colorCovariant =
        Transport.transformedAtomEvaluationExact compatibility
          Eval.colorCasimir
    ; gaugeCovariant =
        Transport.transformedAtomEvaluationExact compatibility
          Eval.gaugeParameter
    }

originalIdentityAtomCovariance :
  ∀ arithmetic environment →
  ConcreteAtomGeneratorCovariance
    arithmetic Orbit.identity environment environment
originalIdentityAtomCovariance arithmetic environment =
  record
    { sineHalfCovariant = λ role axis → refl
    ; cosineFullCovariant = λ role axis → refl
    ; hatSquaredCovariant = λ role → refl
    ; colorCovariant = refl
    ; gaugeCovariant = refl
    }

------------------------------------------------------------------------
-- Semantic invariance is at the *same transformed target box*.
-- This is weaker than transformExpression g E == E.
------------------------------------------------------------------------

record LiteralSevenSemanticGeneratorData
    {expressions : Eval.LiteralDiagramExpressions}
    {ward : Eval.LiteralWardExpressionProofs expressions}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward)
    (arithmetic : Eval.RationalIntervalArithmetic)
    (environment : Grid.GridCell4 → Eval.BoxTrigEnvironment) : Set₂ where
  field
    -- The 7 actual atom covariances. Identity comes by refl.
    atomsFlip0 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.flip0
        (environment cell) (environment (Orbit.act Orbit.flip0 cell))
    atomsFlip1 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.flip1
        (environment cell) (environment (Orbit.act Orbit.flip1 cell))
    atomsFlip2 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.flip2
        (environment cell) (environment (Orbit.act Orbit.flip2 cell))
    atomsFlip3 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.flip3
        (environment cell) (environment (Orbit.act Orbit.flip3 cell))
    atomsSwap01 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.swap01
        (environment cell) (environment (Orbit.act Orbit.swap01 cell))
    atomsSwap12 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.swap12
        (environment cell) (environment (Orbit.act Orbit.swap12 cell))
    atomsSwap23 : ∀ cell →
      ConcreteAtomGeneratorCovariance arithmetic Orbit.swap23
        (environment cell) (environment (Orbit.act Orbit.swap23 cell))

    -- The seven literal Wilson/ghost/Haar SEMANTIC equalities.
    -- They must be proved for the selected scalarData, not an AST proxy.
    semanticFlip0 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip0 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip0 cell))
        (Joint.transformExpression Orbit.flip0 (Eval.regularIntegrand scalarData))
    semanticFlip1 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip1 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip1 cell))
        (Joint.transformExpression Orbit.flip1 (Eval.regularIntegrand scalarData))
    semanticFlip2 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip2 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip2 cell))
        (Joint.transformExpression Orbit.flip2 (Eval.regularIntegrand scalarData))
    semanticFlip3 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip3 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.flip3 cell))
        (Joint.transformExpression Orbit.flip3 (Eval.regularIntegrand scalarData))
    semanticSwap01 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.swap01 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.swap01 cell))
        (Joint.transformExpression Orbit.swap01 (Eval.regularIntegrand scalarData))
    semanticSwap12 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.swap12 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.swap12 cell))
        (Joint.transformExpression Orbit.swap12 (Eval.regularIntegrand scalarData))
    semanticSwap23 : ∀ cell →
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.swap23 cell))
        (Eval.regularIntegrand scalarData)
      ≡
      Eval.evaluateExpression arithmetic
        (environment (Orbit.act Orbit.swap23 cell))
        (Joint.transformExpression Orbit.swap23 (Eval.regularIntegrand scalarData))

open LiteralSevenSemanticGeneratorData public

originalAtomsForGenerator :
  ∀ {expressions ward scalarData arithmetic environment} →
  LiteralSevenSemanticGeneratorData
    {expressions = expressions} {ward = ward}
    scalarData arithmetic environment →
  ∀ generator cell →
  ConcreteAtomGeneratorCovariance arithmetic generator
    (environment cell) (environment (Orbit.act generator cell))
originalAtomsForGenerator {arithmetic = arithmetic} {environment = environment}
  dataSet Orbit.identity cell =
  originalIdentityAtomCovariance arithmetic (environment cell)
originalAtomsForGenerator dataSet Orbit.flip0 cell = atomsFlip0 dataSet cell
originalAtomsForGenerator dataSet Orbit.flip1 cell = atomsFlip1 dataSet cell
originalAtomsForGenerator dataSet Orbit.flip2 cell = atomsFlip2 dataSet cell
originalAtomsForGenerator dataSet Orbit.flip3 cell = atomsFlip3 dataSet cell
originalAtomsForGenerator dataSet Orbit.swap01 cell = atomsSwap01 dataSet cell
originalAtomsForGenerator dataSet Orbit.swap12 cell = atomsSwap12 dataSet cell
originalAtomsForGenerator dataSet Orbit.swap23 cell = atomsSwap23 dataSet cell

originalSemanticForGenerator :
  ∀ {expressions ward scalarData arithmetic environment} →
  (dataSet : LiteralSevenSemanticGeneratorData
    {expressions = expressions} {ward = ward}
    scalarData arithmetic environment) →
  ∀ generator cell →
  Eval.evaluateExpression arithmetic
    (environment (Orbit.act generator cell))
    (Eval.regularIntegrand scalarData)
  ≡
  Eval.evaluateExpression arithmetic
    (environment (Orbit.act generator cell))
    (Joint.transformExpression generator (Eval.regularIntegrand scalarData))
originalSemanticForGenerator dataSet Orbit.identity cell = refl
originalSemanticForGenerator dataSet Orbit.flip0 cell = semanticFlip0 dataSet cell
originalSemanticForGenerator dataSet Orbit.flip1 cell = semanticFlip1 dataSet cell
originalSemanticForGenerator dataSet Orbit.flip2 cell = semanticFlip2 dataSet cell
originalSemanticForGenerator dataSet Orbit.flip3 cell = semanticFlip3 dataSet cell
originalSemanticForGenerator dataSet Orbit.swap01 cell = semanticSwap01 dataSet cell
originalSemanticForGenerator dataSet Orbit.swap12 cell = semanticSwap12 dataSet cell
originalSemanticForGenerator dataSet Orbit.swap23 cell = semanticSwap23 dataSet cell

originalLiteralSemanticOneGeneratorTransport :
  ∀ {expressions ward scalarData arithmetic environment} →
  (dataSet : LiteralSevenSemanticGeneratorData
    {expressions = expressions} {ward = ward}
    scalarData arithmetic environment) →
  ∀ generator cell →
  Eval.evaluateExpression arithmetic
    (environment (Orbit.act generator cell))
    (Eval.regularIntegrand scalarData)
  ≡
  Eval.evaluateExpression arithmetic
    (environment cell)
    (Eval.regularIntegrand scalarData)
originalLiteralSemanticOneGeneratorTransport {scalarData = scalarData} dataSet generator cell =
  trans
    (originalSemanticForGenerator dataSet generator cell)
    (Transport.transformEvaluationExact
      (concreteAtomsBuildOriginalEnvironmentCompatibility
        (originalAtomsForGenerator dataSet generator cell))
      (Eval.regularIntegrand scalarData))


------------------------------------------------------------------------
-- SAME GENERATOR, TWO PRE-EXISTING SOURCE ACTIONS.
-- Action.act and Orbit.act use independent flipInterval definitions;
-- extensional equality is required on an abstract GridCell4.
------------------------------------------------------------------------

canonicalActionIsOrbitAction :
  ∀ generator cell →
  Action.act generator cell
    ≡ Orbit.act (Four.asOrbitGenerator generator) cell
canonicalActionIsOrbitAction Action.flip0
  (Grid.gridCell4 Grid.negativeOuter b c d) = refl
canonicalActionIsOrbitAction Action.flip0
  (Grid.gridCell4 Grid.negativeInner b c d) = refl
canonicalActionIsOrbitAction Action.flip0
  (Grid.gridCell4 Grid.positiveInner b c d) = refl
canonicalActionIsOrbitAction Action.flip0
  (Grid.gridCell4 Grid.positiveOuter b c d) = refl
canonicalActionIsOrbitAction Action.flip1
  (Grid.gridCell4 a Grid.negativeOuter c d) = refl
canonicalActionIsOrbitAction Action.flip1
  (Grid.gridCell4 a Grid.negativeInner c d) = refl
canonicalActionIsOrbitAction Action.flip1
  (Grid.gridCell4 a Grid.positiveInner c d) = refl
canonicalActionIsOrbitAction Action.flip1
  (Grid.gridCell4 a Grid.positiveOuter c d) = refl
canonicalActionIsOrbitAction Action.flip2
  (Grid.gridCell4 a b Grid.negativeOuter d) = refl
canonicalActionIsOrbitAction Action.flip2
  (Grid.gridCell4 a b Grid.negativeInner d) = refl
canonicalActionIsOrbitAction Action.flip2
  (Grid.gridCell4 a b Grid.positiveInner d) = refl
canonicalActionIsOrbitAction Action.flip2
  (Grid.gridCell4 a b Grid.positiveOuter d) = refl
canonicalActionIsOrbitAction Action.flip3
  (Grid.gridCell4 a b c Grid.negativeOuter) = refl
canonicalActionIsOrbitAction Action.flip3
  (Grid.gridCell4 a b c Grid.negativeInner) = refl
canonicalActionIsOrbitAction Action.flip3
  (Grid.gridCell4 a b c Grid.positiveInner) = refl
canonicalActionIsOrbitAction Action.flip3
  (Grid.gridCell4 a b c Grid.positiveOuter) = refl
canonicalActionIsOrbitAction Action.swap01
  (Grid.gridCell4 a b c d) = refl
canonicalActionIsOrbitAction Action.swap12
  (Grid.gridCell4 a b c d) = refl
canonicalActionIsOrbitAction Action.swap23
  (Grid.gridCell4 a b c d) = refl

-- Existing source paths, no alternative orbit geometry.
originalLiteralSemanticPathTransport :
  ∀ {expressions ward scalarData arithmetic environment} →
  (dataSet : LiteralSevenSemanticGeneratorData
    {expressions = expressions} {ward = ward}
    scalarData arithmetic environment) →
  ∀ {source target} →
  Action.HypercubicPath source target →
  Eval.evaluateExpression arithmetic (environment target)
    (Eval.regularIntegrand scalarData)
  ≡
  Eval.evaluateExpression arithmetic (environment source)
    (Eval.regularIntegrand scalarData)
originalLiteralSemanticPathTransport dataSet Action.pathRefl = refl
originalLiteralSemanticPathTransport dataSet
  (Action.pathStep generator cell)
  rewrite canonicalActionIsOrbitAction generator cell =
  originalLiteralSemanticOneGeneratorTransport dataSet
    (Four.asOrbitGenerator generator) cell
originalLiteralSemanticPathTransport dataSet
  (Action.pathTrans first second) =
  trans
    (originalLiteralSemanticPathTransport dataSet second)
    (originalLiteralSemanticPathTransport dataSet first)

originalLiteralSemanticFourOrbitTransport :
  ∀ {expressions ward scalarData arithmetic environment} →
  (dataSet : LiteralSevenSemanticGeneratorData
    {expressions = expressions} {ward = ward}
    scalarData arithmetic environment) →
  ∀ cell →
  Eval.evaluateExpression arithmetic
    (environment (Action.representative (Geometry.orbitClass cell)))
    (Eval.regularIntegrand scalarData)
  ≡
  Eval.evaluateExpression arithmetic
    (environment cell)
    (Eval.regularIntegrand scalarData)
originalLiteralSemanticFourOrbitTransport dataSet cell =
  originalLiteralSemanticPathTransport dataSet
    (Action.cellPathToOrbitRepresentative cell)
