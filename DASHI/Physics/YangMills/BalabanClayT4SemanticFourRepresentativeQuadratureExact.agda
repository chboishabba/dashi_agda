module DASHI.Physics.YangMills.BalabanClayT4SemanticFourRepresentativeQuadratureExact where

------------------------------------------------------------------------
-- SAME-SOURCE FOUR-ORBIT QUADRATURE RECEIPT PROJECTION.
--
-- The actual generated evaluator provides one quadrature proof for EACH
-- GridCell4. We select the four genuine source geometric representatives
-- without introducing arbitrary interval numbers. The semantic
-- covariance certificate transports their exact recursive interval
-- evaluations to each of the 240 generated regular boxes.
--
-- This is intentionally not a claim that the 4 quadratures have been
-- numerically certified: the source evaluator contains analytic Set
-- fields and the actual Wilson/ghost/Haar expression is not inhabited
-- from raw source formulas yet. The output is a proof-preserving
-- reduction of existing receipt families.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import Agda.Builtin.Nat using (_+_)
open import Data.List.Base using (length)
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4LiteralSemanticSevenGeneratorTransportExact as Semantic

record LiteralSemanticFourQuadratureCut
    {expressions : Eval.LiteralDiagramExpressions}
    {ward : Eval.LiteralWardExpressionProofs expressions}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward)
    : Set₃ where
  field
    -- An ACTUAL literal generated-grid evaluator, not 4 opaque numbers.
    source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData

    -- The two physical source seams at SAME original evaluator inputs.
    semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData
      (Eval.arithmetic source)
      (Eval.environment source)

  representative1 representative2 representative3 representative4 :
    Grid.GridCell4
  representative1 = Geometry.oneOuterRepresentative
  representative2 = Geometry.twoOuterRepresentative
  representative3 = Geometry.threeOuterRepresentative
  representative4 = Geometry.fourOuterRepresentative

  box1 box2 box3 box4 : Eval.BoxTrigEnvironment
  box1 = Eval.environment source representative1
  box2 = Eval.environment source representative2
  box3 = Eval.environment source representative3
  box4 = Eval.environment source representative4

  integrand1 : Eval.RationalInterval
  integrand1 = Eval.evaluateExpression (Eval.arithmetic source) box1
    (Eval.regularIntegrand scalarData)
  integrand2 : Eval.RationalInterval
  integrand2 = Eval.evaluateExpression (Eval.arithmetic source) box2
    (Eval.regularIntegrand scalarData)
  integrand3 : Eval.RationalInterval
  integrand3 = Eval.evaluateExpression (Eval.arithmetic source) box3
    (Eval.regularIntegrand scalarData)
  integrand4 : Eval.RationalInterval
  integrand4 = Eval.evaluateExpression (Eval.arithmetic source) box4
    (Eval.regularIntegrand scalarData)

  quadrature1 :
    Eval.CertifiedBoxQuadrature box1
      (Eval.intervalValue (Eval.regularIntegrandEvaluation source representative1))
  quadrature1 = Eval.quadrature source representative1

  quadrature2 :
    Eval.CertifiedBoxQuadrature box2
      (Eval.intervalValue (Eval.regularIntegrandEvaluation source representative2))
  quadrature2 = Eval.quadrature source representative2

  quadrature3 :
    Eval.CertifiedBoxQuadrature box3
      (Eval.intervalValue (Eval.regularIntegrandEvaluation source representative3))
  quadrature3 = Eval.quadrature source representative3

  quadrature4 :
    Eval.CertifiedBoxQuadrature box4
      (Eval.intervalValue (Eval.regularIntegrandEvaluation source representative4))
  quadrature4 = Eval.quadrature source representative4

  -- All four literal receipts are definitionally bound to the same
  -- recursively evaluated regular integrand, not separate selections.
  literalInterval1 :
    Eval.intervalValue (Eval.regularIntegrandEvaluation source representative1)
      ≡ integrand1
  literalInterval1 =
    Eval.intervalValueExact (Eval.regularIntegrandEvaluation source representative1)

  literalInterval2 :
    Eval.intervalValue (Eval.regularIntegrandEvaluation source representative2)
      ≡ integrand2
  literalInterval2 =
    Eval.intervalValueExact (Eval.regularIntegrandEvaluation source representative2)

  literalInterval3 :
    Eval.intervalValue (Eval.regularIntegrandEvaluation source representative3)
      ≡ integrand3
  literalInterval3 =
    Eval.intervalValueExact (Eval.regularIntegrandEvaluation source representative3)

  literalInterval4 :
    Eval.intervalValue (Eval.regularIntegrandEvaluation source representative4)
      ≡ integrand4
  literalInterval4 =
    Eval.intervalValueExact (Eval.regularIntegrandEvaluation source representative4)

  -- Reuse the ACTUAL B4 orbit paths to transport the same interval
  -- from every generated regular cell to its source representative.
  original240EvaluationsReduceToFour :
    ∀ cell →
    Eval.evaluateExpression (Eval.arithmetic source)
      (Eval.environment source
        (Action.representative
          (Geometry.orbitClass cell)))
      (Eval.regularIntegrand scalarData)
    ≡
    Eval.evaluateExpression (Eval.arithmetic source)
      (Eval.environment source cell)
      (Eval.regularIntegrand scalarData)
  original240EvaluationsReduceToFour =
    Semantic.originalLiteralSemanticFourOrbitTransport semantic

open LiteralSemanticFourQuadratureCut public

-- Count certificates are imported from original generated orbit geometry,
-- not guessed from four arbitrary list lengths.
fourRepresentativeRegularCount :
  length Geometry.oneOuterCells +
    (length Geometry.twoOuterCells +
      (length Geometry.threeOuterCells +
        length Geometry.fourOuterCells))
    ≡ 240
fourRepresentativeRegularCount =
  Geometry.regularOrbitMultiplicitySum
