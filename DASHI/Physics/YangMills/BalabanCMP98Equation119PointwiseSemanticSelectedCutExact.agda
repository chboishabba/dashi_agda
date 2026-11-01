{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PointwiseSemanticSelectedCutExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): POINTWISE SELECTED-CUT SEMANTIC PRODUCER
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- R175 pays principal-chart admission by the conservative global implication
--
--     defect(actual relative) <= 1/24 <= selected cut radius.
--
-- But the existing least-privilege selected-cut owner already proves that for
-- an ACTUAL value it is enough to show
--
--     selectedDefect(actual relative) <= selected cut radius.
--
-- This module wires that pointwise theorem into the literal CMP98 contour and
-- keeps the semantic exp(principalLog(relative)) = relative guarantee beside
-- the derivative construction.  It therefore removes the global `1/24 <= cut`
-- requirement from this branch without exploiting the fact that older chart-
-- only derivative constructors happen not to consume image admission.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact as R156
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119PointwiseSelectedCutExact as Pointwise
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

record PointwiseSelectedCutFamily
    {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)) : Set₁ where
  field
    actualRelativeCutReceipt :
      (step : Nat) →
      (point : Centered.CenteredBlockPoint4 6) →
      Pointwise.ActualSelectedCutReceipt
        (R170.bridge weld)
        (R155.relativeContourElement
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point)

open PointwiseSelectedCutFamily public

pointwiseRelativeContourPrincipalImage :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)) →
  PointwiseSelectedCutFamily source weld →
  R156.RelativeContourPrincipalImage
    (R158.asRound152Source (R182.asCanonicalL13Equation119Source source))
    (Selected.principalChart (R170.bridge weld))
pointwiseRelativeContourPrincipalImage source weld family = record
  { R156.RelativeContourPrincipalImage.relativeInImage =
      λ step point →
        Pointwise.actualSelectedCutReceiptGivesPrincipalImage
          (actualRelativeCutReceipt family step point)
  }

pointwisePrincipalPointYExponentiatesToLiteralRelativeContour :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source))
    (family : PointwiseSelectedCutFamily source weld)
    step point →
  Log.expSU2 (Selected.principalChart (R170.bridge weld))
    (R156.principalPointY
      (R158.asRound152Source (R182.asCanonicalL13Equation119Source source))
      (Selected.principalChart (R170.bridge weld))
      step point)
  ≡
  R155.relativeContourElement
    (R158.asRound152Source (R182.asCanonicalL13Equation119Source source))
    step point
pointwisePrincipalPointYExponentiatesToLiteralRelativeContour
    source weld family step point =
  R156.principalPointYExponentiatesToLiteralRelativeContour
    (R158.asRound152Source (R182.asCanonicalL13Equation119Source source))
    (Selected.principalChart (R170.bridge weld))
    (pointwiseRelativeContourPrincipalImage source weld family)
    step point

pointwiseSemanticSelectedCutOneStepDerivative :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)) →
  PointwiseSelectedCutFamily source weld →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
pointwiseSemanticSelectedCutOneStepDerivative source weld family federbush =
  R156.existingPrincipalLogOneStepDerivative
    (R158.asRound152Source (R182.asCanonicalL13Equation119Source source))
    (Selected.principalChart (R170.bridge weld))
    (R159.asUniformLeftRightDexpFamily
      (R177.asUniformAdjointDifferentialCalculus federbush))

pointwiseSemanticSelectedCutMultiscaleDerivative :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)) →
  PointwiseSelectedCutFamily source weld →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator R178.su2AdditiveCarrier
pointwiseSemanticSelectedCutMultiscaleDerivative source weld family federbush =
  R156.existingPrincipalLogMultiscaleDerivative
    (R158.asRound152Source (R182.asCanonicalL13Equation119Source source))
    (Selected.principalChart (R170.bridge weld))
    (R159.asUniformLeftRightDexpFamily
      (R177.asUniformAdjointDifferentialCalculus federbush))

-- The `family` argument is intentionally retained by the derivative producers
-- even though the underlying historical constructor does not inspect it.  The
-- public theorem boundary couples the derivative term to the separately proved
-- exp/log same-object semantics rather than allowing chart-only construction to
-- masquerade as physical principal-log realization.

cmp98Equation119PointwiseSemanticSelectedCutCompilerLevel : ProofLevel
cmp98Equation119PointwiseSemanticSelectedCutCompilerLevel = machineChecked

literalCMP98PointwiseSelectedRelativeDefectBoundLevel : ProofLevel
literalCMP98PointwiseSelectedRelativeDefectBoundLevel = conditional

literalCMP98SelectedBackgroundWeldForPointwiseCutLevel : ProofLevel
literalCMP98SelectedBackgroundWeldForPointwiseCutLevel = conditional
