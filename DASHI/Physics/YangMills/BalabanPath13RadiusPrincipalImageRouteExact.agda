{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact where

------------------------------------------------------------------------
-- PATH13 NATIVE RADIUS -> RELATIVE-CONTOUR PRINCIPAL IMAGE
--
-- This is the radius-driven sibling of the older selected-defect weld.
-- Geometry and the literal 74-link same-object contour remain exactly the same.
-- The per-link estimate now comes from the already-native
-- `SelectedInverseLinkRadius13` instead of re-routing physical smallness through
-- an abstract variational defect.
--
-- Therefore only three selected-chart recognition facts remain here:
--   * the selected cut order is rational order;
--   * the selected cut defect is the standard operator defect;
--   * the fixed source threshold 1/24 lies inside the selected chart radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact as Existing
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as Radius
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact as Erasure
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact as RawPath
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record Path13RadiusCutRecognition
    {CoarseField : Set}
    (selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra)
    (representation : Radius.ExactRationalSU2OperatorDefectRepresentation) : Set₁ where
  field
    selectedCutOrderIsRationalOrder :
      Scale.LessEqual
        (Path.scale
          (Path.defectAlgebra (Selected.cutData (PathTarget.bridge13 selected))))
      ≡ _≤_

    selectedCutDefectIsOperatorDefect : ∀ value →
      Path.defect
        (Path.defectAlgebra (Selected.cutData (PathTarget.bridge13 selected)))
        value
      ≡ Op.defect (Radius.operatorKernel representation) value

    sourceThresholdBelowSelectedCut :
      Chart.sourceDefectThreshold
      ≤ Path.chartRadius (Selected.cutData (PathTarget.bridge13 selected))

open Path13RadiusCutRecognition public

relativeContourDefectBelowSourceThresholdFromRadius :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    (radius : Background.SelectedInverseLinkRadius13
      (PathTarget.path13Background (Reduced.selectedPhysical reduced)))
    (representation : Radius.ExactRationalSU2OperatorDefectRepresentation)
    bond step point →
  Op.defect (Radius.operatorKernel representation)
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
  ≤ Chart.sourceDefectThreshold
relativeContourDefectBelowSourceThresholdFromRadius
    reduced radius representation bond step point =
  let
    geometry = Reduced.asPath13FamilyGeometry reduced
    source = Family.geometrySourceAt geometry bond
    minus = Geometry.minusEmbedding source step
    background = PathTarget.path13Background (Reduced.selectedPhysical reduced)
    closed = Existing.path13RelativeClosedWord reduced bond step point

    bound74 = Radius.rawPathDefectBelowLengthBudgetFromRadius
      representation background radius
      (Embed.embeddingCentre minus) closed 74
      (Existing.path13RelativeClosedWordLengthAtMost74 reduced bond step point)

    boundRelativeBudget :
      Op.defect (Radius.operatorKernel representation)
        (RawPath.pathProduct
          (Erasure.rawPathFactors
            (R192.path13PhysicalPeriodicRealization background)
            (Embed.embeddingCentre minus) closed))
      ≤ R164.relativeLinkBudget
    boundRelativeBudget =
      subst
        (λ upper →
          Op.defect (Radius.operatorKernel representation)
            (RawPath.pathProduct
              (Erasure.rawPathFactors
                (R192.path13PhysicalPeriodicRealization background)
                (Embed.embeddingCentre minus) closed))
          ≤ upper)
        R164.nat74BudgetIsRelativeLinkBudget
        bound74

    targetBound :
      Op.defect (Radius.operatorKernel representation)
        (Family.erasedRelativeContour geometry bond step point)
      ≤ R164.relativeLinkBudget
    targetBound =
      subst
        (λ value →
          Op.defect (Radius.operatorKernel representation) value
          ≤ R164.relativeLinkBudget)
        (Existing.rawClosedProductIsErasedRelativeContour
          reduced bond step point)
        boundRelativeBudget
  in
  ℚP.≤-trans targetBound R164.relativeLinkBudgetInsideSourceThreshold

selectedRadiusCutRecognizesSourceThreshold :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    {representation : Radius.ExactRationalSU2OperatorDefectRepresentation} →
  Path13RadiusCutRecognition selected representation →
  ∀ value →
  Op.defect (Radius.operatorKernel representation) value
    ≤ Chart.sourceDefectThreshold →
  Log.InPrincipalImage
    (Selected.principalChart (PathTarget.bridge13 selected)) value
selectedRadiusCutRecognizesSourceThreshold
    {selected = selected} {representation = representation}
    recognition value operatorBound =
  let
    bridge = PathTarget.bridge13 selected
    cut = Selected.cutData bridge

    operatorBelowCut :
      Op.defect (Radius.operatorKernel representation) value
      ≤ Path.chartRadius cut
    operatorBelowCut =
      ℚP.≤-trans operatorBound
        (sourceThresholdBelowSelectedCut recognition)

    cutDefectBoundRational :
      Path.defect (Path.defectAlgebra cut) value ≤ Path.chartRadius cut
    cutDefectBoundRational =
      subst
        (λ lower → lower ≤ Path.chartRadius cut)
        (sym (selectedCutDefectIsOperatorDefect recognition value))
        operatorBelowCut

    cutDefectBound :
      Scale.LessEqual (Path.scale (Path.defectAlgebra cut))
        (Path.defect (Path.defectAlgebra cut) value)
        (Path.chartRadius cut)
    cutDefectBound =
      subst
        (λ relation → relation
          (Path.defect (Path.defectAlgebra cut) value)
          (Path.chartRadius cut))
        (sym (selectedCutOrderIsRationalOrder recognition))
        cutDefectBoundRational

    admitted : Path.PrincipalLogAdmissible cut value
    admitted = Path.defectBelowRadiusImpliesAdmissible cut value cutDefectBound
  in
  subst
    (λ predicate → predicate value)
    (Selected.admissibleIsPrincipalImage bridge)
    admitted

path13RelativeContourInPrincipalImageFromRadius :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    (radius : Background.SelectedInverseLinkRadius13
      (PathTarget.path13Background (Reduced.selectedPhysical reduced)))
    (representation : Radius.ExactRationalSU2OperatorDefectRepresentation)
    (recognition : Path13RadiusCutRecognition
      (Reduced.selectedPhysical reduced) representation)
    bond step point →
  Log.InPrincipalImage
    (Family.path13PrincipalChart (Reduced.asPath13FamilyGeometry reduced))
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
path13RelativeContourInPrincipalImageFromRadius
    reduced radius representation recognition bond step point =
  selectedRadiusCutRecognizesSourceThreshold recognition
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
    (relativeContourDefectBelowSourceThresholdFromRadius
      reduced radius representation bond step point)

cmp98Path13RadiusRelative74TelescopeLevel : ProofLevel
cmp98Path13RadiusRelative74TelescopeLevel = machineChecked

cmp98Path13RadiusPrincipalImageCompilerLevel : ProofLevel
cmp98Path13RadiusPrincipalImageCompilerLevel = machineChecked

-- The old seven-field selected cut/defect weld is no longer required on this
-- route.  Physical per-link smallness lives in SelectedInverseLinkRadius13;
-- standard SU(2) operator representation and selected chart recognition remain
-- separately attributed interfaces.
literalCMP98Path13RadiusCutRecognitionLevel : ProofLevel
literalCMP98Path13RadiusCutRecognitionLevel = conditional
