{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact where

------------------------------------------------------------------------
-- PATH13 NATIVE RADIUS -> RELATIVE-CONTOUR PRINCIPAL IMAGE
--
-- Geometry and the literal 74-link same-object contour remain exactly the same.
-- Physical per-link smallness comes from the native `SelectedInverseLinkRadius13`.
--
-- The compatibility recognition record retains three fields.  The preferred
-- route factors the first two into `SelectedPath13OperatorChartRepresentation`,
-- where they belong as physical representation identifications.  The genuinely
-- cut-specific residual is then only
--
--   1/24 <= selected cut radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact as Fibre
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
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
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

------------------------------------------------------------------------
-- Compatibility recognition surface.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Preferred cut residual: only the scalar inclusion remains cut-specific.
------------------------------------------------------------------------

record Path13RadiusCutThreshold
    {CoarseField : Set}
    (representation : OperatorChart.SelectedPath13OperatorChartRepresentation
      CoarseField) : Set where
  field
    sourceThresholdInsideSelectedCut :
      Chart.sourceDefectThreshold
      ≤ Path.chartRadius
          (Selected.cutData
            (PathTarget.bridge13
              (OperatorChart.selectedPhysical representation)))

open Path13RadiusCutThreshold public

asPath13RadiusCutRecognition :
  ∀ {CoarseField}
    (representation : OperatorChart.SelectedPath13OperatorChartRepresentation
      CoarseField) →
  Path13RadiusCutThreshold representation →
  Path13RadiusCutRecognition
    (OperatorChart.selectedPhysical representation)
    (OperatorChart.operatorRepresentation representation)
asPath13RadiusCutRecognition representation threshold = record
  { selectedCutOrderIsRationalOrder =
      OperatorChart.selectedCutOrderIsRationalOrder representation
  ; selectedCutDefectIsOperatorDefect =
      OperatorChart.selectedCutDefectIsOperatorDefect representation
  ; sourceThresholdBelowSelectedCut =
      sourceThresholdInsideSelectedCut threshold
  }

------------------------------------------------------------------------
-- Radius-driven 74-link bound on the exact erased relative contour.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Preferred end-to-end principal-image theorem from the representation
-- extension plus the one scalar cut threshold.
------------------------------------------------------------------------

path13RelativeContourInPrincipalImageFromOperatorChart :
  ∀ {CoarseField}
    (representation : OperatorChart.SelectedPath13OperatorChartRepresentation
      CoarseField)
    (threshold : Path13RadiusCutThreshold representation)
    bond step point →
  let selected = OperatorChart.selectedPhysical representation
      reduced = Reduced.canonicalReducedPath13FamilyGeometry selected
  in
  Log.InPrincipalImage
    (Family.path13PrincipalChart (Reduced.asPath13FamilyGeometry reduced))
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
path13RelativeContourInPrincipalImageFromOperatorChart
    representation threshold bond step point =
  let
    fibre = OperatorChart.backgroundRadius representation
    selected = OperatorChart.selectedPhysical representation
    reduced = Reduced.canonicalReducedPath13FamilyGeometry selected
    radius = Fibre.nativeInverseLinkRadius fibre
    recognition = asPath13RadiusCutRecognition representation threshold
  in
  path13RelativeContourInPrincipalImageFromRadius
    reduced radius
    (OperatorChart.operatorRepresentation representation)
    recognition bond step point

cmp98Path13RadiusRelative74TelescopeLevel : ProofLevel
cmp98Path13RadiusRelative74TelescopeLevel = machineChecked

cmp98Path13RadiusPrincipalImageCompilerLevel : ProofLevel
cmp98Path13RadiusPrincipalImageCompilerLevel = machineChecked

cmp98Path13OperatorChartCutThresholdAdapterLevel : ProofLevel
cmp98Path13OperatorChartCutThresholdAdapterLevel = machineChecked

-- Compatibility three-field recognition remains available, but the preferred
-- route pays only one cut-specific scalar receipt after the selected physical
-- norm/representation extension is supplied.
literalCMP98Path13RadiusCutRecognitionLevel : ProofLevel
literalCMP98Path13RadiusCutRecognitionLevel = conditional

literalCMP98Path13RadiusCutThresholdLevel : ProofLevel
literalCMP98Path13RadiusCutThresholdLevel = conditional
