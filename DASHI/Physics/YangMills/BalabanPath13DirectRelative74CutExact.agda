{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13DirectRelative74CutExact where

------------------------------------------------------------------------
-- PATH13: DIRECT 74-LINK BUDGET -> SELECTED PRINCIPAL IMAGE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as Radius
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact as Existing
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact as Erasure
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact as RawPath
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op

record SplitPath13Relative74CutThreshold
    {CoarseField : Set}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField) : Set where
  field
    relative74BudgetInsideSelectedCut :
      R164.relativeLinkBudget
      ≤ Path.chartRadius
          (Selected.cutData
            (PathTarget.bridge13 (Split.selectedPhysical representation)))
open SplitPath13Relative74CutThreshold public

reducedGeometry :
  ∀ {CoarseField} →
  Split.SplitPath13PhysicalStandardRepresentation CoarseField →
  Reduced.ReducedPath13FamilyGeometry CoarseField
reducedGeometry representation =
  Reduced.canonicalReducedPath13FamilyGeometry
    (Split.selectedPhysical representation)

relativeContourDefectBelowRelative74Budget :
  ∀ {CoarseField}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField)
    bond step point →
  let reduced = reducedGeometry representation
      geometry = Reduced.asPath13FamilyGeometry reduced
  in
  Op.defect (Radius.operatorKernel (Split.standardOperatorRepresentation representation))
    (Family.erasedRelativeContour geometry bond step point)
  ≤ R164.relativeLinkBudget
relativeContourDefectBelowRelative74Budget representation bond step point =
  let
    reduced = reducedGeometry representation
    geometry = Reduced.asPath13FamilyGeometry reduced
    source = Family.geometrySourceAt geometry bond
    minus = Geometry.minusEmbedding source step
    background = PathTarget.path13Background (Reduced.selectedPhysical reduced)
    closed = Existing.path13RelativeClosedWord reduced bond step point
    radius = VariationalRadius.selectedPath13NativeRadius
      (Split.physicalVariationalRadius representation)

    bound74 = Radius.rawPathDefectBelowLengthBudgetFromRadius
      (Split.standardOperatorRepresentation representation)
      background radius
      (Embed.embeddingCentre minus) closed 74
      (Existing.path13RelativeClosedWordLengthAtMost74 reduced bond step point)

    boundRelativeBudget :
      Op.defect (Radius.operatorKernel (Split.standardOperatorRepresentation representation))
        (RawPath.pathProduct
          (Erasure.rawPathFactors
            (R192.path13PhysicalPeriodicRealization background)
            (Embed.embeddingCentre minus) closed))
      ≤ R164.relativeLinkBudget
    boundRelativeBudget =
      subst
        (λ upper →
          Op.defect
            (Radius.operatorKernel (Split.standardOperatorRepresentation representation))
            (RawPath.pathProduct
              (Erasure.rawPathFactors
                (R192.path13PhysicalPeriodicRealization background)
                (Embed.embeddingCentre minus) closed))
          ≤ upper)
        R164.nat74BudgetIsRelativeLinkBudget
        bound74
  in
  subst
    (λ value →
      Op.defect (Radius.operatorKernel (Split.standardOperatorRepresentation representation)) value
      ≤ R164.relativeLinkBudget)
    (Existing.rawClosedProductIsErasedRelativeContour reduced bond step point)
    boundRelativeBudget

directRelative74InPrincipalImage :
  ∀ {CoarseField}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField)
    (threshold : SplitPath13Relative74CutThreshold representation)
    bond step point →
  let reduced = reducedGeometry representation
      geometry = Reduced.asPath13FamilyGeometry reduced
  in
  Log.InPrincipalImage
    (Family.path13PrincipalChart geometry)
    (Family.erasedRelativeContour geometry bond step point)
directRelative74InPrincipalImage representation threshold bond step point =
  let
    selected = Split.selectedPhysical representation
    bridge = PathTarget.bridge13 selected
    cut = Selected.cutData bridge
    reduced = reducedGeometry representation
    geometry = Reduced.asPath13FamilyGeometry reduced
    value = Family.erasedRelativeContour geometry bond step point

    operatorBound :
      Op.defect (Radius.operatorKernel (Split.standardOperatorRepresentation representation)) value
      ≤ Path.chartRadius cut
    operatorBound =
      ℚP.≤-trans
        (relativeContourDefectBelowRelative74Budget representation bond step point)
        (relative74BudgetInsideSelectedCut threshold)

    cutDefectBoundRational :
      Path.defect (Path.defectAlgebra cut) value ≤ Path.chartRadius cut
    cutDefectBoundRational =
      subst
        (λ lower → lower ≤ Path.chartRadius cut)
        (sym (Split.selectedCutDefectIsStandardOperatorDefect representation value))
        operatorBound

    cutDefectBound :
      Scale.LessEqual (Path.scale (Path.defectAlgebra cut))
        (Path.defect (Path.defectAlgebra cut) value)
        (Path.chartRadius cut)
    cutDefectBound =
      subst
        (λ relation → relation
          (Path.defect (Path.defectAlgebra cut) value)
          (Path.chartRadius cut))
        (sym (Split.selectedCutOrderIsRationalOrder representation))
        cutDefectBoundRational

    admitted : Path.PrincipalLogAdmissible cut value
    admitted = Path.defectBelowRadiusImpliesAdmissible cut value cutDefectBound
  in
  subst
    (λ predicate → predicate value)
    (Selected.admissibleIsPrincipalImage bridge)
    admitted

relative74DirectCutCompilerLevel : ProofLevel
relative74DirectCutCompilerLevel = machineChecked

literalRelative74CutThresholdLevel : ProofLevel
literalRelative74CutThresholdLevel = conditional
