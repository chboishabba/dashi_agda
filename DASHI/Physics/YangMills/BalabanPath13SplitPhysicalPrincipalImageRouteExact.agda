{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SplitPhysicalPrincipalImageRouteExact where

open import Data.Rational.Base as ℚ using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as Existing
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as Radius
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log

record SplitPath13CutThreshold
    {CoarseField : Set}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField) : Set where
  field
    sourceThresholdInsideSelectedCut :
      Chart.sourceDefectThreshold
      ≤ Path.chartRadius
          (Selected.cutData
            (Target.bridge13 (Split.selectedPhysical representation)))
open SplitPath13CutThreshold public

asRecognition :
  ∀ {CoarseField}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField) →
  SplitPath13CutThreshold representation →
  Existing.Path13RadiusCutRecognition
    (Split.selectedPhysical representation)
    (Split.standardOperatorRepresentation representation)
asRecognition representation threshold = record
  { Existing.Path13RadiusCutRecognition.selectedCutOrderIsRationalOrder =
      Split.selectedCutOrderIsRationalOrder representation
  ; Existing.Path13RadiusCutRecognition.selectedCutDefectIsOperatorDefect =
      Split.selectedCutDefectIsStandardOperatorDefect representation
  ; Existing.Path13RadiusCutRecognition.sourceThresholdBelowSelectedCut =
      sourceThresholdInsideSelectedCut threshold
  }

reducedGeometry :
  ∀ {CoarseField} →
  Split.SplitPath13PhysicalStandardRepresentation CoarseField →
  Reduced.ReducedPath13FamilyGeometry CoarseField
reducedGeometry representation =
  Reduced.canonicalReducedPath13FamilyGeometry (Split.selectedPhysical representation)

relativeContourInPrincipalImage :
  ∀ {CoarseField}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField)
    (threshold : SplitPath13CutThreshold representation)
    bond step point →
  let reduced = reducedGeometry representation
      geometry = Reduced.asPath13FamilyGeometry reduced
  in
  Log.InPrincipalImage
    (Family.path13PrincipalChart geometry)
    (Family.erasedRelativeContour geometry bond step point)
relativeContourInPrincipalImage representation threshold bond step point =
  let
    reduced = reducedGeometry representation
    radius = VariationalRadius.selectedPath13NativeRadius
      (Split.physicalVariationalRadius representation)
  in
  Existing.path13RelativeContourInPrincipalImageFromRadius
    reduced radius
    (Split.standardOperatorRepresentation representation)
    (asRecognition representation threshold)
    bond step point

cmp98Path13SplitPhysicalPrincipalImageCompilerLevel : ProofLevel
cmp98Path13SplitPhysicalPrincipalImageCompilerLevel = machineChecked

-- The standard R171 representation is no longer part of the physical
-- variational producer; only the same-object cut/operator weld and scalar cut
-- inclusion connect it to Path13.
literalCMP98Path13SplitCutOperatorRecognitionLevel : ProofLevel
literalCMP98Path13SplitCutOperatorRecognitionLevel = conditional
