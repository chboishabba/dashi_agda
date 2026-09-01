{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact where

------------------------------------------------------------------------
-- ROUND175 A1 BIDI: THE SELECTED BACKGROUND ALREADY OWNS THE CUT + CHART
--
-- R170 carries `SelectedBackgroundVariationalChartBridge`; that bridge already
-- contains `cutData`, `principalChart`, `sameDefectAlgebra`, and
-- `admissibleIsPrincipalImage`.  R174 showed that these are exactly the data
-- needed to generate R166 recognition.
--
-- Therefore we derive the whole R174 recognition object from R170.  The only
-- additional scalar fact is the inclusion of the conservative CMP98 threshold
-- 1/24 in the already selected principal-log cut radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact as R168
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingCutRecognitionRound174Exact as R174
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope

record SelectedExistingCutInputs
    {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source) : Set where
  field
    sourceThresholdBelowSelectedCut :
      Chart.sourceDefectThreshold
      ≤ Path.chartRadius (Selected.cutData (R170.bridge weld))

open SelectedExistingCutInputs public

selectedCutDefectIsOperatorDefect :
  ∀ {C n Value group CoarseField FineField Lie}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source}
    value →
  Path.defect (Path.defectAlgebra (Selected.cutData (R170.bridge weld))) value
  ≡ Telescope.defect (R170.kernel weld) value
selectedCutDefectIsOperatorDefect {weld = weld} value =
  trans
    (cong (λ algebra → Path.defect algebra value)
      (Selected.sameDefectAlgebra (R170.bridge weld)))
    (sym (R170.kernelDefectIsSelectedDefect weld value))

selectedCutOrderIsRationalOrder :
  ∀ {C n Value group CoarseField FineField Lie}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source} →
  Scale.LessEqual
    (Path.scale (Path.defectAlgebra (Selected.cutData (R170.bridge weld))))
  ≡ _≤_
selectedCutOrderIsRationalOrder {weld = weld} =
  trans
    (cong (λ algebra → Scale.LessEqual (Path.scale algebra))
      (Selected.sameDefectAlgebra (R170.bridge weld)))
    (R170.chartOrderIsRationalOrder weld)

asExistingCutRecognition :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source) →
  SelectedExistingCutInputs source weld →
  R174.ExistingCutRecognition source
    (R168.asLiteralRelativeDefectInputs
      source (R170.asPositiveLinkDefectInputs source weld))
asExistingCutRecognition source weld cutInputs = record
  { R174.ExistingCutRecognition.cut =
      Selected.cutData (R170.bridge weld)
  ; R174.ExistingCutRecognition.chart =
      Selected.principalChart (R170.bridge weld)
  ; R174.ExistingCutRecognition.cutDefectIsOperatorDefect =
      selectedCutDefectIsOperatorDefect
  ; R174.ExistingCutRecognition.cutOrderIsRationalOrder =
      selectedCutOrderIsRationalOrder
  ; R174.ExistingCutRecognition.sourceThresholdBelowCutRadius =
      sourceThresholdBelowSelectedCut cutInputs
  ; R174.ExistingCutRecognition.cutAdmissibleIsPrincipalImage =
      Selected.admissibleIsPrincipalImage (R170.bridge weld)
  }

cmp98Equation119SelectedExistingCutRound175Level : ProofLevel
cmp98Equation119SelectedExistingCutRound175Level = machineChecked

literalCMP98SourceThresholdInsideSelectedCutRound175Level : ProofLevel
literalCMP98SourceThresholdInsideSelectedCutRound175Level = conditional
