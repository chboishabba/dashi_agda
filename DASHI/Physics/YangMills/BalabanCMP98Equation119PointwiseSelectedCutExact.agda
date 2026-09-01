{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PointwiseSelectedCutExact where

------------------------------------------------------------------------
-- LEAST-PRIVILEGE SELECTED CUT: ONLY THE ACTUAL VALUE'S DEFECT IS NEEDED
--
-- The older R170/R175 route identified a generic operator defect with the
-- selected chart defect for every group value. Eq. (119) does not need that
-- universal theorem. The selected bridge already owns the cut, its defect
-- algebra, the cut-algebra identification, and admissible = principal image.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected

selectedDefectBoundRecognizesActualValue :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : Selected.SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    value →
  Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
    (Path.defect (Selected.defectAlgebra bridge) value)
    (Path.chartRadius (Selected.cutData bridge)) →
  Log.InPrincipalImage (Selected.principalChart bridge) value
selectedDefectBoundRecognizesActualValue bridge value selectedBound =
  let
    cut = Selected.cutData bridge
    cutBound :
      Scale.LessEqual (Path.scale (Path.defectAlgebra cut))
        (Path.defect (Path.defectAlgebra cut) value)
        (Path.chartRadius cut)
    cutBound =
      subst
        (λ algebra →
          Scale.LessEqual (Path.scale algebra)
            (Path.defect algebra value)
            (Path.chartRadius cut))
        (sym (Selected.sameDefectAlgebra bridge))
        selectedBound
    admitted : Path.PrincipalLogAdmissible cut value
    admitted = Path.defectBelowRadiusImpliesAdmissible cut value cutBound
  in
  subst
    (λ predicate → predicate value)
    (Selected.admissibleIsPrincipalImage bridge)
    admitted

record ActualSelectedCutReceipt
    {CoarseField FineField Bond Lie Group Bound}
    (bridge : Selected.SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    (value : Group) : Set where
  field
    selectedDefectBelowCut :
      Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
        (Path.defect (Selected.defectAlgebra bridge) value)
        (Path.chartRadius (Selected.cutData bridge))

open ActualSelectedCutReceipt public

actualSelectedCutReceiptGivesPrincipalImage :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    {bridge : Selected.SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound}
    {value : Group} →
  ActualSelectedCutReceipt bridge value →
  Log.InPrincipalImage (Selected.principalChart bridge) value
actualSelectedCutReceiptGivesPrincipalImage {bridge = bridge} {value = value} receipt =
  selectedDefectBoundRecognizesActualValue
    bridge value (selectedDefectBelowCut receipt)

cmp98Equation119PointwiseSelectedCutLevel : ProofLevel
cmp98Equation119PointwiseSelectedCutLevel = machineChecked

literalCMP98ForgottenRelativeSelectedDefectBoundLevel : ProofLevel
literalCMP98ForgottenRelativeSelectedDefectBoundLevel = conditional
