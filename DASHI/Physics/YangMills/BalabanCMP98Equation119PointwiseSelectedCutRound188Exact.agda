{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PointwiseSelectedCutRound188Exact where

------------------------------------------------------------------------
-- ROUND188 A1 BIDI: THE SELECTED CUT ONLY NEEDS THE ACTUAL VALUE'S DEFECT
--
-- The older R170/R175 route identified a generic operator defect with the
-- selected chart defect for every group value.  The Eq. (119) consumer does not
-- need that universal theorem.  `SelectedBackgroundVariationalChartBridge`
-- already owns the cut, the selected defect algebra, the equality of that
-- algebra with the cut algebra, and the identification of cut admissibility
-- with the principal-image predicate.
--
-- Therefore for any ACTUAL value, a bound in the selected defect algebra is
-- enough to obtain principal-image admission directly.
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

cmp98Equation119PointwiseSelectedCutRound188Level : ProofLevel
cmp98Equation119PointwiseSelectedCutRound188Level = machineChecked

-- The universal kernel-defect equality is absent.  On the typed physical lane
-- the remaining quantitative theorem is exactly:
--
--   selectedDefect(forget(actual typed relative holonomy)) <= selected cut.
--
-- Once that is supplied, principal-image admission follows here.
literalCMP98ForgottenRelativeSelectedDefectBoundRound188Level : ProofLevel
literalCMP98ForgottenRelativeSelectedDefectBoundRound188Level = conditional
