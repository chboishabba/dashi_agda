{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13T3SelectedPrintedSemanticsExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): SELECTED-CHART T3 PRINTED SEMANTICS
--
-- This owner x-pollinates the existing T3 right-Jacobian surface into the
-- corrected CMP98 printed-role source path.  The only additional same-object
-- datum is normalization of the T3 chart ball against the selected Path13
-- principal chart.  Per-point relevance then follows mechanically.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3
import DASHI.Physics.YangMills.BalabanCMP98Path13T3PrintedOperatorAdapterExact as Adapter
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedOperatorChartWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredPrintedRoleSourceFamilyExact as Preferred
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record SelectedT3PrintedSemantics
    {CoarseField Scalar : Set}
    (representation :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField) : Set₁ where
  field
    dataSet : Adapter.T3Path13DexpData Scalar

    selectedBallWithinT3Chart : ∀ y →
      Log.InSelectedBall
        (DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact.path13PrincipalChart
          (Preferred.selectedGeometry representation)) y →
      T3.inChartBall dataSet y
open SelectedT3PrintedSemantics public

asSelectedPrintedOperatorSemantics :
  ∀ {CoarseField Scalar}
    {representation :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField} →
  SelectedT3PrintedSemantics {Scalar = Scalar} representation →
  Preferred.SelectedPrintedOperatorSemantics representation
asSelectedPrintedOperatorSemantics semantics = record
  { Preferred.SelectedPrintedOperatorSemantics.operators =
      Adapter.fromT3RightJacobian (dataSet semantics)
  ; Preferred.SelectedPrintedOperatorSemantics.chartWeld = record
      { Weld.PrintedOperatorChartWeld.selectedBallIsRelevant =
          selectedBallWithinT3Chart semantics
      }
  }

cmp98Path13T3SelectedPrintedSemanticsAdapterLevel : ProofLevel
cmp98Path13T3SelectedPrintedSemanticsAdapterLevel = machineChecked

-- A concrete T3 data set and its same-normalization chart identification remain
-- source/physical inputs; the per-point operator laws no longer do.
literalCMP98Path13T3SelectedNormalizationLevel : ProofLevel
literalCMP98Path13T3SelectedNormalizationLevel = conditional
