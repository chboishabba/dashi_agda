{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13T3SelectedPrintedSemanticsExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3
import DASHI.Physics.YangMills.BalabanCMP98Path13T3PrintedOperatorAdapterExact as Adapter
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedOperatorChartWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredPrintedRoleSourceFamilyExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log

record SelectedT3PrintedSemantics
    {CoarseField Scalar : Set}
    (representation :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField) : Set₁ where
  field
    dataSet : Adapter.T3Path13DexpData Scalar

    selectedBallWithinT3Chart : ∀ y →
      Log.InSelectedBall
        (Historical.path13PrincipalChart
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

literalCMP98Path13T3SelectedNormalizationLevel : ProofLevel
literalCMP98Path13T3SelectedNormalizationLevel = conditional
