{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PrintedOperatorChartWeldExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PRINTED OPERATOR DOMAIN <-> SELECTED PRINCIPAL CHART
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact as Printed
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log

record PrintedOperatorChartWeld
    {CoarseField : Set}
    (geometry : Historical.Path13FamilyGeometry CoarseField)
    (operators : Printed.PrintedSemanticOperators) : Set₁ where
  field
    selectedBallIsRelevant : ∀ y →
      Log.InSelectedBall (Historical.path13PrincipalChart geometry) y →
      Printed.RelevantY operators y
open PrintedOperatorChartWeld public

principalPointYRelevant :
  ∀ {CoarseField}
    {geometry : Historical.Path13FamilyGeometry CoarseField}
    {operators : Printed.PrintedSemanticOperators} →
  PrintedOperatorChartWeld geometry operators →
  ∀ value →
  Log.InPrincipalImage (Historical.path13PrincipalChart geometry) value →
  Printed.RelevantY operators
    (Log.principalLog (Historical.path13PrincipalChart geometry) value)
principalPointYRelevant weld value inImage =
  selectedBallIsRelevant weld
    (Log.principalLog _ value)
    (Log.principalLogMapsImage _ value inImage)

fromR159EverywhereRelevant :
  ∀ {CoarseField}
    (geometry : Historical.Path13FamilyGeometry CoarseField)
    (calculus : DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact.UniformAdjointDifferentialCalculus
      DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.SU2LieAlgebra) →
  PrintedOperatorChartWeld geometry (Printed.fromR159UniformCalculus calculus)
fromR159EverywhereRelevant geometry calculus = record
  { PrintedOperatorChartWeld.selectedBallIsRelevant =
      λ y _ → Printed.r159EveryYRelevant calculus y
  }

cmp98Path13PrintedOperatorChartWeldLevel : ProofLevel
cmp98Path13PrintedOperatorChartWeldLevel = machineChecked

literalCMP98Path13PrintedOperatorChartIdentificationLevel : ProofLevel
literalCMP98Path13PrintedOperatorChartIdentificationLevel = conditional
