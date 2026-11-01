{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13SplitT3SelectedSemanticsExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as T3
import DASHI.Physics.YangMills.BalabanCMP98Path13T3PrintedOperatorAdapterExact as Adapter
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact as Printed
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalPrincipalImageRouteExact as Principal
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log

record SplitSelectedT3PrintedSemantics
    {CoarseField Scalar : Set}
    (representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField) : Set₁ where
  field
    dataSet : Adapter.T3Path13DexpData Scalar

    selectedBallWithinT3Chart : ∀ y →
      let reduced = Principal.reducedGeometry representation
          geometry = Reduced.asPath13FamilyGeometry reduced
      in
      Log.InSelectedBall (Family.path13PrincipalChart geometry) y →
      T3.inChartBall dataSet y
open SplitSelectedT3PrintedSemantics public

operators :
  ∀ {CoarseField Scalar}
    {representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField} →
  SplitSelectedT3PrintedSemantics {Scalar = Scalar} representation →
  Printed.PrintedSemanticOperators
operators semantics = Adapter.fromT3RightJacobian (dataSet semantics)

principalPointYRelevant :
  ∀ {CoarseField Scalar}
    {representation : Split.SplitPath13PhysicalStandardRepresentation CoarseField}
    (semantics : SplitSelectedT3PrintedSemantics {Scalar = Scalar} representation)
    value →
  let reduced = Principal.reducedGeometry representation
      geometry = Reduced.asPath13FamilyGeometry reduced
  in
  Log.InPrincipalImage (Family.path13PrincipalChart geometry) value →
  Printed.RelevantY (operators semantics)
    (Log.principalLog (Family.path13PrincipalChart geometry) value)
principalPointYRelevant {representation = representation} semantics value inImage =
  let
    reduced = Principal.reducedGeometry representation
    geometry = Reduced.asPath13FamilyGeometry reduced
    chart = Family.path13PrincipalChart geometry
  in
  selectedBallWithinT3Chart semantics
    (Log.principalLog chart value)
    (Log.principalLogMapsImage chart value inImage)

cmp98Path13SplitT3SelectedSemanticsLevel : ProofLevel
cmp98Path13SplitT3SelectedSemanticsLevel = machineChecked

literalCMP98Path13SplitT3NormalizationLevel : ProofLevel
literalCMP98Path13SplitT3NormalizationLevel = conditional
