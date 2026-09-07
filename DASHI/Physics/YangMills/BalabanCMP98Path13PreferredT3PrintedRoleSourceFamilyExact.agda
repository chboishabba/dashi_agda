{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredT3PrintedRoleSourceFamilyExact where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredPrintedRoleSourceFamilyExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP98Path13T3SelectedPrintedSemanticsExact as T3Sem
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PreferredT3PrintedRolePath13Inputs
    (CoarseField Scalar : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField
    bishopToLegacyReal : Bridge.BishopToDASHIRealBridge
    t3Semantics :
      T3Sem.SelectedT3PrintedSemantics {Scalar = Scalar}
        selectedVariationalOperator
    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)
open PreferredT3PrintedRolePath13Inputs public

asPreferredPrintedRoleInputs :
  ∀ {CoarseField Scalar} →
  PreferredT3PrintedRolePath13Inputs CoarseField Scalar →
  Preferred.PreferredPrintedRolePath13Inputs CoarseField
asPreferredPrintedRoleInputs inputs = record
  { Preferred.PreferredPrintedRolePath13Inputs.selectedVariationalOperator =
      selectedVariationalOperator inputs
  ; Preferred.PreferredPrintedRolePath13Inputs.bishopToLegacyReal =
      bishopToLegacyReal inputs
  ; Preferred.PreferredPrintedRolePath13Inputs.printedSemantics =
      T3Sem.asSelectedPrintedOperatorSemantics (t3Semantics inputs)
  ; Preferred.PreferredPrintedRolePath13Inputs.cutThreshold =
      cutThreshold inputs
  }

preferredT3PrintedRolePath13Equation119QPrime :
  ∀ {CoarseField Scalar} →
  PreferredT3PrintedRolePath13Inputs CoarseField Scalar →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
preferredT3PrintedRolePath13Equation119QPrime inputs =
  Preferred.preferredPrintedRolePath13Equation119QPrime
    (asPreferredPrintedRoleInputs inputs)

cmp98Path13PreferredT3PrintedRoleAdapterLevel : ProofLevel
cmp98Path13PreferredT3PrintedRoleAdapterLevel = machineChecked

literalCMP98Path13PreferredT3InputsLevel : ProofLevel
literalCMP98Path13PreferredT3InputsLevel = conditional
