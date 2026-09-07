{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredMinimalSemanticSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PREFERRED MINIMAL-SEMANTIC SOURCE CUT
--
-- Preferred payments now are:
--   1. selected Path13 variational/operator physical representation;
--   2. foundational Bishop -> legacy-real bridge;
--   3. minimal semantic SU(2) calculus:
--        dExp-/J- inverse pair + reduced Ad_exp family;
--   4. selected cut threshold 1/24 <= r_cut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13MinimalSemanticCalculusExact as Minimal
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredDirectCalculusSourceFamilyExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PreferredMinimalSemanticPath13Inputs
    (CoarseField : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField

    bishopToLegacyReal : Bridge.BishopToDASHIRealBridge

    semanticCalculus : Minimal.MinimalPath13SemanticCalculus

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)
open PreferredMinimalSemanticPath13Inputs public

asPreferredDirectInputs :
  ∀ {CoarseField} →
  PreferredMinimalSemanticPath13Inputs CoarseField →
  Preferred.PreferredDirectCalculusPath13Inputs CoarseField
asPreferredDirectInputs inputs = record
  { Preferred.PreferredDirectCalculusPath13Inputs.selectedVariationalOperator =
      selectedVariationalOperator inputs
  ; Preferred.PreferredDirectCalculusPath13Inputs.bishopToLegacyReal =
      bishopToLegacyReal inputs
  ; Preferred.PreferredDirectCalculusPath13Inputs.differentialCalculus =
      Minimal.asUniformAdjointDifferentialCalculus (semanticCalculus inputs)
  ; Preferred.PreferredDirectCalculusPath13Inputs.cutThreshold =
      cutThreshold inputs
  }

preferredMinimalPath13Equation119QPrime :
  ∀ {CoarseField} →
  PreferredMinimalSemanticPath13Inputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
preferredMinimalPath13Equation119QPrime inputs =
  Preferred.preferredPath13Equation119QPrime
    (asPreferredDirectInputs inputs)

preferredMinimalPath13Equation119QPrimeExact :
  ∀ {CoarseField}
    (inputs : PreferredMinimalSemanticPath13Inputs CoarseField)
    step perturbation bond →
  preferredMinimalPath13Equation119QPrime inputs step perturbation bond
  ≡ Preferred.preferredPath13Equation119QPrime
      (asPreferredDirectInputs inputs) step perturbation bond
preferredMinimalPath13Equation119QPrimeExact inputs step perturbation bond = refl

cmp98Path13PreferredMinimalSemanticAdapterLevel : ProofLevel
cmp98Path13PreferredMinimalSemanticAdapterLevel = machineChecked

cmp98Path13FullUniformCalculusPrunedLevel : ProofLevel
cmp98Path13FullUniformCalculusPrunedLevel = machineChecked

literalCMP98Path13PreferredMinimalSemanticInputsLevel : ProofLevel
literalCMP98Path13PreferredMinimalSemanticInputsLevel = conditional
