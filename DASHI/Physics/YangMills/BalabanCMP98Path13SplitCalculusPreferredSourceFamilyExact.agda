{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13SplitCalculusPreferredSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PREFERRED SPLIT-CALCULUS SOURCE CUT
--
-- Refine the direct-calculus payment into its two genuine coordinates:
--   * exp/log differential data;
--   * Ad_{exp Y} realization plus inverse law.
--
-- The historical R159 bundle is reconstructed internally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13UniformCalculusDecompositionExact as Split
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredDirectCalculusSourceFamilyExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PreferredSplitCalculusPath13Inputs
    (CoarseField : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField

    bishopToLegacyReal : Bridge.BishopToDASHIRealBridge

    expLogDifferential :
      Dexp.SU2ExpLogDifferentialData Lie.SU2LieAlgebra

    adjointRealization :
      Split.AdjointExpRealization Lie.SU2LieAlgebra

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)
open PreferredSplitCalculusPath13Inputs public

splitCalculus :
  ∀ {CoarseField} →
  PreferredSplitCalculusPath13Inputs CoarseField →
  Split.SplitUniformAdjointDifferentialCalculus Lie.SU2LieAlgebra
splitCalculus inputs = record
  { Split.SplitUniformAdjointDifferentialCalculus.differential =
      expLogDifferential inputs
  ; Split.SplitUniformAdjointDifferentialCalculus.adjoint =
      adjointRealization inputs
  }

asPreferredDirectInputs :
  ∀ {CoarseField} →
  PreferredSplitCalculusPath13Inputs CoarseField →
  Preferred.PreferredDirectCalculusPath13Inputs CoarseField
asPreferredDirectInputs inputs = record
  { Preferred.PreferredDirectCalculusPath13Inputs.selectedVariationalOperator =
      selectedVariationalOperator inputs
  ; Preferred.PreferredDirectCalculusPath13Inputs.bishopToLegacyReal =
      bishopToLegacyReal inputs
  ; Preferred.PreferredDirectCalculusPath13Inputs.differentialCalculus =
      Split.asUniformAdjointDifferentialCalculus (splitCalculus inputs)
  ; Preferred.PreferredDirectCalculusPath13Inputs.cutThreshold =
      cutThreshold inputs
  }

preferredSplitPath13Equation119QPrime :
  ∀ {CoarseField} →
  PreferredSplitCalculusPath13Inputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
preferredSplitPath13Equation119QPrime inputs =
  Preferred.preferredPath13Equation119QPrime
    (asPreferredDirectInputs inputs)

preferredSplitPath13Equation119QPrimeExact :
  ∀ {CoarseField}
    (inputs : PreferredSplitCalculusPath13Inputs CoarseField)
    step perturbation bond →
  preferredSplitPath13Equation119QPrime inputs step perturbation bond
  ≡ Preferred.preferredPath13Equation119QPrime
      (asPreferredDirectInputs inputs) step perturbation bond
preferredSplitPath13Equation119QPrimeExact inputs step perturbation bond = refl

cmp98Path13SplitCalculusPreferredAdapterLevel : ProofLevel
cmp98Path13SplitCalculusPreferredAdapterLevel = machineChecked

cmp98Path13UniformCalculusNoLongerPrimitiveLevel : ProofLevel
cmp98Path13UniformCalculusNoLongerPrimitiveLevel = machineChecked

literalCMP98Path13ExpLogDifferentialInputsLevel : ProofLevel
literalCMP98Path13ExpLogDifferentialInputsLevel = conditional

literalCMP98Path13AdjointRealizationInputsLevel : ProofLevel
literalCMP98Path13AdjointRealizationInputsLevel = conditional
