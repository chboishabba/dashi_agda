{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13BishopBridgeSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): FOUNDATIONAL BISHOP-BRIDGE SOURCE ADAPTER
--
-- Replace the bespoke YM `RationalRealRingEmbedding` source payment by the
-- repository-wide foundational Bishop -> legacy-real bridge.  The rational
-- embedding and all 0/1/+/*/order laws are compiled internally.
--
-- This is an ownership reduction, not an inhabitance claim for the legacy-real
-- bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact as R208Bridge
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13VariationalRadiusSourceFamilyExact as Existing
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record BishopBridgePath13SourceFamilyInputs
    (CoarseField : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField

    bishopToLegacyReal : Bridge.BishopToDASHIRealBridge

    federbushConvention : R177.ExistingFederbushConventionFamily

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)

open BishopBridgePath13SourceFamilyInputs public

asVariationalRadiusInputs :
  ∀ {CoarseField} →
  BishopBridgePath13SourceFamilyInputs CoarseField →
  Existing.VariationalRadiusPath13SourceFamilyInputs CoarseField
asVariationalRadiusInputs inputs = record
  { Existing.VariationalRadiusPath13SourceFamilyInputs.selectedVariationalOperator =
      selectedVariationalOperator inputs
  ; Existing.VariationalRadiusPath13SourceFamilyInputs.scalarEmbedding =
      R208Bridge.bishopBridgeRingEmbedding (bishopToLegacyReal inputs)
  ; Existing.VariationalRadiusPath13SourceFamilyInputs.federbushConvention =
      federbushConvention inputs
  ; Existing.VariationalRadiusPath13SourceFamilyInputs.cutThreshold =
      cutThreshold inputs
  }

bishopBridgePath13Equation119QPrime :
  ∀ {CoarseField} →
  BishopBridgePath13SourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
bishopBridgePath13Equation119QPrime inputs =
  Existing.variationalRadiusPath13Equation119QPrime
    (asVariationalRadiusInputs inputs)

bishopBridgePath13Equation119QPrimeExact :
  ∀ {CoarseField}
    (inputs : BishopBridgePath13SourceFamilyInputs CoarseField)
    step perturbation bond →
  bishopBridgePath13Equation119QPrime inputs step perturbation bond
  ≡ Existing.variationalRadiusPath13Equation119QPrime
      (asVariationalRadiusInputs inputs) step perturbation bond
bishopBridgePath13Equation119QPrimeExact inputs step perturbation bond = refl

cmp98Path13BishopBridgeSourceAdapterLevel : ProofLevel
cmp98Path13BishopBridgeSourceAdapterLevel = machineChecked

cmp98Path13BespokeR208EmbeddingPrunedLevel : ProofLevel
cmp98Path13BespokeR208EmbeddingPrunedLevel = machineChecked

literalCMP98Path13BishopBridgeSourceInputsLevel : ProofLevel
literalCMP98Path13BishopBridgeSourceInputsLevel = conditional
