{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13VariationalRadiusSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PREFERRED VARIATIONAL-RADIUS SOURCE ADAPTER
--
-- The older radius-native adapter still accepts a fully assembled
-- `SelectedPath13OperatorChartRepresentation`.  This owner pushes the source
-- boundary one level inward:
--
--   selected Path13 variational/physical representation
--     -> native inverse-link radius
--     -> same-object background/radius fibre
--     -> operator/chart compatibility fibre
--     -> existing radius-native Eq. (119) compiler.
--
-- Hence `SelectedInverseLinkRadius13` is no longer a primitive source payment
-- on this route.  It is theorem output from the selected variational fine-bond
-- estimate plus the physical defect representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact as Existing
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record VariationalRadiusPath13SourceFamilyInputs
    (CoarseField : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField

    scalarEmbedding : R208.RationalRealRingEmbedding
    federbushConvention : R177.ExistingFederbushConventionFamily

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)

open VariationalRadiusPath13SourceFamilyInputs public

asRadiusNativeInputs :
  ∀ {CoarseField} →
  VariationalRadiusPath13SourceFamilyInputs CoarseField →
  Existing.RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField
asRadiusNativeInputs inputs = record
  { Existing.RadiusNativePath13TwoCarrierSourceFamilyInputs.selectedOperatorChart =
      OperatorChart.asSelectedPath13OperatorChartRepresentation
        (selectedVariationalOperator inputs)
  ; Existing.RadiusNativePath13TwoCarrierSourceFamilyInputs.scalarEmbeddingRadius =
      scalarEmbedding inputs
  ; Existing.RadiusNativePath13TwoCarrierSourceFamilyInputs.federbushConventionRadius =
      federbushConvention inputs
  ; Existing.RadiusNativePath13TwoCarrierSourceFamilyInputs.cutThreshold =
      cutThreshold inputs
  }

variationalRadiusPath13Equation119QPrime :
  ∀ {CoarseField} →
  VariationalRadiusPath13SourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
variationalRadiusPath13Equation119QPrime inputs =
  Existing.radiusNativePath13Equation119QPrime (asRadiusNativeInputs inputs)

variationalRadiusPath13Equation119QPrimeExact :
  ∀ {CoarseField}
    (inputs : VariationalRadiusPath13SourceFamilyInputs CoarseField)
    step perturbation bond →
  variationalRadiusPath13Equation119QPrime inputs step perturbation bond
  ≡ Existing.radiusNativePath13Equation119QPrime
      (asRadiusNativeInputs inputs) step perturbation bond
variationalRadiusPath13Equation119QPrimeExact inputs step perturbation bond = refl

cmp98Path13VariationalRadiusSourceAdapterLevel : ProofLevel
cmp98Path13VariationalRadiusSourceAdapterLevel = machineChecked

cmp98Path13NativeRadiusNoLongerPrimitiveLevel : ProofLevel
cmp98Path13NativeRadiusNoLongerPrimitiveLevel = machineChecked

-- Remaining source-facing contents of the first top-level object are now the
-- selected background and physical representation identifications.  This file
-- does not construct those source facts, the real embedding, Federbush family,
-- or scalar cut threshold.
literalCMP98Path13VariationalRadiusSourceInputsLevel : ProofLevel
literalCMP98Path13VariationalRadiusSourceInputsLevel = conditional
