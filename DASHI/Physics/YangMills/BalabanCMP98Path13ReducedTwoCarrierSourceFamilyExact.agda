{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): REDUCED SHORTEST SOURCE FAMILY
--
-- Geometry and pointwise principal-image receipts are generated internally.
-- Two four-input source routes are retained:
--
--   A. compact historical route:
--      selected background + scalar embedding + Federbush family
--      + one mixed selected-cut/operator-defect weld;
--
--   B. provenance-separated radius-native route:
--      selected background/radius/operator-chart representation fibre
--      + scalar embedding + Federbush family
--      + the single cut-specific scalar receipt 1/24 <= r_cut.
--
-- Route B does not assert new existence.  It makes physical smallness, standard
-- representation and cut authority live at their proper typed owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact as BackgroundRadius
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact as Principal
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

------------------------------------------------------------------------
-- Compatibility reduced input.
------------------------------------------------------------------------

record ReducedPath13TwoCarrierSourceFamilyInputs
    (CoarseField : Set) : Set₁ where
  field
    geometry : Geometry.ReducedPath13FamilyGeometry CoarseField
    scalarEmbedding : R208.RationalRealRingEmbedding
    federbushConvention : R177.ExistingFederbushConventionFamily
    cutDefectWeld :
      Principal.Path13SelectedCutDefectWeld
        (Geometry.selectedPhysical geometry)

open ReducedPath13TwoCarrierSourceFamilyInputs public

asFullPath13TwoCarrierSourceFamilyInputs :
  ∀ {CoarseField} →
  ReducedPath13TwoCarrierSourceFamilyInputs CoarseField →
  Family.Path13TwoCarrierSourceFamilyInputs CoarseField
asFullPath13TwoCarrierSourceFamilyInputs inputs = record
  { Family.Path13TwoCarrierSourceFamilyInputs.geometry =
      Geometry.asPath13FamilyGeometry (geometry inputs)
  ; Family.Path13TwoCarrierSourceFamilyInputs.scalarEmbedding =
      scalarEmbedding inputs
  ; Family.Path13TwoCarrierSourceFamilyInputs.federbushConvention =
      federbushConvention inputs
  ; Family.Path13TwoCarrierSourceFamilyInputs.relativeContourInPrincipalImage =
      Principal.path13RelativeContourInPrincipalImage
        (geometry inputs) (cutDefectWeld inputs)
  }

reducedPath13Equation119QPrime :
  ∀ {CoarseField} →
  ReducedPath13TwoCarrierSourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
reducedPath13Equation119QPrime inputs =
  Family.path13Equation119QPrime
    (asFullPath13TwoCarrierSourceFamilyInputs inputs)

reducedPath13Equation119QPrimeAtBondExact :
  ∀ {CoarseField}
    (inputs : ReducedPath13TwoCarrierSourceFamilyInputs CoarseField)
    step perturbation bond →
  reducedPath13Equation119QPrime inputs step perturbation bond
  ≡ Family.path13Equation119QPrime
      (asFullPath13TwoCarrierSourceFamilyInputs inputs)
      step perturbation bond
reducedPath13Equation119QPrimeAtBondExact inputs step perturbation bond = refl

------------------------------------------------------------------------
-- Compact four-input route.
------------------------------------------------------------------------

record CanonicalPath13TwoCarrierSourceFamilyInputs
    (CoarseField : Set) : Set₁ where
  field
    selectedPhysical :
      PathTarget.SelectedPhysicalBackground13Instantiation
        CoarseField Lie.SU2LieAlgebra
    scalarEmbeddingCanonical : R208.RationalRealRingEmbedding
    federbushConventionCanonical : R177.ExistingFederbushConventionFamily
    cutDefectWeldCanonical :
      Principal.Path13SelectedCutDefectWeld selectedPhysical

open CanonicalPath13TwoCarrierSourceFamilyInputs public

asReducedPath13TwoCarrierSourceFamilyInputs :
  ∀ {CoarseField} →
  CanonicalPath13TwoCarrierSourceFamilyInputs CoarseField →
  ReducedPath13TwoCarrierSourceFamilyInputs CoarseField
asReducedPath13TwoCarrierSourceFamilyInputs inputs = record
  { geometry =
      Geometry.canonicalReducedPath13FamilyGeometry
        (selectedPhysical inputs)
  ; scalarEmbedding = scalarEmbeddingCanonical inputs
  ; federbushConvention = federbushConventionCanonical inputs
  ; cutDefectWeld = cutDefectWeldCanonical inputs
  }

asCanonicalFullPath13TwoCarrierSourceFamilyInputs :
  ∀ {CoarseField} →
  CanonicalPath13TwoCarrierSourceFamilyInputs CoarseField →
  Family.Path13TwoCarrierSourceFamilyInputs CoarseField
asCanonicalFullPath13TwoCarrierSourceFamilyInputs inputs =
  asFullPath13TwoCarrierSourceFamilyInputs
    (asReducedPath13TwoCarrierSourceFamilyInputs inputs)

canonicalPath13Equation119QPrime :
  ∀ {CoarseField} →
  CanonicalPath13TwoCarrierSourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
canonicalPath13Equation119QPrime inputs =
  reducedPath13Equation119QPrime
    (asReducedPath13TwoCarrierSourceFamilyInputs inputs)

canonicalPath13Equation119QPrimeAtBondExact :
  ∀ {CoarseField}
    (inputs : CanonicalPath13TwoCarrierSourceFamilyInputs CoarseField)
    step perturbation bond →
  canonicalPath13Equation119QPrime inputs step perturbation bond
  ≡ Family.path13Equation119QPrime
      (asCanonicalFullPath13TwoCarrierSourceFamilyInputs inputs)
      step perturbation bond
canonicalPath13Equation119QPrimeAtBondExact inputs step perturbation bond = refl

canonicalSourceGeometryBackgroundExact :
  ∀ {CoarseField}
    (inputs : CanonicalPath13TwoCarrierSourceFamilyInputs CoarseField) →
  Geometry.selectedPhysical
    (geometry (asReducedPath13TwoCarrierSourceFamilyInputs inputs))
  ≡ selectedPhysical inputs
canonicalSourceGeometryBackgroundExact inputs = refl

------------------------------------------------------------------------
-- Preferred four-input radius-native route.
------------------------------------------------------------------------

record RadiusNativePath13TwoCarrierSourceFamilyInputs
    (CoarseField : Set) : Set₁ where
  field
    selectedOperatorChart :
      OperatorChart.SelectedPath13OperatorChartRepresentation CoarseField

    scalarEmbeddingRadius : R208.RationalRealRingEmbedding
    federbushConventionRadius : R177.ExistingFederbushConventionFamily

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold selectedOperatorChart

open RadiusNativePath13TwoCarrierSourceFamilyInputs public

selectedBackgroundRadius :
  ∀ {CoarseField} →
  RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField →
  BackgroundRadius.SelectedPath13BackgroundWithRadius CoarseField
selectedBackgroundRadius inputs =
  OperatorChart.backgroundRadius (selectedOperatorChart inputs)

selectedPhysicalRadius :
  ∀ {CoarseField} →
  RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField →
  PathTarget.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra
selectedPhysicalRadius inputs =
  OperatorChart.selectedPhysical (selectedOperatorChart inputs)

radiusNativeReducedGeometry :
  ∀ {CoarseField} →
  RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField →
  Geometry.ReducedPath13FamilyGeometry CoarseField
radiusNativeReducedGeometry inputs =
  Geometry.canonicalReducedPath13FamilyGeometry
    (selectedPhysicalRadius inputs)

asRadiusNativeFullPath13TwoCarrierSourceFamilyInputs :
  ∀ {CoarseField} →
  RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField →
  Family.Path13TwoCarrierSourceFamilyInputs CoarseField
asRadiusNativeFullPath13TwoCarrierSourceFamilyInputs inputs = record
  { Family.Path13TwoCarrierSourceFamilyInputs.geometry =
      Geometry.asPath13FamilyGeometry (radiusNativeReducedGeometry inputs)
  ; Family.Path13TwoCarrierSourceFamilyInputs.scalarEmbedding =
      scalarEmbeddingRadius inputs
  ; Family.Path13TwoCarrierSourceFamilyInputs.federbushConvention =
      federbushConventionRadius inputs
  ; Family.Path13TwoCarrierSourceFamilyInputs.relativeContourInPrincipalImage =
      RadiusPrincipal.path13RelativeContourInPrincipalImageFromOperatorChart
        (selectedOperatorChart inputs)
        (cutThreshold inputs)
  }

radiusNativePath13Equation119QPrime :
  ∀ {CoarseField} →
  RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Family.Path13PositiveBond → Lie.SU2LieAlgebra
radiusNativePath13Equation119QPrime inputs =
  Family.path13Equation119QPrime
    (asRadiusNativeFullPath13TwoCarrierSourceFamilyInputs inputs)

radiusNativePath13Equation119QPrimeAtBondExact :
  ∀ {CoarseField}
    (inputs : RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField)
    step perturbation bond →
  radiusNativePath13Equation119QPrime inputs step perturbation bond
  ≡ Family.path13Equation119QPrime
      (asRadiusNativeFullPath13TwoCarrierSourceFamilyInputs inputs)
      step perturbation bond
radiusNativePath13Equation119QPrimeAtBondExact inputs step perturbation bond = refl

radiusNativeBackgroundSameObject :
  ∀ {CoarseField}
    (inputs : RadiusNativePath13TwoCarrierSourceFamilyInputs CoarseField) →
  Geometry.selectedPhysical (radiusNativeReducedGeometry inputs)
  ≡ OperatorChart.selectedPhysical (selectedOperatorChart inputs)
radiusNativeBackgroundSameObject inputs = refl

cmp98Path13ReducedSourceFamilyAdapterLevel : ProofLevel
cmp98Path13ReducedSourceFamilyAdapterLevel = machineChecked

cmp98Path13ReducedFieldDerivativeCompilerLevel : ProofLevel
cmp98Path13ReducedFieldDerivativeCompilerLevel = machineChecked

cmp98Path13PerBondPerPointSourceReceiptsPrunedLevel : ProofLevel
cmp98Path13PerBondPerPointSourceReceiptsPrunedLevel = machineChecked

cmp98Path13CanonicalFourInputSourceAdapterLevel : ProofLevel
cmp98Path13CanonicalFourInputSourceAdapterLevel = machineChecked

cmp98Path13CanonicalFourInputFieldDerivativeLevel : ProofLevel
cmp98Path13CanonicalFourInputFieldDerivativeLevel = machineChecked

cmp98Path13RadiusNativeSourceAdapterLevel : ProofLevel
cmp98Path13RadiusNativeSourceAdapterLevel = machineChecked

cmp98Path13RadiusNativeFieldDerivativeLevel : ProofLevel
cmp98Path13RadiusNativeFieldDerivativeLevel = machineChecked

cmp98Path13RadiusNativeSameObjectOwnershipLevel : ProofLevel
cmp98Path13RadiusNativeSameObjectOwnershipLevel =
  BackgroundRadius.cmp98Path13SelectedBackgroundRadiusFibreLevel

cmp98Path13RadiusNativeOperatorChartOwnershipLevel : ProofLevel
cmp98Path13RadiusNativeOperatorChartOwnershipLevel =
  OperatorChart.cmp98Path13SelectedOperatorChartRepresentationLevel

cmp98Path13RadiusNativeOneScalarCutResidualLevel : ProofLevel
cmp98Path13RadiusNativeOneScalarCutResidualLevel =
  RadiusPrincipal.cmp98Path13OperatorChartCutThresholdAdapterLevel

literalCMP98Path13ReducedSourceFamilyInputsLevel : ProofLevel
literalCMP98Path13ReducedSourceFamilyInputsLevel = conditional
