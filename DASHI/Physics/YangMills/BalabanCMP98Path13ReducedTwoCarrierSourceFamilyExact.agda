{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): REDUCED SHORTEST SOURCE FAMILY
--
-- The compatibility-facing family still accepts one embedding per bond and one
-- principal-image proof per bond/point.  Both are now generated.  Radius-six
-- walk agreement is also constructed internally.
--
-- Two source routes are retained:
--
--   A. the compact four-input historical cut/defect weld;
--   B. a provenance-separated native-radius route in which physical link
--      smallness is the already-owned Path13 `SelectedInverseLinkRadius13`,
--      standard SU(2) operator representation is source-independent, and only
--      three selected-chart recognition facts remain at the cut.
--
-- Route B is not claimed to have fewer fields.  Its gain is typed ownership:
-- physical radius, standard representation and selected chart recognition can
-- no longer be conflated into one opaque weld.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact as Principal
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as RadiusOperator
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

------------------------------------------------------------------------
-- Compatibility reduced input: retains an explicit reduced geometry object.
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
-- Canonical compact route: geometry is generated from selectedPhysical.
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
-- Provenance-separated native-radius route.
------------------------------------------------------------------------

record RadiusNativePath13TwoCarrierSourceFamilyInputs
    (CoarseField : Set) : Set₁ where
  field
    selectedPhysicalRadius :
      PathTarget.SelectedPhysicalBackground13Instantiation
        CoarseField Lie.SU2LieAlgebra

    nativeInverseLinkRadius :
      Background.SelectedInverseLinkRadius13
        (PathTarget.path13Background selectedPhysicalRadius)

    scalarEmbeddingRadius : R208.RationalRealRingEmbedding
    federbushConventionRadius : R177.ExistingFederbushConventionFamily

    operatorRepresentation :
      RadiusOperator.ExactRationalSU2OperatorDefectRepresentation

    cutRecognition :
      RadiusPrincipal.Path13RadiusCutRecognition
        selectedPhysicalRadius operatorRepresentation

open RadiusNativePath13TwoCarrierSourceFamilyInputs public

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
      RadiusPrincipal.path13RelativeContourInPrincipalImageFromRadius
        (radiusNativeReducedGeometry inputs)
        (nativeInverseLinkRadius inputs)
        (operatorRepresentation inputs)
        (cutRecognition inputs)
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
  ≡ selectedPhysicalRadius inputs
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

-- The compact four-input route remains the fewest top-level fields.  The
-- radius-native route is retained because it separates physical smallness from
-- standard representation and chart recognition, and reuses the exact Path13
-- radius already consumed by the coercivity lane.
literalCMP98Path13ReducedSourceFamilyInputsLevel : ProofLevel
literalCMP98Path13ReducedSourceFamilyInputsLevel = conditional
