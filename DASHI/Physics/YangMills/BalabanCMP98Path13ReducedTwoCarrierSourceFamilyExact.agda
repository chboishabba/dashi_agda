{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): REDUCED SHORTEST SOURCE FAMILY
--
-- The compatibility-facing family still accepts one embedding per bond and one
-- principal-image proof per bond/point.  Both are now generated.  Radius-six
-- walk agreement is also constructed internally, so the final source-facing
-- input has exactly four coordinated payments:
--
--   * selected Path13 physical/variational background;
--   * one rational-real ring embedding;
--   * one existing Federbush convention family;
--   * one global selected-cut/operator-defect weld DEPENDENT on that exact
--     selected Path13 background.
--
-- No independent geometry object remains on the shortest route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact as Principal
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
-- Canonical shortest input: geometry is generated from selectedPhysical.
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

-- Only these four globally coordinated inhabitants remain source-facing.
literalCMP98Path13ReducedSourceFamilyInputsLevel : ProofLevel
literalCMP98Path13ReducedSourceFamilyInputsLevel = conditional
