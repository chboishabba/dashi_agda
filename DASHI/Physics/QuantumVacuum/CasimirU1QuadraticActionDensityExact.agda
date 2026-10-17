module DASHI.Physics.QuantumVacuum.CasimirU1QuadraticActionDensityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as R
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct as Inner
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress
import DASHI.Physics.QuantumVacuum.CasimirU1CurvatureRestrictionExact as Curvature
import DASHI.Physics.QuantumVacuum.CasimirU1InvariantPairingRestrictionExact as Pairing
import DASHI.Physics.QuantumVacuum.CasimirSide4CartanCurvatureClosureExact as Side4Cartan
import DASHI.Physics.QuantumVacuum.CasimirFreeMaxwellActionNormalizationExact as Normalization

------------------------------------------------------------------------
-- CARTAN U(1) QUADRATIC ACTION-DENSITY COMPILER
------------------------------------------------------------------------

record ExteriorCartanImageReceipt
    {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra}
    (formula : Curvature.SameObjectCurvatureFormula
      SelectedField selectedLieValue) : Set₁ where
  field
    exteriorPhase :
      SelectedField → SelectedField → U1.U1LieAlgebra

    exteriorFieldStrengthIsEmbedded :
      ∀ left right →
      Curvature.exteriorFieldStrength formula left right
      ≡ U1.embedU1Lie (exteriorPhase left right)

open ExteriorCartanImageReceipt public

restrictedYMQuadraticDensity :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  Curvature.SameObjectCurvatureFormula SelectedField selectedLieValue →
  SelectedField → SelectedField → ℝ
restrictedYMQuadraticDensity formula left right =
  Inner.su2Dot
    (Curvature.curvatureFieldStrength formula left right)
    (Curvature.curvatureFieldStrength formula left right)

maxwellQuadraticDensity :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra}
    {formula : Curvature.SameObjectCurvatureFormula
      SelectedField selectedLieValue} →
  ExteriorCartanImageReceipt formula →
  SelectedField → SelectedField → ℝ
maxwellQuadraticDensity exteriorImage left right =
  R._*R_
    (exteriorPhase exteriorImage left right)
    (exteriorPhase exteriorImage left right)

restrictedYMQuadraticDensityIsMaxwell :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  (fieldImage :
    U1Stress.CanonicalCartanU1FieldImageReceipt
      SelectedField selectedLieValue) →
  (formula : Curvature.SameObjectCurvatureFormula
    SelectedField selectedLieValue) →
  (exteriorImage : ExteriorCartanImageReceipt formula) →
  ∀ left right →
  restrictedYMQuadraticDensity formula left right
  ≡ maxwellQuadraticDensity exteriorImage left right
restrictedYMQuadraticDensityIsMaxwell
    fieldImage formula exteriorImage left right =
  trans
    (cong₂ Inner.su2Dot
      (Curvature.cartanCurvatureReducesToExterior
        fieldImage formula left right)
      (Curvature.cartanCurvatureReducesToExterior
        fieldImage formula left right))
    (trans
      (cong₂ Inner.su2Dot
        (exteriorFieldStrengthIsEmbedded exteriorImage left right)
        (exteriorFieldStrengthIsEmbedded exteriorImage left right))
      (Pairing.u1EmbeddedInvariantNormSquare
        (exteriorPhase exteriorImage left right)))

restrictedYMQuadraticDensityWithCommonPrefactor :
  ℝ →
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  Curvature.SameObjectCurvatureFormula SelectedField selectedLieValue →
  SelectedField → SelectedField → ℝ
restrictedYMQuadraticDensityWithCommonPrefactor prefactor formula left right =
  R._*R_ prefactor (restrictedYMQuadraticDensity formula left right)

maxwellQuadraticDensityWithCommonPrefactor :
  ℝ →
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra}
    {formula : Curvature.SameObjectCurvatureFormula
      SelectedField selectedLieValue} →
  ExteriorCartanImageReceipt formula →
  SelectedField → SelectedField → ℝ
maxwellQuadraticDensityWithCommonPrefactor prefactor exteriorImage left right =
  R._*R_ prefactor (maxwellQuadraticDensity exteriorImage left right)

restrictedYMQuadraticDensityWithCommonPrefactorIsMaxwell :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  (fieldImage :
    U1Stress.CanonicalCartanU1FieldImageReceipt
      SelectedField selectedLieValue) →
  (formula : Curvature.SameObjectCurvatureFormula
    SelectedField selectedLieValue) →
  (exteriorImage : ExteriorCartanImageReceipt formula) →
  (prefactor : ℝ) →
  ∀ left right →
  restrictedYMQuadraticDensityWithCommonPrefactor
    prefactor formula left right
  ≡ maxwellQuadraticDensityWithCommonPrefactor
      prefactor exteriorImage left right
restrictedYMQuadraticDensityWithCommonPrefactorIsMaxwell
    fieldImage formula exteriorImage prefactor left right =
  cong
    (R._*R_ prefactor)
    (restrictedYMQuadraticDensityIsMaxwell
      fieldImage formula exteriorImage left right)

------------------------------------------------------------------------
-- ACTION-FUNCTIONAL LIFT
------------------------------------------------------------------------

record DensityActionFunctional (SelectedField : Set) : Set₁ where
  field
    ActionValue : Set
    integrateDensity :
      (SelectedField → SelectedField → ℝ) → ActionValue
    respectsPointwiseDensityEquality :
      ∀ leftDensity rightDensity →
      (∀ left right → leftDensity left right ≡ rightDensity left right) →
      integrateDensity leftDensity ≡ integrateDensity rightDensity

open DensityActionFunctional public

restrictedYMActionFromDensity :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  (functional : DensityActionFunctional SelectedField) →
  (prefactor : ℝ) →
  Curvature.SameObjectCurvatureFormula SelectedField selectedLieValue →
  ActionValue functional
restrictedYMActionFromDensity functional prefactor formula =
  integrateDensity functional
    (restrictedYMQuadraticDensityWithCommonPrefactor prefactor formula)

maxwellActionFromDensity :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra}
    {formula : Curvature.SameObjectCurvatureFormula
      SelectedField selectedLieValue} →
  (functional : DensityActionFunctional SelectedField) →
  (prefactor : ℝ) →
  ExteriorCartanImageReceipt formula →
  ActionValue functional
maxwellActionFromDensity functional prefactor exteriorImage =
  integrateDensity functional
    (maxwellQuadraticDensityWithCommonPrefactor prefactor exteriorImage)

restrictedYMActionEqualsMaxwellFromSameDensityFunctional :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  (fieldImage :
    U1Stress.CanonicalCartanU1FieldImageReceipt
      SelectedField selectedLieValue) →
  (formula : Curvature.SameObjectCurvatureFormula
    SelectedField selectedLieValue) →
  (exteriorImage : ExteriorCartanImageReceipt formula) →
  (functional : DensityActionFunctional SelectedField) →
  (prefactor : ℝ) →
  restrictedYMActionFromDensity functional prefactor formula
  ≡ maxwellActionFromDensity functional prefactor exteriorImage
restrictedYMActionEqualsMaxwellFromSameDensityFunctional
    fieldImage formula exteriorImage functional prefactor =
  respectsPointwiseDensityEquality functional
    (restrictedYMQuadraticDensityWithCommonPrefactor prefactor formula)
    (maxwellQuadraticDensityWithCommonPrefactor prefactor exteriorImage)
    (restrictedYMQuadraticDensityWithCommonPrefactorIsMaxwell
      fieldImage formula exteriorImage prefactor)

------------------------------------------------------------------------
-- Status / firewalls.
------------------------------------------------------------------------

data QuadraticDensityEqualityAutomaticallyChoosesPhysicalPrefactor : Set where
data QuadraticDensityEqualityAutomaticallySuppliesActionFunctional : Set where
data FlatSide4CartanCurlAutomaticallyIdentifiesSelectedNonlinearExteriorField : Set where

quadraticDensityDoesNotChoosePhysicalPrefactor :
  QuadraticDensityEqualityAutomaticallyChoosesPhysicalPrefactor → ⊥
quadraticDensityDoesNotChoosePhysicalPrefactor ()

quadraticDensityDoesNotSupplyActionFunctional :
  QuadraticDensityEqualityAutomaticallySuppliesActionFunctional → ⊥
quadraticDensityDoesNotSupplyActionFunctional ()

flatSide4CartanCurlDoesNotIdentifySelectedNonlinearExteriorField :
  FlatSide4CartanCurlAutomaticallyIdentifiesSelectedNonlinearExteriorField → ⊥
flatSide4CartanCurlDoesNotIdentifySelectedNonlinearExteriorField ()

side4CartanCurvatureBoundary : Side4Cartan.CasimirSide4CartanCurvatureBoundary
side4CartanCurvatureBoundary = Side4Cartan.canonicalSide4CartanCurvatureBoundary

freeMaxwellNormalizationBoundary : Normalization.CasimirFreeMaxwellNormalizationBoundary
freeMaxwellNormalizationBoundary = Normalization.canonicalFreeMaxwellNormalizationBoundary

record CasimirU1QuadraticDensityBoundary : Set where
  constructor casimir-u1-quadratic-density-boundary
  field
    quadraticYMDensityToMaxwellDensityCompilerOwned : Bool
    sameObjectNondegenerateCurvatureStillRequired : Bool
    side4CartanCurlClosureCompilerAvailable : Bool
    independentFiniteCartanCurlClosurePaymentRequired : Bool
    selectedNonlinearExteriorCartanTransportStillRequired : Bool
    freeMaxwellNormalizationStillRequired : Bool
    measuredAlphaEMRequiredForIdealQuadraticDensity : Bool
    actionIntegrationStillRequired : Bool
    independentRestrictedYMMaxwellActionTheoremRequiredAfterInputs : Bool

open CasimirU1QuadraticDensityBoundary public

canonicalU1QuadraticDensityBoundary : CasimirU1QuadraticDensityBoundary
canonicalU1QuadraticDensityBoundary =
  casimir-u1-quadratic-density-boundary
    true true true false true true false true false

casimirU1QuadraticDensityReading : String
casimirU1QuadraticDensityReading =
  "On the SAME selected nondegenerate curvature object, Cartan abelianization plus the invariant pairing compile the Yang-Mills quadratic density to the Maxwell square, and one density functional lifts that to action equality. The literal side-four donor now also proves finite Cartan closure of the curl, so no second finite dA-in-Cartan calculation is required. What remains is same-object transport from the selected nonlinear curvature/exterior derivative to that concrete Cartan-curvature realization, plus the actual nondegenerate curvature producer and action integration. FreeMaxwellActionNormalization supplies the common field/generator/prefactor convention; measured alpha_EM is separate phenomenology rather than an ideal Casimir density input."
