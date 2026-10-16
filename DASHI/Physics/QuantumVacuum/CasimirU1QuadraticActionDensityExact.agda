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

------------------------------------------------------------------------
-- CARTAN U(1) QUADRATIC ACTION-DENSITY COMPILER
--
-- The old finite YM action owner has definitionally zero curvature and is not
-- used here.  This theorem is conditional on the SAME real/nondegenerate
-- curvature object.  Once
--
--   F = dA + [A,A]
--
-- is attached and both the selected field and its exterior field strength lie
-- on the canonical Cartan axis, the previously proved bracket and invariant-
-- pairing restrictions force the quadratic Yang--Mills density to be the
-- ordinary Maxwell square.  The theorem is independent of the numerical
-- physical coupling: any common prefactor transports through the equality.
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
--
-- Integration/summation is deliberately abstract but proof-relevant: a real
-- selected action producer supplies one density functional plus its congruence
-- law.  Once supplied, no separate YM=Maxwell action theorem is required.
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

quadraticDensityDoesNotChoosePhysicalPrefactor :
  QuadraticDensityEqualityAutomaticallyChoosesPhysicalPrefactor → ⊥
quadraticDensityDoesNotChoosePhysicalPrefactor ()

quadraticDensityDoesNotSupplyActionFunctional :
  QuadraticDensityEqualityAutomaticallySuppliesActionFunctional → ⊥
quadraticDensityDoesNotSupplyActionFunctional ()

record CasimirU1QuadraticDensityBoundary : Set where
  constructor casimir-u1-quadratic-density-boundary
  field
    quadraticYMDensityToMaxwellDensityCompilerOwned : Bool
    sameObjectNondegenerateCurvatureStillRequired : Bool
    exteriorFieldStrengthCartanImageStillRequired : Bool
    physicalActionPrefactorStillRequired : Bool
    actionIntegrationStillRequired : Bool
    independentRestrictedYMMaxwellActionTheoremRequiredAfterInputs : Bool

open CasimirU1QuadraticDensityBoundary public

canonicalU1QuadraticDensityBoundary : CasimirU1QuadraticDensityBoundary
canonicalU1QuadraticDensityBoundary =
  casimir-u1-quadratic-density-boundary true true true true true false

casimirU1QuadraticDensityReading : String
casimirU1QuadraticDensityReading =
  "On the SAME selected nondegenerate curvature object, Cartan abelianization plus the live invariant-pairing theorem compile the quadratic Yang-Mills density exactly to the Maxwell field-strength square. The equality survives any common scalar prefactor. A proof-relevant DensityActionFunctional then lifts pointwise density equality to full action equality, so no second restricted-YM=Maxwell theorem is required after these inputs are attached. Still independent are the actual nondegenerate curvature producer, Cartan image of the exterior field strength, the physical electromagnetic action prefactor/coupling convention, and the real action integration/measure functional. The old zero-curvature finite YM action is not used."
