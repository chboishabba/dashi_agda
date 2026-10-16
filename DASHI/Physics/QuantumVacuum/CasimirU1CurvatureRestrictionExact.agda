module DASHI.Physics.QuantumVacuum.CasimirU1CurvatureRestrictionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress

------------------------------------------------------------------------
-- CONDITIONAL CARTAN-U(1) CURVATURE REDUCTION
--
-- This theorem deliberately does not invent a continuum/non-flat curvature
-- producer.  Instead it says exactly what happens once such a same-object
-- producer supplies the usual local decomposition F = dA + [A,A] on the
-- selected field.  The already-proved Cartan image receipt makes the bracket
-- term zero, so the curvature reduces to the abelian exterior field strength.
------------------------------------------------------------------------

record SameObjectCurvatureFormula
    (SelectedField : Set)
    (selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra) : Set₁ where
  field
    exteriorFieldStrength : SelectedField → SelectedField → SU2Lie.SU2LieAlgebra
    curvatureFieldStrength : SelectedField → SelectedField → SU2Lie.SU2LieAlgebra

    curvatureEqualsExteriorPlusBracket :
      ∀ left right →
      curvatureFieldStrength left right
      ≡ SU2Lie.lieAdd
          (exteriorFieldStrength left right)
          (Bracket.lieBracket (selectedLieValue left) (selectedLieValue right))

open SameObjectCurvatureFormula public

cartanCurvatureReducesToExterior :
  ∀ {SelectedField : Set}
    {selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra} →
  (fieldImage : U1Stress.CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue) →
  (formula : SameObjectCurvatureFormula SelectedField selectedLieValue) →
  ∀ left right →
  curvatureFieldStrength formula left right
  ≡ exteriorFieldStrength formula left right
cartanCurvatureReducesToExterior fieldImage formula left right =
  trans
    (curvatureEqualsExteriorPlusBracket formula left right)
    (trans
      (cong
        (SU2Lie.lieAdd (exteriorFieldStrength formula left right))
        (U1Stress.restrictedFieldBracketZero fieldImage left right))
      (SU2Lie.lieZeroRight (exteriorFieldStrength formula left right)))

record CasimirU1CurvatureRestrictionBoundary : Set where
  constructor casimir-u1-curvature-restriction-boundary
  field
    cartesianU1FieldImageConsumed : Bool
    bracketZeroCompilerConsumed : Bool
    curvatureFormulaToAbelianFieldStrengthCompilerOwned : Bool
    secondBracketVanishingProofRequired : Bool
    sameObjectNondegenerateCurvatureFormulaAttached : Bool

open CasimirU1CurvatureRestrictionBoundary public

canonicalCasimirU1CurvatureRestrictionBoundary : CasimirU1CurvatureRestrictionBoundary
canonicalCasimirU1CurvatureRestrictionBoundary =
  casimir-u1-curvature-restriction-boundary true true true false false

data RemainingCasimirU1CurvatureRestrictionBlocker : Set where
  missingSameObjectNondegenerateCurvatureFormulaAttachment :
    RemainingCasimirU1CurvatureRestrictionBlocker

firstCurvatureRestrictionBlocker : RemainingCasimirU1CurvatureRestrictionBlocker
firstCurvatureRestrictionBlocker = missingSameObjectNondegenerateCurvatureFormulaAttachment

data AbelianReductionAutomaticallySuppliesPhysicalMaxwellCalibration : Set where

abelianReductionDoesNotSupplyPhysicalMaxwellCalibration :
  AbelianReductionAutomaticallySuppliesPhysicalMaxwellCalibration → ⊥
abelianReductionDoesNotSupplyPhysicalMaxwellCalibration ()

casimirU1CurvatureRestrictionReading : String
casimirU1CurvatureRestrictionReading =
  "For any SAME selected field carrying a nondegenerate curvature formula F=dA+[A,A], the canonical Cartan-U(1) field-image receipt and existing bracket-zero theorem compile F=dA exactly. The remaining field-strength payment is therefore attachment of the real selected nondegenerate curvature formula; no second abelian/bracket theorem is required. Physical Maxwell normalization, action equality, boundary conditions, and quantum-stress identification remain separate."
