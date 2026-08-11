module DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal finite Kronecker carrier for the twelve
-- Lie-coordinate/direction block-average rows.  This closes the pointwise row
-- selector missing from the dimension ledger and identifies the matrix
-- transpose of the literal average constraint with the physical constant
-- adjoint lift.  Consequently the already-proved normal operator 256 I is the
-- actual average-average Gram block, not merely an analogous physical map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Rational.Base as ℚ using (ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as Section

selectedBlockAverageRowFiniteSelector :
  Basis.FiniteSelector Average.SelectedBlockAverageRow4
selectedBlockAverageRowFiniteSelector =
  Basis.productFiniteSelector
    Basis.lieCoordinateFiniteSelector
    Basis.axis4FiniteSelector

selectedBlockAverageRowEnumerationExact :
  Basis.elements selectedBlockAverageRowFiniteSelector
  ≡ Average.selectedBlockAverageRows4
selectedBlockAverageRowEnumerationExact = refl

selectedBlockAverageRowDelta :
  Average.SelectedBlockAverageRow4 →
  Average.SelectedBlockAverageRow4 → ℚ
selectedBlockAverageRowDelta row column =
  Basis.kronecker
    (Basis.decide selectedBlockAverageRowFiniteSelector)
    column row

selectedBlockAverageRowDeltaActsAsIdentity :
  ∀ vector row →
  Sums.sumRational
    (Basis.elements selectedBlockAverageRowFiniteSelector)
    (λ column →
      selectedBlockAverageRowDelta row column * vector column)
  ≡ vector row
selectedBlockAverageRowDeltaActsAsIdentity vector row =
  trans
    (Sums.sumRationalCong
      (Basis.elements selectedBlockAverageRowFiniteSelector)
      (λ column →
        selectedBlockAverageRowDelta row column * vector column)
      (λ column →
        vector column
        * Basis.kronecker
            (Basis.decide selectedBlockAverageRowFiniteSelector)
            column row)
      (λ column → ℚRing.solve []))
    (Basis.selectorExact
      selectedBlockAverageRowFiniteSelector vector row)

selectedBlockAverageRowCarrier :
  Matrix.FiniteRationalCoordinates Average.SelectedBlockAverageRow4
selectedBlockAverageRowCarrier = record
  { Matrix.FiniteRationalCoordinates.coordinates =
      Basis.elements selectedBlockAverageRowFiniteSelector
  ; Matrix.FiniteRationalCoordinates.delta =
      selectedBlockAverageRowDelta
  ; Matrix.FiniteRationalCoordinates.deltaActsAsIdentity =
      selectedBlockAverageRowDeltaActsAsIdentity
  }

selectedBlockAverageTransposeApply :
  (Average.SelectedBlockAverageRow4 → ℚ) → KKT.StateVector
selectedBlockAverageTransposeApply multiplier =
  Rect.applyRectangular selectedBlockAverageRowCarrier
    (Rect.transposeRectangular
      Average.selectedBackgroundBlockAverageConstraintMatrix)
    multiplier

selectedBlockAverageMatrixBasisApplyExact :
  ∀ column row →
  Average.selectedBackgroundBlockAverageConstraintApply
    (Basis.physicalBasis column) row
  ≡ Average.selectedBackgroundBlockAverageConstraintMatrix row column
selectedBlockAverageMatrixBasisApplyExact column row =
  Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
    (Basis.physicalBasis column) row

selectedBlockAverageTransposeIsRowPairing :
  ∀ multiplier column →
  selectedBlockAverageTransposeApply multiplier column
  ≡ Section.selectedBlockAverageRowDot
      (Average.selectedBackgroundBlockAverageConstraintApply
        (Basis.physicalBasis column))
      multiplier
selectedBlockAverageTransposeIsRowPairing multiplier column =
  Sums.sumRationalCong
    (Basis.elements selectedBlockAverageRowFiniteSelector)
    (λ row →
      Average.selectedBackgroundBlockAverageConstraintMatrix row column
      * multiplier row)
    (λ row →
      Average.selectedBackgroundBlockAverageConstraintApply
        (Basis.physicalBasis column) row
      * multiplier row)
    (λ row →
      cong (_* multiplier row)
        (sym (selectedBlockAverageMatrixBasisApplyExact column row)))

selectedBlockAverageTransposeApplyExact :
  ∀ multiplier column →
  selectedBlockAverageTransposeApply multiplier column
  ≡ Section.selectedBlockAverageAdjointLift multiplier column
selectedBlockAverageTransposeApplyExact multiplier column =
  trans
    (selectedBlockAverageTransposeIsRowPairing multiplier column)
    (trans
      (Section.selectedBlockAverageAdjointExact
        (Basis.physicalBasis column) multiplier)
      (Basis.physicalBasisDotExact column
        (Section.selectedBlockAverageAdjointLift multiplier)))

selectedBlockAverageLiteralGramApply :
  (Average.SelectedBlockAverageRow4 → ℚ) →
  Average.SelectedBlockAverageRow4 → ℚ
selectedBlockAverageLiteralGramApply multiplier =
  Average.selectedBackgroundBlockAverageConstraintApply
    (selectedBlockAverageTransposeApply multiplier)

selectedBlockAverageLiteralGramExact :
  ∀ multiplier row →
  selectedBlockAverageLiteralGramApply multiplier row
  ≡ Section.siteCount * multiplier row
selectedBlockAverageLiteralGramExact multiplier row =
  trans
    (cong
      (λ state →
        Average.selectedBackgroundBlockAverageConstraintApply state row)
      (selectedBlockAverageTransposeApplyExact multiplier))
    (Section.selectedBlockAverageNormalExact multiplier row)

selectedBlockAverageLiteralGramInverseLeftExact :
  ∀ multiplier row →
  Section.selectedBlockAverageNormalInverseApply
    (selectedBlockAverageLiteralGramApply multiplier) row
  ≡ multiplier row
selectedBlockAverageLiteralGramInverseLeftExact multiplier row =
  trans
    (cong (Section.oneOverSiteCount *_)
      (selectedBlockAverageLiteralGramExact multiplier row))
    (ℚRing.solve-∀ (multiplier row))

selectedBlockAverageLiteralGramInverseRightExact :
  ∀ multiplier row →
  selectedBlockAverageLiteralGramApply
    (Section.selectedBlockAverageNormalInverseApply multiplier) row
  ≡ multiplier row
selectedBlockAverageLiteralGramInverseRightExact multiplier row =
  trans
    (selectedBlockAverageLiteralGramExact
      (Section.selectedBlockAverageNormalInverseApply multiplier) row)
    (ℚRing.solve-∀ (multiplier row))

selectedBlockAverageRowCarrierLevel : ProofLevel
selectedBlockAverageRowCarrierLevel = machineChecked

selectedBlockAverageTransposeLevel : ProofLevel
selectedBlockAverageTransposeLevel = machineChecked

selectedBlockAverageLiteralGramInverseLevel : ProofLevel
selectedBlockAverageLiteralGramInverseLevel = machineChecked
