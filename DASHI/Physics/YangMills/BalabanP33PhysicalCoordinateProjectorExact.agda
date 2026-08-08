module DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Volker Bach, Thomas Chen, Juerg Froehlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
--
-- Construct an actual finite diagonal projector on the repository's literal
-- 3072-coordinate side-four SU(2) carrier.  A Boolean coordinate mask defines
-- both a vector projector and its diagonal matrix.  The module proves:
--
--   P^2 = P pointwise,
--   <u,Pv> = <Pu,v>,
--   the image/fixed-point characterization,
--   a literal basis resolution of P,
--   (PMP)v = P(M(Pv)),
--   v^T(PMP)v = (Pv)^T M (Pv),
--
-- and preservation of matrix symmetry.  No abstract basis or independently
-- supplied matrix/form compatibility field is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasEntryDecayExact as Entry

Coordinate : Set
Coordinate = Physical.PhysicalSU2Coordinate4

PhysicalVector : Set
PhysicalVector = Coordinate → ℚ

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

PhysicalCoordinateMask : Set
PhysicalCoordinateMask = Coordinate → Bool

maskCoefficient : Bool → ℚ
maskCoefficient false = 0ℚ
maskCoefficient true = 1ℚ

maskSelect : Bool → ℚ → ℚ
maskSelect selected value = maskCoefficient selected * value

maskSelectIdempotent : ∀ selected value →
  maskSelect selected (maskSelect selected value)
  ≡ maskSelect selected value
maskSelectIdempotent false value = ℚRing.solve-∀ value
maskSelectIdempotent true value = ℚRing.solve-∀ value

maskSelectProductMove : ∀ selected left right →
  left * maskSelect selected right
  ≡ maskSelect selected left * right
maskSelectProductMove false left right = ℚRing.solve-∀ left right
maskSelectProductMove true left right = ℚRing.solve-∀ left right

physicalCoordinateProject :
  PhysicalCoordinateMask → PhysicalVector → PhysicalVector
physicalCoordinateProject mask vector coordinate =
  maskSelect (mask coordinate) (vector coordinate)

physicalConstraintProjectorIdempotent : ∀ mask vector coordinate →
  physicalCoordinateProject mask
    (physicalCoordinateProject mask vector) coordinate
  ≡ physicalCoordinateProject mask vector coordinate
physicalConstraintProjectorIdempotent mask vector coordinate =
  maskSelectIdempotent (mask coordinate) (vector coordinate)

physicalConstraintProjectorSelfAdjoint : ∀ mask left right →
  Physical.physicalCoordinateDot left
    (physicalCoordinateProject mask right)
  ≡ Physical.physicalCoordinateDot
      (physicalCoordinateProject mask left) right
physicalConstraintProjectorSelfAdjoint mask left right =
  Sums.sumRationalCong
    Physical.physicalSU2Coordinates4
    (λ coordinate →
      left coordinate
        * physicalCoordinateProject mask right coordinate)
    (λ coordinate →
      physicalCoordinateProject mask left coordinate
        * right coordinate)
    (λ coordinate →
      maskSelectProductMove
        (mask coordinate) (left coordinate) (right coordinate))

record PhysicalConstraintProjectorImage
    (mask : PhysicalCoordinateMask)
    (vector : PhysicalVector) : Set where
  field
    outsideMaskZero : ∀ coordinate →
      mask coordinate ≡ false →
      vector coordinate ≡ 0ℚ

open PhysicalConstraintProjectorImage public

physicalConstraintProjectorImageCharacterizationForward :
  ∀ mask vector →
  PhysicalConstraintProjectorImage mask vector →
  ∀ coordinate →
  physicalCoordinateProject mask vector coordinate ≡ vector coordinate
physicalConstraintProjectorImageCharacterizationForward
    mask vector image coordinate
  with mask coordinate
... | true = ℚRing.solve-∀ (vector coordinate)
... | false =
  trans
    (ℚRing.solve-∀ (vector coordinate))
    (sym (outsideMaskZero image coordinate refl))

physicalConstraintProjectorImageCharacterizationBackward :
  ∀ mask vector →
  (∀ coordinate →
    physicalCoordinateProject mask vector coordinate ≡ vector coordinate) →
  PhysicalConstraintProjectorImage mask vector
physicalConstraintProjectorImageCharacterizationBackward
    mask vector fixed =
  record
    { outsideMaskZero = λ coordinate maskFalse →
        trans
          (sym (fixed coordinate))
          (trans
            (cong
              (λ selected →
                maskSelect selected (vector coordinate))
              maskFalse)
            (ℚRing.solve-∀ (vector coordinate)))
    }

physicalCoordinateProjectLiesInImage : ∀ mask vector →
  PhysicalConstraintProjectorImage mask
    (physicalCoordinateProject mask vector)
physicalCoordinateProjectLiesInImage mask vector =
  physicalConstraintProjectorImageCharacterizationBackward
    mask
    (physicalCoordinateProject mask vector)
    (physicalConstraintProjectorIdempotent mask vector)

maskProjectorMatrix :
  PhysicalCoordinateMask → PhysicalMatrix
maskProjectorMatrix mask row column =
  maskSelect (mask row)
    (maskSelect (mask column)
      (Calibration.identityEntry row column))

projectedPhysicalMatrix :
  PhysicalCoordinateMask → PhysicalMatrix → PhysicalMatrix
projectedPhysicalMatrix mask matrix row column =
  maskSelect (mask row)
    (maskSelect (mask column) (matrix row column))

projectedPhysicalMatrixSelfAdjoint :
  ∀ mask matrix →
  (∀ left right → matrix left right ≡ matrix right left) →
  ∀ left right →
  projectedPhysicalMatrix mask matrix left right
  ≡ projectedPhysicalMatrix mask matrix right left
projectedPhysicalMatrixSelfAdjoint mask matrix symmetric left right
  with mask left | mask right
... | false | false = ℚRing.solve []
... | false | true = ℚRing.solve []
... | true | false = ℚRing.solve []
... | true | true = cong (λ selected → 1ℚ * (1ℚ * selected))
    (symmetric left right)

projectedPhysicalMatrixApplyExact :
  ∀ mask matrix vector row →
  Physical.physicalMatrixApply
    (projectedPhysicalMatrix mask matrix) vector row
  ≡ physicalCoordinateProject mask
      (Physical.physicalMatrixApply matrix
        (physicalCoordinateProject mask vector))
      row
projectedPhysicalMatrixApplyExact mask matrix vector row =
  let
    selectedRow = maskCoefficient (mask row)

    pointwise : ∀ column →
      projectedPhysicalMatrix mask matrix row column
        * vector column
      ≡ selectedRow
        * (matrix row column
          * physicalCoordinateProject mask vector column)
    pointwise column with mask row | mask column
    ... | false | false =
      ℚRing.solve-∀ (matrix row column) (vector column)
    ... | false | true =
      ℚRing.solve-∀ (matrix row column) (vector column)
    ... | true | false =
      ℚRing.solve-∀ (matrix row column) (vector column)
    ... | true | true =
      ℚRing.solve-∀ (matrix row column) (vector column)

    rewritten =
      Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ column →
          projectedPhysicalMatrix mask matrix row column
            * vector column)
        (λ column →
          selectedRow
            * (matrix row column
              * physicalCoordinateProject mask vector column))
        pointwise

    factored =
      Sums.sumRationalScale
        selectedRow
        Physical.physicalSU2Coordinates4
        (λ column →
          matrix row column
            * physicalCoordinateProject mask vector column)
  in
  trans rewritten
    (trans factored
      (ℚRing.solve-∀
        (Physical.physicalMatrixApply matrix
          (physicalCoordinateProject mask vector) row)))

projectedPhysicalQuadratic :
  PhysicalCoordinateMask → PhysicalMatrix → PhysicalVector → ℚ
projectedPhysicalQuadratic mask matrix vector =
  Physical.physicalMatrixQuadratic matrix
    (physicalCoordinateProject mask vector)

projectedLiteralHessianMatrixRepresentsForm :
  ∀ mask matrix vector →
  Physical.physicalMatrixQuadratic
    (projectedPhysicalMatrix mask matrix) vector
  ≡ projectedPhysicalQuadratic mask matrix vector
projectedLiteralHessianMatrixRepresentsForm mask matrix vector =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ row →
        vector row
          * Physical.physicalMatrixApply
              (projectedPhysicalMatrix mask matrix) vector row)
      (λ row →
        vector row
          * physicalCoordinateProject mask
              (Physical.physicalMatrixApply matrix
                (physicalCoordinateProject mask vector))
              row)
      (λ row →
        cong
          (vector row *_)
          (projectedPhysicalMatrixApplyExact
            mask matrix vector row)))
    (physicalConstraintProjectorSelfAdjoint
      mask vector
      (Physical.physicalMatrixApply matrix
        (physicalCoordinateProject mask vector)))

physicalConstrainedResolutionOfIdentity :
  ∀ mask vector row →
  physicalCoordinateProject mask vector row
  ≡ Sums.sumRational Physical.physicalSU2Coordinates4
      (λ column →
        physicalCoordinateProject mask
          (Basis.physicalBasis column) row
        * vector column)
physicalConstrainedResolutionOfIdentity mask vector row =
  let
    selectedRow = maskCoefficient (mask row)

    pointwise : ∀ column →
      physicalCoordinateProject mask
        (Basis.physicalBasis column) row
        * vector column
      ≡ selectedRow
        * (Calibration.identityEntry row column * vector column)
    pointwise column with mask row
    ... | false = ℚRing.solve-∀ (vector column)
    ... | true = ℚRing.solve-∀ (vector column)

    rewritten =
      Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ column →
          physicalCoordinateProject mask
            (Basis.physicalBasis column) row
            * vector column)
        (λ column →
          selectedRow
            * (Calibration.identityEntry row column * vector column))
        pointwise

    factored =
      Sums.sumRationalScale
        selectedRow
        Physical.physicalSU2Coordinates4
        (λ column →
          Calibration.identityEntry row column * vector column)
  in
  sym
    (trans rewritten
      (trans factored
        (cong
          (selectedRow *_)
          (Entry.physicalIdentityApplyExact vector row))))

rawPhysicalEdgeLieBasis : Set
rawPhysicalEdgeLieBasis = Coordinate

physicalConstrainedCoordinateBasis :
  PhysicalCoordinateMask → Coordinate → PhysicalVector
physicalConstrainedCoordinateBasis mask coordinate =
  physicalCoordinateProject mask (Basis.physicalBasis coordinate)

physicalCoordinateMaskProjectorLevel : ProofLevel
physicalCoordinateMaskProjectorLevel = machineChecked

physicalCoordinateProjectorSelfAdjointLevel : ProofLevel
physicalCoordinateProjectorSelfAdjointLevel = machineChecked

physicalConstrainedResolutionLevel : ProofLevel
physicalConstrainedResolutionLevel = machineChecked

projectedLiteralHessianRepresentationLevel : ProofLevel
projectedLiteralHessianRepresentationLevel = machineChecked
