module DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasSchurExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Werner Kirsch,
-- "An Invitation to Random Schrödinger Operators",
-- Panoramas et Synthèses 25 (2008), 1--119; arXiv:0709.3707.
-- No DOI was assigned to the cited survey chapter.
--
-- Lin Lin and Jianfeng Lu,
-- "Decay Estimates of Discretized Green's Functions for Schrödinger Type
-- Operators", Science China Mathematics 59 (2016), 1561--1578.
-- DOI: 10.1007/s11425-016-0311-4.
--
-- DASHI CONTRIBUTION
--
-- Close the row/column-to-l2 bridge for the literal 3072-coordinate P33
-- carrier.  The tilted defect
--
--   E = D H D^-1 - H
--
-- is not symmetric even when H is symmetric.  Consequently we do not claim
-- the false identity R_E=C_E.  Instead, the same orientation-uniform entry
-- estimate is summed once by rows and once by columns.  Symmetry of H is used
-- only to identify the absolute column mass of H with its corresponding row
-- mass.  This proves
--
--   ||E v||_2^2 <= (1/64)^2 ||v||_2^2 = 1/4096 ||v||_2^2.
--
-- Combined with the original squared lower bound 1/1024 and the exact
-- same-vector identity H_D v = H v + E v, the square-root-free half-gap theorem
-- gives
--
--   1/4096 ||v||_2^2 <= ||H_D v||_2^2.
--
-- The local shell ratio itself is dimension-free, but the admissible ratio is
-- not automatically dimension-free: stencil degree and coefficient size enter
-- through the absolute row mass.  The final scalar theorem below records this
-- dependence explicitly rather than hiding a 1/d-type loss.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as Promotion
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33CombesThomasSquaredHalfGapExact as Squared

Coordinate : Set
Coordinate = Physical.PhysicalSU2Coordinate4

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

------------------------------------------------------------------------
-- Physical symmetry and geometry bundle.
------------------------------------------------------------------------

record PhysicalCombesThomasSchurData
    (hessian : PhysicalMatrix) : Set₁ where
  field
    geometry : Promotion.PhysicalCombesThomasGeometry hessian
    hessianSymmetric : Schur.Symmetric hessian

open PhysicalCombesThomasSchurData public

physicalTiltedHessian :
  ∀ {hessian} →
  PhysicalCombesThomasSchurData hessian → PhysicalMatrix
physicalTiltedHessian {hessian} data =
  CT.diagonalConjugate
    (Promotion.physicalWeight (geometry data))
    (Promotion.physicalInverseWeight (geometry data))
    hessian

physicalTiltDefect :
  ∀ {hessian} →
  PhysicalCombesThomasSchurData hessian → PhysicalMatrix
physicalTiltDefect {hessian} data =
  CT.diagonalTiltDefect
    (Promotion.physicalWeight (geometry data))
    (Promotion.physicalInverseWeight (geometry data))
    hessian

physicalTiltDefectIsMatrixDifference :
  ∀ {hessian}
    (data : PhysicalCombesThomasSchurData hessian)
    left right →
  physicalTiltDefect data left right
  ≡ Squared.matrixDifference
      (physicalTiltedHessian data)
      hessian left right
physicalTiltDefectIsMatrixDifference data left right = refl

------------------------------------------------------------------------
-- Row and column estimates for the non-symmetric tilted defect.
------------------------------------------------------------------------

physicalTiltDefectRowBelowHalfGap :
  ∀ {hessian}
    (data : PhysicalCombesThomasSchurData hessian)
    row →
  Schur.absoluteRowMass
    Physical.physicalSU2Coordinates4
    (physicalTiltDefect data) row
  ≤ Tilt.p33HalfGap
physicalTiltDefectRowBelowHalfGap data row =
  Promotion.physicalTiltDefectBelowHalfGap
    (geometry data) row

physicalTiltDefectColumnMassBound :
  ∀ {hessian}
    (data : PhysicalCombesThomasSchurData hessian)
    column →
  Schur.absoluteColumnMass
    Physical.physicalSU2Coordinates4
    (physicalTiltDefect data) column
  ≤ Promotion.distortion (geometry data)
      * Schur.absoluteColumnMass
          Physical.physicalSU2Coordinates4 hessian column
physicalTiltDefectColumnMassBound {hessian} data column =
  subst
    (λ upper →
      Schur.absoluteColumnMass
        Physical.physicalSU2Coordinates4
        (physicalTiltDefect data) column
      ≤ upper)
    (Sums.sumRationalScale
      (Promotion.distortion (geometry data))
      Physical.physicalSU2Coordinates4
      (λ row → ∣ hessian row column ∣))
    (Schur.sumPointwiseBelow
      Physical.physicalSU2Coordinates4
      (λ row → ∣ physicalTiltDefect data row column ∣)
      (λ row →
        Promotion.distortion (geometry data)
          * ∣ hessian row column ∣)
      (λ row →
        Promotion.physicalTiltDefectEntryBound
          (geometry data) row column))

physicalHessianColumnMassEqualsRowMass :
  ∀ {hessian}
    (data : PhysicalCombesThomasSchurData hessian)
    coordinate →
  Schur.absoluteColumnMass
    Physical.physicalSU2Coordinates4 hessian coordinate
  ≡ Schur.absoluteRowMass
      Physical.physicalSU2Coordinates4 hessian coordinate
physicalHessianColumnMassEqualsRowMass {hessian} data coordinate =
  Schur.symmetricColumnMassEqualsRowMass
    Physical.physicalSU2Coordinates4
    hessian
    (hessianSymmetric data)
    coordinate

physicalTiltDefectColumnBelowHalfGap :
  ∀ {hessian}
    (data : PhysicalCombesThomasSchurData hessian)
    column →
  Schur.absoluteColumnMass
    Physical.physicalSU2Coordinates4
    (physicalTiltDefect data) column
  ≤ Tilt.p33HalfGap
physicalTiltDefectColumnBelowHalfGap {hessian} data column =
  let
    geometryData = geometry data

    columnToRow :
      Promotion.distortion geometryData
        * Schur.absoluteColumnMass
            Physical.physicalSU2Coordinates4 hessian column
      ≡ Promotion.distortion geometryData
        * Schur.absoluteRowMass
            Physical.physicalSU2Coordinates4 hessian column
    columnToRow =
      cong
        (Promotion.distortion geometryData *_)
        (physicalHessianColumnMassEqualsRowMass data column)

    rowMassScaled :
      Promotion.distortion geometryData
        * Schur.absoluteRowMass
            Physical.physicalSU2Coordinates4 hessian column
      ≤ Promotion.distortion geometryData
        * Promotion.rowMass geometryData
    rowMassScaled =
      let
        instance
          distortionNN : NonNegative
            (Promotion.distortion geometryData)
          distortionNN = ℚ.nonNegative
            (Promotion.distortionNonnegative geometryData)
      in
      ℚP.*-monoˡ-≤-nonNeg
        (Promotion.distortion geometryData)
        (Promotion.hessianAbsoluteRowMass geometryData column)

    rowToHalfGap :
      Promotion.distortion geometryData
        * Schur.absoluteRowMass
            Physical.physicalSU2Coordinates4 hessian column
      ≤ Tilt.p33HalfGap
    rowToHalfGap =
      ℚP.≤-trans rowMassScaled
        (Promotion.scalarTiltBudget geometryData)

    columnToHalfGap :
      Promotion.distortion geometryData
        * Schur.absoluteColumnMass
            Physical.physicalSU2Coordinates4 hessian column
      ≤ Tilt.p33HalfGap
    columnToHalfGap =
      subst
        (λ selected → selected ≤ Tilt.p33HalfGap)
        (sym columnToRow)
        rowToHalfGap
  in
  ℚP.≤-trans
    (physicalTiltDefectColumnMassBound data column)
    columnToHalfGap

------------------------------------------------------------------------
-- Exact physical squared Schur estimate.
------------------------------------------------------------------------

physicalTiltDefectSchurSquared :
  ∀ {hessian}
    (data : PhysicalCombesThomasSchurData hessian)
    vector →
  Schur.vectorNormSq
    Physical.physicalSU2Coordinates4
    (Schur.matrixApply
      Physical.physicalSU2Coordinates4
      (physicalTiltDefect data)
      vector)
  ≤ Squared.p33HalfGapSquared
      * Schur.vectorNormSq
          Physical.physicalSU2Coordinates4 vector
physicalTiltDefectSchurSquared data vector =
  let
    halfGapNonnegative : 0ℚ ≤ Tilt.p33HalfGap
    halfGapNonnegative = ℚP.nonNegative⁻¹ Tilt.p33HalfGap

    schurBound :
      Schur.vectorNormSq
        Physical.physicalSU2Coordinates4
        (Schur.matrixApply
          Physical.physicalSU2Coordinates4
          (physicalTiltDefect data)
          vector)
      ≤ (Tilt.p33HalfGap * Tilt.p33HalfGap)
          * Schur.vectorNormSq
              Physical.physicalSU2Coordinates4 vector
    schurBound =
      Schur.finiteSchurSquared
        Physical.physicalSU2Coordinates4
        (physicalTiltDefect data)
        vector
        Tilt.p33HalfGap Tilt.p33HalfGap
        halfGapNonnegative halfGapNonnegative
        (physicalTiltDefectRowBelowHalfGap data)
        (physicalTiltDefectColumnBelowHalfGap data)
  in
  subst
    (λ coefficient →
      Schur.vectorNormSq
        Physical.physicalSU2Coordinates4
        (Schur.matrixApply
          Physical.physicalSU2Coordinates4
          (physicalTiltDefect data)
          vector)
      ≤ coefficient
          * Schur.vectorNormSq
              Physical.physicalSU2Coordinates4 vector)
    (sym Squared.p33HalfGapSquaredIsOneOverSixtyFourSquared)
    schurBound

------------------------------------------------------------------------
-- The remaining physical coercivity input and its exact tilted consequence.
------------------------------------------------------------------------

record PhysicalOriginalSquaredCoercivity
    (hessian : PhysicalMatrix) : Set₁ where
  field
    schurData : PhysicalCombesThomasSchurData hessian

    originalSquaredLower : ∀ vector →
      Squared.p33OriginalGapSquared
        * Schur.vectorNormSq
            Physical.physicalSU2Coordinates4 vector
      ≤ Schur.vectorNormSq
          Physical.physicalSU2Coordinates4
          (Schur.matrixApply
            Physical.physicalSU2Coordinates4 hessian vector)

open PhysicalOriginalSquaredCoercivity public

physicalTiltedSquaredLower :
  ∀ {hessian}
    (coercivity : PhysicalOriginalSquaredCoercivity hessian)
    vector →
  Squared.p33HalfGapSquared
    * Schur.vectorNormSq
        Physical.physicalSU2Coordinates4 vector
  ≤ Schur.vectorNormSq
      Physical.physicalSU2Coordinates4
      (Schur.matrixApply
        Physical.physicalSU2Coordinates4
        (physicalTiltedHessian (schurData coercivity))
        vector)
physicalTiltedSquaredLower {hessian} coercivity vector =
  Squared.p33SquaredHalfGapSurvives
    (Schur.vectorNormSq
      Physical.physicalSU2Coordinates4 vector)
    (Schur.vectorNormSq
      Physical.physicalSU2Coordinates4
      (Schur.matrixApply
        Physical.physicalSU2Coordinates4 hessian vector))
    (Schur.vectorNormSq
      Physical.physicalSU2Coordinates4
      (Schur.matrixApply
        Physical.physicalSU2Coordinates4
        (physicalTiltDefect (schurData coercivity)) vector))
    (Schur.vectorNormSq
      Physical.physicalSU2Coordinates4
      (Schur.matrixApply
        Physical.physicalSU2Coordinates4
        (physicalTiltedHessian (schurData coercivity)) vector))
    (originalSquaredLower coercivity vector)
    (physicalTiltDefectSchurSquared
      (schurData coercivity) vector)
    (Squared.sameVectorReverseTriangleSquared
      Physical.physicalSU2Coordinates4
      (physicalTiltedHessian (schurData coercivity))
      hessian vector)

------------------------------------------------------------------------
-- Explicit stencil-degree/rate dependence.
------------------------------------------------------------------------

rowMassFromStencilDegreeBudget :
  ∀ distortion rowMass degree entryBound →
  0ℚ ≤ distortion →
  rowMass ≤ degree * entryBound →
  distortion * (degree * entryBound) ≤ Tilt.p33HalfGap →
  distortion * rowMass ≤ Tilt.p33HalfGap
rowMassFromStencilDegreeBudget
    distortion rowMass degree entryBound
    distortionNonnegative rowMassBound degreeBudget =
  let
    instance
      distortionNN : NonNegative distortion
      distortionNN = ℚ.nonNegative distortionNonnegative
  in
  ℚP.≤-trans
    (ℚP.*-monoˡ-≤-nonNeg distortion rowMassBound)
    degreeBudget

physicalTiltDefectRowColumnLevel : ProofLevel
physicalTiltDefectRowColumnLevel = machineChecked

physicalTiltDefectSchurSquaredLevel : ProofLevel
physicalTiltDefectSchurSquaredLevel = machineChecked

physicalTiltedSquaredHalfGapLevel : ProofLevel
physicalTiltedSquaredHalfGapLevel = machineChecked

stencilDegreeRateDependenceLevel : ProofLevel
stencilDegreeRateDependenceLevel = machineChecked
