module DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Jerrold E. Marsden and Matthew West,
-- "Discrete Mechanics and Variational Integrators",
-- Acta Numerica 10 (2001), 357--514.
-- DOI: 10.1017/S096249290100006X.
--
-- DASHI CONTRIBUTION
--
-- On the literal 3072-coordinate side-four SU(2) state carrier, construct the
-- exact finite KKT projector
--
--   P = I - L* (L L*)^-1 L.
--
-- The multiplier carrier is finite but otherwise generic.  A concrete caller
-- must supply the actual constraint matrix and an exact two-sided inverse of
-- its Gram matrix.  From those data this module proves the full orthogonal
-- decomposition, image/kernel characterizations, norm contraction, the unique
-- nearest-admissible theorem and the minimum-norm repair theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasEntryDecayExact as Entry
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

State : Set
State = Physical.PhysicalSU2Coordinate4

StateVector : Set
StateVector = State → ℚ

physicalStateCarrier : Matrix.FiniteRationalCoordinates State
physicalStateCarrier = record
  { Matrix.FiniteRationalCoordinates.coordinates =
      Physical.physicalSU2Coordinates4
  ; Matrix.FiniteRationalCoordinates.delta =
      Calibration.identityEntry
  ; Matrix.FiniteRationalCoordinates.deltaActsAsIdentity =
      Entry.physicalIdentityApplyExact
  }

stateDot : StateVector → StateVector → ℚ
stateDot = Rect.finiteDot physicalStateCarrier

stateNormSq : StateVector → ℚ
stateNormSq = Rect.finiteNormSq physicalStateCarrier

stateNormSqNonnegative : ∀ vector → 0ℚ ≤ stateNormSq vector
stateNormSqNonnegative =
  Rect.finiteNormSqNonnegative physicalStateCarrier

stateNormSqZeroPointwise :
  ∀ vector → stateNormSq vector ≡ 0ℚ →
  ∀ coordinate → vector coordinate ≡ 0ℚ
stateNormSqZeroPointwise vector normZero coordinate =
  let
    squareBelowZero :
      FiniteL2.square (vector coordinate) ≤ 0ℚ
    squareBelowZero =
      subst
        (λ upper → FiniteL2.square (vector coordinate) ≤ upper)
        normZero
        (Basis.physicalCoordinateSquareBelowNormSq vector coordinate)

    squareZero :
      FiniteL2.square (vector coordinate) ≡ 0ℚ
    squareZero = ℚP.≤-antisym
      squareBelowZero
      (FiniteL2.squareNonnegative (vector coordinate))
  in
  Separation.rationalSquareZeroImpliesZero
    (vector coordinate) squareZero

constraintGramRaw :
  ∀ {Multiplier : Set} →
  Matrix.FiniteRationalCoordinates Multiplier →
  Rect.RectangularMatrix Multiplier State →
  Matrix.RationalMatrix Multiplier
constraintGramRaw multiplierCarrier constraintMatrix =
  Rect.composeRectangular
    physicalStateCarrier
    constraintMatrix
    (Rect.transposeRectangular constraintMatrix)

record FiniteKKTProjectorData (Multiplier : Set) : Set₁ where
  field
    multiplierCarrier :
      Matrix.FiniteRationalCoordinates Multiplier

    constraintMatrix :
      Rect.RectangularMatrix Multiplier State

    gramInverseCertificate :
      Matrix.RationalMatrixInverseCertificate
        multiplierCarrier
        (constraintGramRaw multiplierCarrier constraintMatrix)

    gramInverseSymmetric :
      ∀ left right →
      Matrix.inverseMatrix gramInverseCertificate left right
      ≡ Matrix.inverseMatrix gramInverseCertificate right left

open FiniteKKTProjectorData public

constraintApply :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  StateVector → Multiplier → ℚ
constraintApply data =
  Rect.applyRectangular
    physicalStateCarrier
    (constraintMatrix data)

constraintAdjointApply :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  (Multiplier → ℚ) → StateVector
constraintAdjointApply data =
  Rect.applyRectangular
    (multiplierCarrier data)
    (Rect.transposeRectangular (constraintMatrix data))

constraintGram :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  Matrix.RationalMatrix Multiplier
constraintGram data =
  constraintGramRaw
    (multiplierCarrier data)
    (constraintMatrix data)

multiplierGreen :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  Matrix.RationalMatrix Multiplier
multiplierGreen data =
  Matrix.inverseMatrix (gramInverseCertificate data)

multiplierGreenApply :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  (Multiplier → ℚ) → Multiplier → ℚ
multiplierGreenApply data =
  Rect.applyRectangular
    (multiplierCarrier data)
    (multiplierGreen data)

selectedConstraintRepair :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  StateVector → StateVector
selectedConstraintRepair data vector =
  constraintAdjointApply data
    (multiplierGreenApply data
      (constraintApply data vector))

selectedAdmissibleProject :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  StateVector → StateVector
selectedAdmissibleProject data vector =
  Rect.vectorSubtract vector
    (selectedConstraintRepair data vector)

record SelectedConstraintKernel
    {Multiplier : Set}
    (data : FiniteKKTProjectorData Multiplier)
    (vector : StateVector) : Set where
  field
    constraintZero :
      ∀ multiplier → constraintApply data vector multiplier ≡ 0ℚ

open SelectedConstraintKernel public

record SelectedRepairSpace
    {Multiplier : Set}
    (data : FiniteKKTProjectorData Multiplier)
    (vector : StateVector) : Set₁ where
  field
    multiplier : Multiplier → ℚ
    representedByAdjoint :
      ∀ coordinate →
      vector coordinate
      ≡ constraintAdjointApply data multiplier coordinate

open SelectedRepairSpace public

record SelectedProjectorImage
    {Multiplier : Set}
    (data : FiniteKKTProjectorData Multiplier)
    (vector : StateVector) : Set where
  field
    fixedByProjector :
      ∀ coordinate →
      selectedAdmissibleProject data vector coordinate
      ≡ vector coordinate

open SelectedProjectorImage public

record SelectedProjectorKernel
    {Multiplier : Set}
    (data : FiniteKKTProjectorData Multiplier)
    (vector : StateVector) : Set where
  field
    killedByProjector :
      ∀ coordinate →
      selectedAdmissibleProject data vector coordinate
      ≡ 0ℚ

open SelectedProjectorKernel public

constraintGramActionExact :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    multiplier row →
  constraintApply data
    (constraintAdjointApply data multiplier) row
  ≡ Rect.applyRectangular
      (multiplierCarrier data)
      (constraintGram data)
      multiplier row
constraintGramActionExact data multiplier row =
  sym
    (Rect.applyComposeRectangularExact
      physicalStateCarrier
      (multiplierCarrier data)
      (constraintMatrix data)
      (Rect.transposeRectangular (constraintMatrix data))
      multiplier row)

constraintRepairExact :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector multiplier →
  constraintApply data
    (selectedConstraintRepair data vector) multiplier
  ≡ constraintApply data vector multiplier
constraintRepairExact data vector multiplier =
  trans
    (constraintGramActionExact
      data
      (multiplierGreenApply data
        (constraintApply data vector))
      multiplier)
    (Matrix.matrixInverseRightExact
      (gramInverseCertificate data)
      (constraintApply data vector)
      multiplier)

selectedProjectorConstraintZero :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedConstraintKernel data
    (selectedAdmissibleProject data vector)
selectedProjectorConstraintZero data vector = record
  { constraintZero = λ multiplier →
      trans
        (Rect.applyRectangularSubtract
          physicalStateCarrier
          (constraintMatrix data)
          vector
          (selectedConstraintRepair data vector)
          multiplier)
        (trans
          (cong
            (constraintApply data vector multiplier -_)
            (constraintRepairExact data vector multiplier))
          (ℚRing.solve-∀
            (constraintApply data vector multiplier)))
  }

greenOfConstraintKernelZero :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedConstraintKernel data vector →
  ∀ multiplier →
  multiplierGreenApply data
    (constraintApply data vector) multiplier
  ≡ 0ℚ
greenOfConstraintKernelZero data vector kernel multiplier =
  trans
    (Rect.applyRectangularVectorCong
      (multiplierCarrier data)
      (multiplierGreen data)
      (constraintZero kernel)
      multiplier)
    (Rect.applyRectangularZero
      (multiplierCarrier data)
      (multiplierGreen data)
      multiplier)

repairOfConstraintKernelZero :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedConstraintKernel data vector →
  ∀ coordinate →
  selectedConstraintRepair data vector coordinate ≡ 0ℚ
repairOfConstraintKernelZero data vector kernel coordinate =
  trans
    (Rect.applyRectangularVectorCong
      (multiplierCarrier data)
      (Rect.transposeRectangular (constraintMatrix data))
      (greenOfConstraintKernelZero data vector kernel)
      coordinate)
    (Rect.applyRectangularZero
      (multiplierCarrier data)
      (Rect.transposeRectangular (constraintMatrix data))
      coordinate)

selectedProjectorFixesConstraintKernel :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedConstraintKernel data vector →
  ∀ coordinate →
  selectedAdmissibleProject data vector coordinate
  ≡ vector coordinate
selectedProjectorFixesConstraintKernel data vector kernel coordinate =
  trans
    (cong
      (vector coordinate -_)
      (repairOfConstraintKernelZero
        data vector kernel coordinate))
    (ℚRing.solve-∀ (vector coordinate))

selectedProjectorIdempotent :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector coordinate →
  selectedAdmissibleProject data
    (selectedAdmissibleProject data vector) coordinate
  ≡ selectedAdmissibleProject data vector coordinate
selectedProjectorIdempotent data vector =
  selectedProjectorFixesConstraintKernel
    data
    (selectedAdmissibleProject data vector)
    (selectedProjectorConstraintZero data vector)

greenGramExact :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    multiplier row →
  multiplierGreenApply data
    (Rect.applyRectangular
      (multiplierCarrier data)
      (constraintGram data)
      multiplier)
    row
  ≡ multiplier row
greenGramExact data multiplier row =
  Matrix.matrixInverseLeftExact
    (gramInverseCertificate data)
    multiplier row

repairOfAdjointExact :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    multiplier coordinate →
  selectedConstraintRepair data
    (constraintAdjointApply data multiplier)
    coordinate
  ≡ constraintAdjointApply data multiplier coordinate
repairOfAdjointExact data multiplier coordinate =
  let
    gramToGreenPointwise : ∀ row →
      multiplierGreenApply data
        (constraintApply data
          (constraintAdjointApply data multiplier))
        row
      ≡ multiplier row
    gramToGreenPointwise row =
      trans
        (Rect.applyRectangularVectorCong
          (multiplierCarrier data)
          (multiplierGreen data)
          (λ selected →
            constraintGramActionExact
              data multiplier selected)
          row)
        (greenGramExact data multiplier row)
  in
  Rect.applyRectangularVectorCong
    (multiplierCarrier data)
    (Rect.transposeRectangular (constraintMatrix data))
    gramToGreenPointwise
    coordinate

selectedProjectorKillsRepairSpace :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedRepairSpace data vector →
  SelectedProjectorKernel data vector
selectedProjectorKillsRepairSpace data vector repairSpace = record
  { killedByProjector = λ coordinate →
      let
        constraintRepresentation : ∀ row →
          constraintApply data vector row
          ≡ constraintApply data
              (constraintAdjointApply data
                (multiplier repairSpace))
              row
        constraintRepresentation row =
          Rect.applyRectangularVectorCong
            physicalStateCarrier
            (constraintMatrix data)
            (representedByAdjoint repairSpace)
            row

        greenRepresentation : ∀ row →
          multiplierGreenApply data
            (constraintApply data vector) row
          ≡ multiplierGreenApply data
              (constraintApply data
                (constraintAdjointApply data
                  (multiplier repairSpace)))
              row
        greenRepresentation row =
          Rect.applyRectangularVectorCong
            (multiplierCarrier data)
            (multiplierGreen data)
            constraintRepresentation
            row

        repairRepresentation :
          selectedConstraintRepair data vector coordinate
          ≡ selectedConstraintRepair data
              (constraintAdjointApply data
                (multiplier repairSpace))
              coordinate
        repairRepresentation =
          Rect.applyRectangularVectorCong
            (multiplierCarrier data)
            (Rect.transposeRectangular (constraintMatrix data))
            greenRepresentation
            coordinate

        repairIsVector :
          selectedConstraintRepair data vector coordinate
          ≡ vector coordinate
        repairIsVector =
          trans repairRepresentation
            (trans
              (repairOfAdjointExact
                data (multiplier repairSpace) coordinate)
              (sym
                (representedByAdjoint repairSpace coordinate)))
      in
      trans
        (cong
          (vector coordinate -_)
          repairIsVector)
        (ℚRing.solve-∀ (vector coordinate))
  }

selectedProjectorImageIsConstraintKernel :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedProjectorImage data vector →
  SelectedConstraintKernel data vector
selectedProjectorImageIsConstraintKernel data vector image = record
  { constraintZero = λ multiplier →
      trans
        (Rect.applyRectangularVectorCong
          physicalStateCarrier
          (constraintMatrix data)
          (λ coordinate →
            sym (fixedByProjector image coordinate))
          multiplier)
        (constraintZero
          (selectedProjectorConstraintZero data vector)
          multiplier)
  }

selectedConstraintKernelIsProjectorImage :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedConstraintKernel data vector →
  SelectedProjectorImage data vector
selectedConstraintKernelIsProjectorImage data vector kernel = record
  { fixedByProjector =
      selectedProjectorFixesConstraintKernel data vector kernel
  }

selectedProjectorKernelIsRepairSpace :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedProjectorKernel data vector →
  SelectedRepairSpace data vector
selectedProjectorKernelIsRepairSpace data vector kernel = record
  { multiplier =
      multiplierGreenApply data (constraintApply data vector)
  ; representedByAdjoint = λ coordinate →
      let
        projectedZero = killedByProjector kernel coordinate
        repair = selectedConstraintRepair data vector coordinate

        shifted :
          selectedAdmissibleProject data vector coordinate
            + repair
          ≡ 0ℚ + repair
        shifted = cong (_+ repair) projectedZero
      in
      trans
        (sym
          (ℚRing.solve-∀
            (vector coordinate) repair))
        (trans shifted
          (ℚRing.solve-∀ repair))
  }

selectedRepairSpaceIsProjectorKernel :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  SelectedRepairSpace data vector →
  SelectedProjectorKernel data vector
selectedRepairSpaceIsProjectorKernel =
  selectedProjectorKillsRepairSpace

selectedAdmissibleOrthogonalDecompositionPointwise :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector coordinate →
  vector coordinate
  ≡ selectedAdmissibleProject data vector coordinate
    + selectedConstraintRepair data vector coordinate
selectedAdmissibleOrthogonalDecompositionPointwise data vector coordinate =
  ℚRing.solve-∀
    (vector coordinate)
    (selectedConstraintRepair data vector coordinate)

multiplierDot :
  ∀ {Multiplier} →
  FiniteKKTProjectorData Multiplier →
  (Multiplier → ℚ) → (Multiplier → ℚ) → ℚ
multiplierDot data =
  Rect.finiteDot (multiplierCarrier data)

selectedRepairSelfAdjoint :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    left right →
  stateDot left (selectedConstraintRepair data right)
  ≡ stateDot (selectedConstraintRepair data left) right
selectedRepairSelfAdjoint data left right =
  let
    leftConstraint = constraintApply data left
    rightConstraint = constraintApply data right
    greenLeft = multiplierGreenApply data leftConstraint
    greenRight = multiplierGreenApply data rightConstraint
  in
  trans
    (sym
      (Rect.rectangularAdjointExact
        (multiplierCarrier data)
        physicalStateCarrier
        (constraintMatrix data)
        left
        greenRight))
    (trans
      (Rect.symmetricMatrixMovesAcrossDot
        (multiplierCarrier data)
        (multiplierGreen data)
        (gramInverseSymmetric data)
        leftConstraint
        rightConstraint)
      (trans
        (Rect.finiteDotSymmetric
          (multiplierCarrier data)
          greenLeft rightConstraint)
        (trans
          (Rect.rectangularAdjointExact
            (multiplierCarrier data)
            physicalStateCarrier
            (constraintMatrix data)
            right
            greenLeft)
          (Rect.finiteDotSymmetric
            physicalStateCarrier
            right
            (selectedConstraintRepair data left)))))

selectedProjectorSelfAdjoint :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    left right →
  stateDot left (selectedAdmissibleProject data right)
  ≡ stateDot (selectedAdmissibleProject data left) right
selectedProjectorSelfAdjoint data left right =
  trans
    (Rect.finiteDotSubtractRight
      physicalStateCarrier
      left right
      (selectedConstraintRepair data right))
    (trans
      (cong
        (stateDot left right -_)
        (selectedRepairSelfAdjoint data left right))
      (sym
        (Rect.finiteDotSubtractLeft
          physicalStateCarrier
          left
          (selectedConstraintRepair data left)
          right)))

selectedAdmissibleRepairOrthogonal :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    admissible multiplier →
  SelectedConstraintKernel data admissible →
  stateDot admissible
    (constraintAdjointApply data multiplier)
  ≡ 0ℚ
selectedAdmissibleRepairOrthogonal
    data admissible multiplier admissibleKernel =
  trans
    (sym
      (Rect.rectangularAdjointExact
        (multiplierCarrier data)
        physicalStateCarrier
        (constraintMatrix data)
        admissible multiplier))
    (trans
      (Sums.sumRationalCong
        (Matrix.coordinates (multiplierCarrier data))
        (λ row →
          constraintApply data admissible row * multiplier row)
        (λ row → 0ℚ * multiplier row)
        (λ row →
          cong (_* multiplier row)
            (constraintZero admissibleKernel row)))
      (trans
        (Sums.sumRationalCong
          (Matrix.coordinates (multiplierCarrier data))
          (λ row → 0ℚ * multiplier row)
          (λ _ → 0ℚ)
          (λ row → ℚRing.solve-∀ (multiplier row)))
        (Fubini.sumRationalZero
          (Matrix.coordinates (multiplierCarrier data)))))

selectedProjectRepairOrthogonal :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  stateDot
    (selectedAdmissibleProject data vector)
    (selectedConstraintRepair data vector)
  ≡ 0ℚ
selectedProjectRepairOrthogonal data vector =
  selectedAdmissibleRepairOrthogonal
    data
    (selectedAdmissibleProject data vector)
    (multiplierGreenApply data
      (constraintApply data vector))
    (selectedProjectorConstraintZero data vector)

selectedRepairProjectOrthogonal :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  stateDot
    (selectedConstraintRepair data vector)
    (selectedAdmissibleProject data vector)
  ≡ 0ℚ
selectedRepairProjectOrthogonal data vector =
  trans
    (Rect.finiteDotSymmetric
      physicalStateCarrier
      (selectedConstraintRepair data vector)
      (selectedAdmissibleProject data vector))
    (selectedProjectRepairOrthogonal data vector)

stateNormPointwiseCong :
  ∀ {left right : StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  stateNormSq left ≡ stateNormSq right
stateNormPointwiseCong {left} {right} pointwise =
  Sums.sumRationalCong
    Physical.physicalSU2Coordinates4
    (λ coordinate → left coordinate * left coordinate)
    (λ coordinate → right coordinate * right coordinate)
    (λ coordinate →
      cong₂ _*_
        (pointwise coordinate)
        (pointwise coordinate))

selectedStatePythagorean :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  stateNormSq vector
  ≡ stateNormSq (selectedAdmissibleProject data vector)
    + stateNormSq (selectedConstraintRepair data vector)
selectedStatePythagorean data vector =
  trans
    (stateNormPointwiseCong
      (selectedAdmissibleOrthogonalDecompositionPointwise data vector))
    (Rect.normSqAddOrthogonal
      physicalStateCarrier
      (selectedAdmissibleProject data vector)
      (selectedConstraintRepair data vector)
      (selectedProjectRepairOrthogonal data vector)
      (selectedRepairProjectOrthogonal data vector))

selectedProjectorNormContraction :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  stateNormSq (selectedAdmissibleProject data vector)
  ≤ stateNormSq vector
selectedProjectorNormContraction data vector =
  let
    repairNN =
      stateNormSqNonnegative
        (selectedConstraintRepair data vector)

    withRemainder :
      stateNormSq (selectedAdmissibleProject data vector)
      ≤ stateNormSq (selectedAdmissibleProject data vector)
        + stateNormSq (selectedConstraintRepair data vector)
    withRemainder =
      subst
        (λ lower →
          lower
          ≤ stateNormSq (selectedAdmissibleProject data vector)
            + stateNormSq (selectedConstraintRepair data vector))
        (ℚP.+-identityʳ
          (stateNormSq (selectedAdmissibleProject data vector)))
        (ℚP.+-mono-≤ ℚP.≤-refl repairNN)
  in
  subst
    (λ upper →
      stateNormSq (selectedAdmissibleProject data vector)
      ≤ upper)
    (sym (selectedStatePythagorean data vector))
    withRemainder

stateDistanceSq : StateVector → StateVector → ℚ
stateDistanceSq left right =
  stateNormSq (Rect.vectorSubtract left right)

selectedDifferenceDecompositionPointwise :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector admissible coordinate →
  Rect.vectorSubtract vector admissible coordinate
  ≡ Rect.vectorAdd
      (selectedConstraintRepair data vector)
      (Rect.vectorSubtract
        (selectedAdmissibleProject data vector)
        admissible)
      coordinate
selectedDifferenceDecompositionPointwise
    data vector admissible coordinate =
  ℚRing.solve-∀
    (vector coordinate)
    (selectedConstraintRepair data vector coordinate)
    (admissible coordinate)

selectedProjectedDifferenceKernel :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector admissible →
  SelectedConstraintKernel data admissible →
  SelectedConstraintKernel data
    (Rect.vectorSubtract
      (selectedAdmissibleProject data vector)
      admissible)
selectedProjectedDifferenceKernel data vector admissible kernel = record
  { constraintZero = λ multiplier →
      trans
        (Rect.applyRectangularSubtract
          physicalStateCarrier
          (constraintMatrix data)
          (selectedAdmissibleProject data vector)
          admissible
          multiplier)
        (trans
          (cong₂ _-_
            (constraintZero
              (selectedProjectorConstraintZero data vector)
              multiplier)
            (constraintZero kernel multiplier))
          (ℚRing.solve []))
  }

selectedDifferencePythagorean :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector admissible →
  SelectedConstraintKernel data admissible →
  stateDistanceSq vector admissible
  ≡ stateNormSq (selectedConstraintRepair data vector)
    + stateNormSq
        (Rect.vectorSubtract
          (selectedAdmissibleProject data vector)
          admissible)
selectedDifferencePythagorean data vector admissible kernel =
  let
    difference =
      Rect.vectorSubtract
        (selectedAdmissibleProject data vector)
        admissible

    differenceKernel =
      selectedProjectedDifferenceKernel
        data vector admissible kernel

    differenceRepairOrthogonal :
      stateDot difference
        (selectedConstraintRepair data vector)
      ≡ 0ℚ
    differenceRepairOrthogonal =
      selectedAdmissibleRepairOrthogonal
        data difference
        (multiplierGreenApply data
          (constraintApply data vector))
        differenceKernel

    repairDifferenceOrthogonal :
      stateDot
        (selectedConstraintRepair data vector)
        difference
      ≡ 0ℚ
    repairDifferenceOrthogonal =
      trans
        (Rect.finiteDotSymmetric
          physicalStateCarrier
          (selectedConstraintRepair data vector)
          difference)
        differenceRepairOrthogonal
  in
  trans
    (stateNormPointwiseCong
      (selectedDifferenceDecompositionPointwise
        data vector admissible))
    (Rect.normSqAddOrthogonal
      physicalStateCarrier
      (selectedConstraintRepair data vector)
      difference
      repairDifferenceOrthogonal
      differenceRepairOrthogonal)

selectedDistanceToProjectionIsRepairNorm :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector →
  stateDistanceSq vector
    (selectedAdmissibleProject data vector)
  ≡ stateNormSq (selectedConstraintRepair data vector)
selectedDistanceToProjectionIsRepairNorm data vector =
  stateNormPointwiseCong
    (λ coordinate →
      ℚRing.solve-∀
        (vector coordinate)
        (selectedConstraintRepair data vector coordinate))

selectedProjectedVariationNearestAdmissible :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector admissible →
  SelectedConstraintKernel data admissible →
  stateDistanceSq vector
    (selectedAdmissibleProject data vector)
  ≤ stateDistanceSq vector admissible
selectedProjectedVariationNearestAdmissible
    data vector admissible kernel =
  let
    residual =
      Rect.vectorSubtract
        (selectedAdmissibleProject data vector)
        admissible

    residualNN = stateNormSqNonnegative residual

    repairBelowSum :
      stateNormSq (selectedConstraintRepair data vector)
      ≤ stateNormSq (selectedConstraintRepair data vector)
        + stateNormSq residual
    repairBelowSum =
      subst
        (λ lower →
          lower
          ≤ stateNormSq (selectedConstraintRepair data vector)
            + stateNormSq residual)
        (ℚP.+-identityʳ
          (stateNormSq (selectedConstraintRepair data vector)))
        (ℚP.+-mono-≤ ℚP.≤-refl residualNN)
  in
  subst
    (λ lower → lower ≤ stateDistanceSq vector admissible)
    (sym (selectedDistanceToProjectionIsRepairNorm data vector))
    (subst
      (λ upper →
        stateNormSq (selectedConstraintRepair data vector)
        ≤ upper)
      (sym
        (selectedDifferencePythagorean
          data vector admissible kernel))
      repairBelowSum)

selectedProjectedVariationUniqueNearestAdmissible :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector admissible →
  SelectedConstraintKernel data admissible →
  stateDistanceSq vector admissible
    ≡ stateDistanceSq vector
        (selectedAdmissibleProject data vector) →
  ∀ coordinate →
  admissible coordinate
  ≡ selectedAdmissibleProject data vector coordinate
selectedProjectedVariationUniqueNearestAdmissible
    data vector admissible kernel sameDistance coordinate =
  let
    residual =
      Rect.vectorSubtract
        (selectedAdmissibleProject data vector)
        admissible

    pythagorean =
      selectedDifferencePythagorean
        data vector admissible kernel

    projectionDistance =
      selectedDistanceToProjectionIsRepairNorm data vector

    sumEqualsRepair :
      stateNormSq (selectedConstraintRepair data vector)
        + stateNormSq residual
      ≡ stateNormSq (selectedConstraintRepair data vector)
    sumEqualsRepair =
      trans
        (sym pythagorean)
        (trans sameDistance projectionDistance)

    residualZero :
      stateNormSq residual ≡ 0ℚ
    residualZero =
      trans
        (sym
          (ℚRing.solve-∀
            (stateNormSq (selectedConstraintRepair data vector))
            (stateNormSq residual)))
        (trans
          (cong
            (λ selected →
              selected
              - stateNormSq
                  (selectedConstraintRepair data vector))
            sumEqualsRepair)
          (ℚRing.solve-∀
            (stateNormSq (selectedConstraintRepair data vector))))

    differenceZero :
      selectedAdmissibleProject data vector coordinate
        - admissible coordinate
      ≡ 0ℚ
    differenceZero =
      stateNormSqZeroPointwise residual residualZero coordinate

    shifted :
      (selectedAdmissibleProject data vector coordinate
        - admissible coordinate)
        + admissible coordinate
      ≡ 0ℚ + admissible coordinate
    shifted = cong (_+ admissible coordinate) differenceZero
  in
  sym
    (trans
      (sym
        (ℚRing.solve-∀
          (selectedAdmissibleProject data vector coordinate)
          (admissible coordinate)))
      (trans shifted
        (ℚRing.solve-∀ (admissible coordinate))))

selectedRepairIsMinimumNorm :
  ∀ {Multiplier}
    (data : FiniteKKTProjectorData Multiplier)
    vector correction →
  (∀ multiplier →
    constraintApply data correction multiplier
    ≡ constraintApply data vector multiplier) →
  stateNormSq (selectedConstraintRepair data vector)
  ≤ stateNormSq correction
selectedRepairIsMinimumNorm data vector correction sameConstraint =
  let
    candidate = Rect.vectorSubtract vector correction

    candidateKernel : SelectedConstraintKernel data candidate
    candidateKernel = record
      { constraintZero = λ multiplier →
          trans
            (Rect.applyRectangularSubtract
              physicalStateCarrier
              (constraintMatrix data)
              vector correction multiplier)
            (trans
              (cong
                (constraintApply data vector multiplier -_)
                (sameConstraint multiplier))
              (ℚRing.solve-∀
                (constraintApply data vector multiplier)))
      }

    nearest =
      selectedProjectedVariationNearestAdmissible
        data vector candidate candidateKernel

    correctionDistance :
      stateDistanceSq vector candidate
      ≡ stateNormSq correction
    correctionDistance =
      stateNormPointwiseCong
        (λ coordinate →
          ℚRing.solve-∀
            (vector coordinate) (correction coordinate))
  in
  subst
    (λ lower → lower ≤ stateNormSq correction)
    (selectedDistanceToProjectionIsRepairNorm data vector)
    (subst
      (λ upper →
        stateDistanceSq vector
          (selectedAdmissibleProject data vector)
        ≤ upper)
      correctionDistance
      nearest)

finiteKKTProjectorConstraintLevel : ProofLevel
finiteKKTProjectorConstraintLevel = machineChecked

finiteKKTProjectorOrthogonalLevel : ProofLevel
finiteKKTProjectorOrthogonalLevel = machineChecked

finiteKKTNearestAdmissibleLevel : ProofLevel
finiteKKTNearestAdmissibleLevel = machineChecked

selectedPhysicalConstraintMatrixProducerLevel : ProofLevel
selectedPhysicalConstraintMatrixProducerLevel = conditional

selectedConstraintGramInverseProducerLevel : ProofLevel
selectedConstraintGramInverseProducerLevel = conditional
