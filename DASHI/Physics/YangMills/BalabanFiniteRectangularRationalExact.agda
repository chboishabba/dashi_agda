module DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Supply exact finite rectangular-matrix algebra over the repository's
-- rational coordinate carriers.  This is the common algebra required by the
-- KKT projector, multiplier-space defect identity, reduced Hessian and saddle
-- Green operator.  All identities are finite sums and are proved without
-- function extensionality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix

RationalVector : Set → Set
RationalVector Index = Index → ℚ

RectangularMatrix : Set → Set → Set
RectangularMatrix Row Column = Row → Column → ℚ

zeroVector : ∀ {Index : Set} → RationalVector Index
zeroVector _ = 0ℚ

vectorAdd :
  ∀ {Index : Set} →
  RationalVector Index → RationalVector Index → RationalVector Index
vectorAdd left right index = left index + right index

vectorSubtract :
  ∀ {Index : Set} →
  RationalVector Index → RationalVector Index → RationalVector Index
vectorSubtract left right index = left index - right index

vectorNegate :
  ∀ {Index : Set} →
  RationalVector Index → RationalVector Index
vectorNegate vector index = - vector index

finiteDot :
  ∀ {Index : Set} →
  Matrix.FiniteRationalCoordinates Index →
  RationalVector Index → RationalVector Index → ℚ
finiteDot carrier left right =
  Sums.sumRational (Matrix.coordinates carrier)
    (λ index → left index * right index)

finiteNormSq :
  ∀ {Index : Set} →
  Matrix.FiniteRationalCoordinates Index →
  RationalVector Index → ℚ
finiteNormSq carrier vector = finiteDot carrier vector vector

applyRectangular :
  ∀ {Row Column : Set} →
  Matrix.FiniteRationalCoordinates Column →
  RectangularMatrix Row Column →
  RationalVector Column → RationalVector Row
applyRectangular columnCarrier matrix vector row =
  Sums.sumRational (Matrix.coordinates columnCarrier)
    (λ column → matrix row column * vector column)

transposeRectangular :
  ∀ {Row Column : Set} →
  RectangularMatrix Row Column →
  RectangularMatrix Column Row
transposeRectangular matrix column row = matrix row column

composeRectangular :
  ∀ {Row Middle Column : Set} →
  Matrix.FiniteRationalCoordinates Middle →
  RectangularMatrix Row Middle →
  RectangularMatrix Middle Column →
  RectangularMatrix Row Column
composeRectangular middleCarrier left right row column =
  Sums.sumRational (Matrix.coordinates middleCarrier)
    (λ middle → left row middle * right middle column)

finiteDotSymmetric :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index) left right →
  finiteDot carrier left right ≡ finiteDot carrier right left
finiteDotSymmetric carrier left right =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ index → left index * right index)
    (λ index → right index * left index)
    (λ index → ℚP.*-comm (left index) (right index))

finiteDotAddRight :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index)
    left first second →
  finiteDot carrier left (vectorAdd first second)
  ≡ finiteDot carrier left first + finiteDot carrier left second
finiteDotAddRight carrier left first second =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ index → left index * (first index + second index))
      (λ index → left index * first index + left index * second index)
      (λ index → ℚRing.solve-∀
        (left index) (first index) (second index)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ index → left index * first index)
      (λ index → left index * second index))

finiteDotAddLeft :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index)
    first second right →
  finiteDot carrier (vectorAdd first second) right
  ≡ finiteDot carrier first right + finiteDot carrier second right
finiteDotAddLeft carrier first second right =
  trans
    (finiteDotSymmetric carrier (vectorAdd first second) right)
    (trans
      (finiteDotAddRight carrier right first second)
      (cong₂ _+_
        (finiteDotSymmetric carrier right first)
        (finiteDotSymmetric carrier right second)))

sumRationalNegate :
  ∀ {Index : Set} (values : List Index) (term : Index → ℚ) →
  Sums.sumRational values (λ index → - term index)
  ≡ - Sums.sumRational values term
sumRationalNegate [] term = refl
sumRationalNegate (index ∷ values) term
  rewrite sumRationalNegate values term =
  ℚRing.solve-∀ (term index) (Sums.sumRational values term)

finiteDotSubtractRight :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index)
    left first second →
  finiteDot carrier left (vectorSubtract first second)
  ≡ finiteDot carrier left first - finiteDot carrier left second
finiteDotSubtractRight carrier left first second =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ index → left index * (first index - second index))
      (λ index → left index * first index
        + - (left index * second index))
      (λ index → ℚRing.solve-∀
        (left index) (first index) (second index)))
    (trans
      (Fubini.sumRationalAdd
        (Matrix.coordinates carrier)
        (λ index → left index * first index)
        (λ index → - (left index * second index)))
      (cong
        (finiteDot carrier left first +_)
        (sumRationalNegate
          (Matrix.coordinates carrier)
          (λ index → left index * second index))))

finiteDotSubtractLeft :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index)
    first second right →
  finiteDot carrier (vectorSubtract first second) right
  ≡ finiteDot carrier first right - finiteDot carrier second right
finiteDotSubtractLeft carrier first second right =
  trans
    (finiteDotSymmetric carrier (vectorSubtract first second) right)
    (trans
      (finiteDotSubtractRight carrier right first second)
      (cong₂ _-_
        (finiteDotSymmetric carrier right first)
        (finiteDotSymmetric carrier right second)))

finiteDotZeroLeft :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index) right →
  finiteDot carrier zeroVector right ≡ 0ℚ
finiteDotZeroLeft carrier right =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ index → 0ℚ * right index)
      (λ _ → 0ℚ)
      (λ index → ℚRing.solve-∀ (right index)))
    (Fubini.sumRationalZero (Matrix.coordinates carrier))

finiteDotZeroRight :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index) left →
  finiteDot carrier left zeroVector ≡ 0ℚ
finiteDotZeroRight carrier left =
  trans
    (finiteDotSymmetric carrier left zeroVector)
    (finiteDotZeroLeft carrier left)

sumSquaresNonnegative :
  ∀ {Index : Set} (values : List Index) (vector : RationalVector Index) →
  0ℚ ≤ Sums.sumRational values
    (λ index → vector index * vector index)
sumSquaresNonnegative [] vector = ℚP.≤-refl
sumSquaresNonnegative (index ∷ values) vector =
  FiniteL2.addNonnegative
    (FiniteL2.squareNonnegative (vector index))
    (sumSquaresNonnegative values vector)

finiteNormSqNonnegative :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index) vector →
  0ℚ ≤ finiteNormSq carrier vector
finiteNormSqNonnegative carrier vector =
  sumSquaresNonnegative (Matrix.coordinates carrier) vector

applyRectangularVectorCong :
  ∀ {Row Column}
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    {left right : RationalVector Column} →
  (∀ column → left column ≡ right column) →
  ∀ row →
  applyRectangular columnCarrier matrix left row
  ≡ applyRectangular columnCarrier matrix right row
applyRectangularVectorCong carrier matrix {left} {right} pointwise row =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ column → matrix row column * left column)
    (λ column → matrix row column * right column)
    (λ column → cong (matrix row column *_) (pointwise column))

applyRectangularZero :
  ∀ {Row Column}
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column) row →
  applyRectangular columnCarrier matrix zeroVector row ≡ 0ℚ
applyRectangularZero carrier matrix row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ column → matrix row column * 0ℚ)
      (λ _ → 0ℚ)
      (λ column → ℚRing.solve-∀ (matrix row column)))
    (Fubini.sumRationalZero (Matrix.coordinates carrier))

applyRectangularAdd :
  ∀ {Row Column}
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    left right row →
  applyRectangular columnCarrier matrix (vectorAdd left right) row
  ≡ applyRectangular columnCarrier matrix left row
    + applyRectangular columnCarrier matrix right row
applyRectangularAdd carrier matrix left right row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ column → matrix row column * (left column + right column))
      (λ column → matrix row column * left column
        + matrix row column * right column)
      (λ column → ℚRing.solve-∀
        (matrix row column) (left column) (right column)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ column → matrix row column * left column)
      (λ column → matrix row column * right column))

applyRectangularSubtract :
  ∀ {Row Column}
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    left right row →
  applyRectangular columnCarrier matrix (vectorSubtract left right) row
  ≡ applyRectangular columnCarrier matrix left row
    - applyRectangular columnCarrier matrix right row
applyRectangularSubtract carrier matrix left right row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ column → matrix row column * (left column - right column))
      (λ column → matrix row column * left column
        + - (matrix row column * right column))
      (λ column → ℚRing.solve-∀
        (matrix row column) (left column) (right column)))
    (trans
      (Fubini.sumRationalAdd
        (Matrix.coordinates carrier)
        (λ column → matrix row column * left column)
        (λ column → - (matrix row column * right column)))
      (cong
        (applyRectangular carrier matrix left row +_)
        (sumRationalNegate
          (Matrix.coordinates carrier)
          (λ column → matrix row column * right column))))

applyComposeRectangularExact :
  ∀ {Row Middle Column}
    (middleCarrier : Matrix.FiniteRationalCoordinates Middle)
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (left : RectangularMatrix Row Middle)
    (right : RectangularMatrix Middle Column)
    vector row →
  applyRectangular columnCarrier
    (composeRectangular middleCarrier left right) vector row
  ≡ applyRectangular middleCarrier left
      (applyRectangular columnCarrier right vector) row
applyComposeRectangularExact
    middleCarrier columnCarrier left right vector row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates columnCarrier)
      (λ column →
        Sums.sumRational (Matrix.coordinates middleCarrier)
          (λ middle → left row middle * right middle column)
        * vector column)
      (λ column →
        Sums.sumRational (Matrix.coordinates middleCarrier)
          (λ middle →
            (left row middle * right middle column) * vector column))
      (λ column →
        sym
          (Matrix.sumRationalRightScale
            (Matrix.coordinates middleCarrier)
            (λ middle → left row middle * right middle column)
            (vector column))))
    (trans
      (Fubini.sumSwap
        (Matrix.coordinates columnCarrier)
        (Matrix.coordinates middleCarrier)
        (λ column middle →
          (left row middle * right middle column) * vector column))
      (Sums.sumRationalCong
        (Matrix.coordinates middleCarrier)
        (λ middle →
          Sums.sumRational (Matrix.coordinates columnCarrier)
            (λ column →
              (left row middle * right middle column) * vector column))
        (λ middle →
          left row middle
            * applyRectangular columnCarrier right vector middle)
        (λ middle →
          trans
            (Sums.sumRationalCong
              (Matrix.coordinates columnCarrier)
              (λ column →
                (left row middle * right middle column) * vector column)
              (λ column →
                left row middle * (right middle column * vector column))
              (λ column → ℚRing.solve-∀
                (left row middle)
                (right middle column)
                (vector column)))
            (Sums.sumRationalScale
              (left row middle)
              (Matrix.coordinates columnCarrier)
              (λ column → right middle column * vector column))))))

rectangularAdjointExact :
  ∀ {Row Column}
    (rowCarrier : Matrix.FiniteRationalCoordinates Row)
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    vector multiplier →
  finiteDot rowCarrier
    (applyRectangular columnCarrier matrix vector)
    multiplier
  ≡ finiteDot columnCarrier vector
      (applyRectangular rowCarrier
        (transposeRectangular matrix) multiplier)
rectangularAdjointExact
    rowCarrier columnCarrier matrix vector multiplier =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates rowCarrier)
      (λ row →
        applyRectangular columnCarrier matrix vector row
          * multiplier row)
      (λ row →
        Sums.sumRational (Matrix.coordinates columnCarrier)
          (λ column →
            (matrix row column * vector column) * multiplier row))
      (λ row →
        Matrix.sumRationalRightScale
          (Matrix.coordinates columnCarrier)
          (λ column → matrix row column * vector column)
          (multiplier row)))
    (trans
      (Fubini.sumSwap
        (Matrix.coordinates rowCarrier)
        (Matrix.coordinates columnCarrier)
        (λ row column →
          (matrix row column * vector column) * multiplier row))
      (Sums.sumRationalCong
        (Matrix.coordinates columnCarrier)
        (λ column →
          Sums.sumRational (Matrix.coordinates rowCarrier)
            (λ row →
              (matrix row column * vector column) * multiplier row))
        (λ column →
          vector column
            * applyRectangular rowCarrier
                (transposeRectangular matrix) multiplier column)
        (λ column →
          trans
            (Sums.sumRationalCong
              (Matrix.coordinates rowCarrier)
              (λ row →
                (matrix row column * vector column) * multiplier row)
              (λ row →
                vector column * (matrix row column * multiplier row))
              (λ row → ℚRing.solve-∀
                (matrix row column)
                (vector column)
                (multiplier row)))
            (Sums.sumRationalScale
              (vector column)
              (Matrix.coordinates rowCarrier)
              (λ row → matrix row column * multiplier row))))))

transposeApplyOfSymmetric :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : Matrix.RationalMatrix Index) →
  (∀ left right → matrix left right ≡ matrix right left) →
  ∀ vector coordinate →
  applyRectangular carrier (transposeRectangular matrix)
    vector coordinate
  ≡ applyRectangular carrier matrix vector coordinate
transposeApplyOfSymmetric carrier matrix symmetric vector coordinate =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ column → matrix column coordinate * vector column)
    (λ column → matrix coordinate column * vector column)
    (λ column →
      cong (_* vector column)
        (symmetric column coordinate))

symmetricMatrixMovesAcrossDot :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : Matrix.RationalMatrix Index) →
  (∀ left right → matrix left right ≡ matrix right left) →
  ∀ left right →
  finiteDot carrier left
    (applyRectangular carrier matrix right)
  ≡ finiteDot carrier
      (applyRectangular carrier matrix left) right
symmetricMatrixMovesAcrossDot carrier matrix symmetric left right =
  trans
    (finiteDotSymmetric carrier left
      (applyRectangular carrier matrix right))
    (trans
      (rectangularAdjointExact
        carrier carrier matrix right left)
      (trans
        (Sums.sumRationalCong
          (Matrix.coordinates carrier)
          (λ coordinate →
            right coordinate
              * applyRectangular carrier
                  (transposeRectangular matrix) left coordinate)
          (λ coordinate →
            right coordinate
              * applyRectangular carrier matrix left coordinate)
          (λ coordinate →
            cong (right coordinate *_)
              (transposeApplyOfSymmetric
                carrier matrix symmetric left coordinate)))
        (finiteDotSymmetric carrier right
          (applyRectangular carrier matrix left))))

normSqAddExpansion :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index)
    left right →
  finiteNormSq carrier (vectorAdd left right)
  ≡ finiteNormSq carrier left
    + finiteNormSq carrier right
    + finiteDot carrier left right
    + finiteDot carrier right left
normSqAddExpansion carrier left right =
  trans
    (finiteDotAddLeft carrier left right (vectorAdd left right))
    (trans
      (cong₂ _+_
        (finiteDotAddRight carrier left left right)
        (finiteDotAddRight carrier right left right))
      (ℚRing.solve-∀
        (finiteNormSq carrier left)
        (finiteNormSq carrier right)
        (finiteDot carrier left right)
        (finiteDot carrier right left))))

normSqAddOrthogonal :
  ∀ {Index} (carrier : Matrix.FiniteRationalCoordinates Index)
    left right →
  finiteDot carrier left right ≡ 0ℚ →
  finiteDot carrier right left ≡ 0ℚ →
  finiteNormSq carrier (vectorAdd left right)
  ≡ finiteNormSq carrier left + finiteNormSq carrier right
normSqAddOrthogonal carrier left right leftRightZero rightLeftZero =
  trans
    (normSqAddExpansion carrier left right)
    (trans
      (cong
        (λ selected →
          finiteNormSq carrier left
          + finiteNormSq carrier right
          + selected
          + finiteDot carrier right left)
        leftRightZero)
      (trans
        (cong
          (λ selected →
            finiteNormSq carrier left
            + finiteNormSq carrier right
            + 0ℚ + selected)
          rightLeftZero)
        (ℚRing.solve-∀
          (finiteNormSq carrier left)
          (finiteNormSq carrier right))))

finiteRectangularCompositionLevel : ProofLevel
finiteRectangularCompositionLevel = machineChecked

finiteRectangularAdjointLevel : ProofLevel
finiteRectangularAdjointLevel = machineChecked

finiteRationalPythagoreanLevel : ProofLevel
finiteRationalPythagoreanLevel = machineChecked
