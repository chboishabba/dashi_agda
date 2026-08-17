module DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Exact finite rational calculus for rectangular matrices on the repository's
-- proof-bearing finite coordinate carriers.  This module supplies the common
-- algebra used by the selected 780 x 3072 constraint, its transpose, Gram
-- matrix and KKT identities:
--
--   apply(A B) v = A (B v),
--   <A v,w> = <v,A^T w>,
--   ||v||^2 = sum_i v_i^2 >= 0.
--
-- Every identity is proved by literal finite Fubini/reassociation.  No
-- dimension argument, spectral theorem, function extensionality, or hidden
-- infinite sum is used.
--
-- ROUND60 STATIC REPAIR
--
-- The KKT/pseudoinverse modules already consumed pointwise congruence,
-- add/subtract application, dot add/subtract and symmetric move-across-dot
-- identities under this namespace, but the base file did not export them.
-- They are proved here directly so the existing callers and the Round60
-- PSD/polarization reductions share one actual finite-linear-algebra authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

RectangularMatrix : Set → Set → Set
RectangularMatrix Row Column = Row → Column → ℚ

Vector : Set → Set
Vector Index = Index → ℚ

vectorAdd : ∀ {Index : Set} → Vector Index → Vector Index → Vector Index
vectorAdd left right index = left index + right index

vectorSubtract : ∀ {Index : Set} → Vector Index → Vector Index → Vector Index
vectorSubtract left right index = left index - right index

applyRectangular :
  ∀ {Row Column : Set} →
  Matrix.FiniteRationalCoordinates Column →
  RectangularMatrix Row Column → Vector Column → Vector Row
applyRectangular carrier matrix vector row =
  Sums.sumRational (Matrix.coordinates carrier)
    (λ column → matrix row column * vector column)

transposeRectangular :
  ∀ {Row Column : Set} →
  RectangularMatrix Row Column → RectangularMatrix Column Row
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

finiteDot :
  ∀ {Index : Set} →
  Matrix.FiniteRationalCoordinates Index →
  Vector Index → Vector Index → ℚ
finiteDot carrier left right =
  Sums.sumRational (Matrix.coordinates carrier)
    (λ index → left index * right index)

finiteNormSq :
  ∀ {Index : Set} →
  Matrix.FiniteRationalCoordinates Index → Vector Index → ℚ
finiteNormSq carrier vector = finiteDot carrier vector vector

finiteNormSqNonnegative :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index) vector →
  0ℚ ≤ finiteNormSq carrier vector
finiteNormSqNonnegative carrier vector =
  Schur.sumNonnegative
    (Matrix.coordinates carrier)
    (λ index → vector index * vector index)
    (λ index → FiniteL2.squareNonnegative (vector index))

applyRectangularAddExact :
  ∀ {Row Column : Set}
    (carrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    left right row →
  applyRectangular carrier matrix (vectorAdd left right) row
  ≡ applyRectangular carrier matrix left row
    + applyRectangular carrier matrix right row
applyRectangularAddExact carrier matrix left right row =
  trans
    (Sums.sumRationalCong (Matrix.coordinates carrier) _ _
      (λ column →
        ℚP.*-distribˡ-+
          (matrix row column) (left column) (right column)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ column → matrix row column * left column)
      (λ column → matrix row column * right column))

applyComposeRectangularExact :
  ∀ {Row Middle Column : Set}
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
  let
    columns = Matrix.coordinates columnCarrier
    middles = Matrix.coordinates middleCarrier

    expandProducts :
      Sums.sumRational columns
        (λ column →
          Sums.sumRational middles
            (λ middle → left row middle * right middle column)
          * vector column)
      ≡ Sums.sumRational columns
          (λ column →
            Sums.sumRational middles
              (λ middle →
                (left row middle * right middle column) * vector column))
    expandProducts = Sums.sumRationalCong columns _ _
      (λ column →
        trans
          (ℚP.*-comm
            (Sums.sumRational middles
              (λ middle → left row middle * right middle column))
            (vector column))
          (trans
            (sym
              (Sums.sumRationalScale
                (vector column) middles
                (λ middle → left row middle * right middle column)))
            (Sums.sumRationalCong middles _ _
              (λ middle →
                ℚP.*-comm
                  (vector column)
                  (left row middle * right middle column)))))

    swap :
      Sums.sumRational columns
        (λ column →
          Sums.sumRational middles
            (λ middle →
              (left row middle * right middle column) * vector column))
      ≡ Sums.sumRational middles
          (λ middle →
            Sums.sumRational columns
              (λ column →
                (left row middle * right middle column) * vector column))
    swap = Fubini.sumSwap columns middles
      (λ column middle →
        (left row middle * right middle column) * vector column)

    factorLeft :
      Sums.sumRational middles
        (λ middle →
          Sums.sumRational columns
            (λ column →
              (left row middle * right middle column) * vector column))
      ≡ Sums.sumRational middles
          (λ middle →
            left row middle
            * Sums.sumRational columns
                (λ column → right middle column * vector column))
    factorLeft = Sums.sumRationalCong middles _ _
      (λ middle →
        trans
          (Sums.sumRationalCong columns _ _
            (λ column →
              ℚP.*-assoc
                (left row middle) (right middle column) (vector column)))
          (Sums.sumRationalScale
            (left row middle) columns
            (λ column → right middle column * vector column)))
  in
  trans expandProducts (trans swap factorLeft)

rectangularAdjointExact :
  ∀ {Row Column : Set}
    (rowCarrier : Matrix.FiniteRationalCoordinates Row)
    (columnCarrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    vector multiplier →
  finiteDot rowCarrier
    (applyRectangular columnCarrier matrix vector) multiplier
  ≡ finiteDot columnCarrier vector
      (applyRectangular rowCarrier (transposeRectangular matrix) multiplier)
rectangularAdjointExact rowCarrier columnCarrier matrix vector multiplier =
  let
    rows = Matrix.coordinates rowCarrier
    columns = Matrix.coordinates columnCarrier

    expandLeft :
      Sums.sumRational rows
        (λ row →
          Sums.sumRational columns
            (λ column → matrix row column * vector column)
          * multiplier row)
      ≡ Sums.sumRational rows
          (λ row →
            Sums.sumRational columns
              (λ column →
                (matrix row column * vector column) * multiplier row))
    expandLeft = Sums.sumRationalCong rows _ _
      (λ row →
        trans
          (ℚP.*-comm
            (Sums.sumRational columns
              (λ column → matrix row column * vector column))
            (multiplier row))
          (trans
            (sym
              (Sums.sumRationalScale
                (multiplier row) columns
                (λ column → matrix row column * vector column)))
            (Sums.sumRationalCong columns _ _
              (λ column →
                ℚP.*-comm
                  (multiplier row)
                  (matrix row column * vector column)))))

    swap :
      Sums.sumRational rows
        (λ row →
          Sums.sumRational columns
            (λ column →
              (matrix row column * vector column) * multiplier row))
      ≡ Sums.sumRational columns
          (λ column →
            Sums.sumRational rows
              (λ row →
                (matrix row column * vector column) * multiplier row))
    swap = Fubini.sumSwap rows columns
      (λ row column →
        (matrix row column * vector column) * multiplier row)

    reorder :
      Sums.sumRational columns
        (λ column →
          Sums.sumRational rows
            (λ row →
              (matrix row column * vector column) * multiplier row))
      ≡ Sums.sumRational columns
          (λ column →
            vector column
            * Sums.sumRational rows
                (λ row → matrix row column * multiplier row))
    reorder = Sums.sumRationalCong columns _ _
      (λ column →
        trans
          (Sums.sumRationalCong rows _ _
            (λ row →
              trans
                (ℚP.*-assoc
                  (matrix row column) (vector column) (multiplier row))
                (trans
                  (sym
                    (ℚP.*-assoc
                      (matrix row column) (vector column) (multiplier row)))
                  (trans
                    (cong
                      (λ value → value * multiplier row)
                      (ℚP.*-comm
                        (matrix row column) (vector column)))
                    (ℚP.*-assoc
                      (vector column) (matrix row column) (multiplier row))))))
          (Sums.sumRationalScale
            (vector column) rows
            (λ row → matrix row column * multiplier row)))
  in
  trans expandLeft (trans swap reorder)

finiteDotSymmetric :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left right →
  finiteDot carrier left right ≡ finiteDot carrier right left
finiteDotSymmetric carrier left right =
  Sums.sumRationalCong (Matrix.coordinates carrier) _ _
    (λ index → ℚP.*-comm (left index) (right index))

------------------------------------------------------------------------
-- Additive / congruence API used by the finite KKT development.
------------------------------------------------------------------------

applyRectangularVectorCong :
  ∀ {Row Column}
    (carrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    {left right : Column → ℚ} →
  (∀ column → left column ≡ right column) →
  ∀ row →
  applyRectangular carrier matrix left row
  ≡ applyRectangular carrier matrix right row
applyRectangularVectorCong carrier matrix pointwise row =
  Sums.sumRationalCong
    (Matrix.coordinates carrier) _ _
    (λ column → cong (matrix row column *_) (pointwise column))

applyRectangularZero :
  ∀ {Row Column}
    (carrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column) row →
  applyRectangular carrier matrix (λ _ → 0ℚ) row ≡ 0ℚ
applyRectangularZero carrier matrix row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier) _ (λ _ → 0ℚ)
      (λ column → ℚRing.solve-∀ (matrix row column)))
    (Fubini.sumRationalZero (Matrix.coordinates carrier))

applyRectangularAdd :
  ∀ {Row Column}
    (carrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    left right row →
  applyRectangular carrier matrix (vectorAdd left right) row
  ≡ applyRectangular carrier matrix left row
    + applyRectangular carrier matrix right row
applyRectangularAdd = applyRectangularAddExact

sumRationalSubtract :
  ∀ {Index : Set} (indices : List Index) (left right : Index → ℚ) →
  Sums.sumRational indices (λ index → left index - right index)
  ≡ Sums.sumRational indices left - Sums.sumRational indices right
sumRationalSubtract [] left right = ℚRing.solve []
sumRationalSubtract (index ∷ indices) left right
  rewrite sumRationalSubtract indices left right =
  ℚRing.solve-∀
    (left index) (right index)
    (Sums.sumRational indices left)
    (Sums.sumRational indices right)

applyRectangularSubtract :
  ∀ {Row Column}
    (carrier : Matrix.FiniteRationalCoordinates Column)
    (matrix : RectangularMatrix Row Column)
    left right row →
  applyRectangular carrier matrix (vectorSubtract left right) row
  ≡ applyRectangular carrier matrix left row
    - applyRectangular carrier matrix right row
applyRectangularSubtract carrier matrix left right row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier) _ _
      (λ column →
        ℚRing.solve-∀ (matrix row column) (left column) (right column)))
    (sumRationalSubtract
      (Matrix.coordinates carrier)
      (λ column → matrix row column * left column)
      (λ column → matrix row column * right column))

finiteDotLeftPointwiseCong :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    {left transported right : Index → ℚ} →
  (∀ index → left index ≡ transported index) →
  finiteDot carrier left right ≡ finiteDot carrier transported right
finiteDotLeftPointwiseCong carrier {left} {transported} {right} pointwise =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ index → left index * right index)
    (λ index → transported index * right index)
    (λ index → cong (_* right index) (pointwise index))

finiteDotRightPointwiseCong :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    {left right transported : Index → ℚ} →
  (∀ index → right index ≡ transported index) →
  finiteDot carrier left right ≡ finiteDot carrier left transported
finiteDotRightPointwiseCong carrier {left} {right} {transported} pointwise =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ index → left index * right index)
    (λ index → left index * transported index)
    (λ index → cong (left index *_) (pointwise index))

finiteDotAddLeft :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left right vector →
  finiteDot carrier (vectorAdd left right) vector
  ≡ finiteDot carrier left vector + finiteDot carrier right vector
finiteDotAddLeft carrier left right vector =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier) _ _
      (λ index → ℚRing.solve-∀ (left index) (right index) (vector index)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ index → left index * vector index)
      (λ index → right index * vector index))

finiteDotAddRight :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    vector left right →
  finiteDot carrier vector (vectorAdd left right)
  ≡ finiteDot carrier vector left + finiteDot carrier vector right
finiteDotAddRight carrier vector left right =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier) _ _
      (λ index → ℚRing.solve-∀ (vector index) (left index) (right index)))
    (Fubini.sumRationalAdd
      (Matrix.coordinates carrier)
      (λ index → vector index * left index)
      (λ index → vector index * right index))

finiteDotSubtractLeft :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left right vector →
  finiteDot carrier (vectorSubtract left right) vector
  ≡ finiteDot carrier left vector - finiteDot carrier right vector
finiteDotSubtractLeft carrier left right vector =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier) _ _
      (λ index → ℚRing.solve-∀ (left index) (right index) (vector index)))
    (sumRationalSubtract
      (Matrix.coordinates carrier)
      (λ index → left index * vector index)
      (λ index → right index * vector index))

finiteDotSubtractRight :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    vector left right →
  finiteDot carrier vector (vectorSubtract left right)
  ≡ finiteDot carrier vector left - finiteDot carrier vector right
finiteDotSubtractRight carrier vector left right =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier) _ _
      (λ index → ℚRing.solve-∀ (vector index) (left index) (right index)))
    (sumRationalSubtract
      (Matrix.coordinates carrier)
      (λ index → vector index * left index)
      (λ index → vector index * right index))

applyTransposeEqualsApplySymmetric :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : RectangularMatrix Index Index) →
  (∀ left right → matrix left right ≡ matrix right left) →
  ∀ vector row →
  applyRectangular carrier (transposeRectangular matrix) vector row
  ≡ applyRectangular carrier matrix vector row
applyTransposeEqualsApplySymmetric carrier matrix symmetry vector row =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ column → matrix column row * vector column)
    (λ column → matrix row column * vector column)
    (λ column → cong (_* vector column) (symmetry column row))

symmetricMatrixMovesAcrossDot :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : RectangularMatrix Index Index) →
  (∀ left right → matrix left right ≡ matrix right left) →
  ∀ left right →
  finiteDot carrier left (applyRectangular carrier matrix right)
  ≡ finiteDot carrier (applyRectangular carrier matrix left) right
symmetricMatrixMovesAcrossDot carrier matrix symmetry left right =
  trans
    (finiteDotSymmetric carrier left (applyRectangular carrier matrix right))
    (trans
      (rectangularAdjointExact carrier carrier matrix right left)
      (trans
        (finiteDotRightPointwiseCong carrier
          (applyTransposeEqualsApplySymmetric
            carrier matrix symmetry left))
        (finiteDotSymmetric carrier right
          (applyRectangular carrier matrix left))))

finiteRectangularRationalLevel : ProofLevel
finiteRectangularRationalLevel = machineChecked

finiteRectangularCompositionLevel : ProofLevel
finiteRectangularCompositionLevel = machineChecked

finiteRectangularAdjointLevel : ProofLevel
finiteRectangularAdjointLevel = machineChecked

finiteRectangularAdditiveLevel : ProofLevel
finiteRectangularAdditiveLevel = machineChecked

finiteRectangularSymmetricMoveLevel : ProofLevel
finiteRectangularSymmetricMoveLevel = machineChecked
