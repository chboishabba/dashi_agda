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
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
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

finiteRectangularRationalLevel : ProofLevel
finiteRectangularRationalLevel = machineChecked

finiteRectangularCompositionLevel : ProofLevel
finiteRectangularCompositionLevel = machineChecked

finiteRectangularAdjointLevel : ProofLevel
finiteRectangularAdjointLevel = machineChecked
