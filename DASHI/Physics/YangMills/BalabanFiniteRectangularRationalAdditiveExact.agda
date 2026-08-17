module DASHI.Physics.YangMills.BalabanFiniteRectangularRationalAdditiveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION / STATIC API REPAIR
--
-- Round58 KKT/Moebius modules already consume additive dot-product identities,
-- pointwise congruence, zero/add/subtract application, vector subtraction and
-- the symmetric move-across-dot law under the `Rect` namespace, but the older
-- base rectangular module did not export those names.  This extension supplies
-- the missing literal finite-sum proofs without changing the carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact public
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix

vectorSubtract : ∀ {Index : Set} → Vector Index → Vector Index → Vector Index
vectorSubtract left right index = left index - right index

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
    (Matrix.coordinates carrier)
    _ _
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

finiteRectangularAdditiveLevel : ProofLevel
finiteRectangularAdditiveLevel = machineChecked

finiteRectangularSymmetricMoveLevel : ProofLevel
finiteRectangularSymmetricMoveLevel = machineChecked
