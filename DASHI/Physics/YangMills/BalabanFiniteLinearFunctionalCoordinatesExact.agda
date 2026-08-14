module DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove, rather than assume, the coordinate row of a finite linear
-- functional.  For the repository's concrete finite carrier and Kronecker
-- delta, every linear functional F satisfies
--
--   F(v) = sum_j F(e_j) v_j.
--
-- This is the exact bridge used below to turn the already literal
-- selected-background gauge derivative into a rectangular KKT matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

Vector : Set → Set
Vector Index = Index → ℚ

zeroVector : ∀ {Index} → Vector Index
zeroVector _ = 0ℚ

addVector : ∀ {Index} → Vector Index → Vector Index → Vector Index
addVector left right index = left index + right index

scaleVector : ∀ {Index} → ℚ → Vector Index → Vector Index
scaleVector coefficient vector index = coefficient * vector index

basisVector : ∀ {Index} →
  Matrix.FiniteRationalCoordinates Index → Index → Vector Index
basisVector carrier column row = Matrix.delta carrier row column

listCoordinateExpansion : ∀ {Index} →
  Matrix.FiniteRationalCoordinates Index →
  List Index → Vector Index → Vector Index
listCoordinateExpansion carrier [] vector = zeroVector
listCoordinateExpansion carrier (column ∷ columns) vector =
  addVector
    (scaleVector (vector column) (basisVector carrier column))
    (listCoordinateExpansion carrier columns vector)

record FiniteLinearFunctional {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index) : Set₁ where
  field
    functional : Vector Index → ℚ
    zeroExact : functional zeroVector ≡ 0ℚ
    addExact : ∀ left right →
      functional (addVector left right)
      ≡ functional left + functional right
    scaleExact : ∀ coefficient vector →
      functional (scaleVector coefficient vector)
      ≡ coefficient * functional vector
    pointwiseCong : ∀ left right →
      (∀ index → left index ≡ right index) →
      functional left ≡ functional right
open FiniteLinearFunctional public

functionalOfListExpansion :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index}
    (linear : FiniteLinearFunctional carrier)
    columns vector →
  functional linear (listCoordinateExpansion carrier columns vector)
  ≡ Sums.sumRational columns
      (λ column →
        functional linear (basisVector carrier column) * vector column)
functionalOfListExpansion linear [] vector = zeroExact linear
functionalOfListExpansion {carrier = carrier}
    linear (column ∷ columns) vector =
  trans
    (addExact linear
      (scaleVector (vector column) (basisVector carrier column))
      (listCoordinateExpansion carrier columns vector))
    (trans
      (cong
        (λ tail →
          functional linear
            (scaleVector (vector column) (basisVector carrier column))
          + tail)
        (functionalOfListExpansion linear columns vector))
      (trans
        (cong
          (λ head → head
            + Sums.sumRational columns
                (λ selected →
                  functional linear (basisVector carrier selected)
                  * vector selected))
          (scaleExact linear
            (vector column) (basisVector carrier column)))
        (cong
          (λ head → head
            + Sums.sumRational columns
                (λ selected →
                  functional linear (basisVector carrier selected)
                  * vector selected))
          (ℚP.*-comm
            (vector column)
            (functional linear (basisVector carrier column))))))

listExpansionPointwiseAsSum :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    columns vector row →
  listCoordinateExpansion carrier columns vector row
  ≡ Sums.sumRational columns
      (λ column →
        vector column * Matrix.delta carrier row column)
listExpansionPointwiseAsSum carrier [] vector row =
  refl
listExpansionPointwiseAsSum carrier (column ∷ columns) vector row =
  cong
    (vector column * Matrix.delta carrier row column +_)
    (listExpansionPointwiseAsSum carrier columns vector row)

listExpansionIsVector :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    vector row →
  listCoordinateExpansion
    carrier (Matrix.coordinates carrier) vector row
  ≡ vector row
listExpansionIsVector carrier vector row =
  trans
    (listExpansionPointwiseAsSum
      carrier (Matrix.coordinates carrier) vector row)
    (trans
      (Sums.sumRationalCong
        (Matrix.coordinates carrier)
        (λ column →
          vector column * Matrix.delta carrier row column)
        (λ column →
          Matrix.delta carrier row column * vector column)
        (λ column → ℚP.*-comm (vector column) (Matrix.delta carrier row column)))
      (Matrix.deltaActsAsIdentity carrier vector row))

finiteLinearFunctionalCoordinateExpansion :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index}
    (linear : FiniteLinearFunctional carrier)
    vector →
  Sums.sumRational (Matrix.coordinates carrier)
    (λ column →
      functional linear (basisVector carrier column) * vector column)
  ≡ functional linear vector
finiteLinearFunctionalCoordinateExpansion
    {carrier = carrier} linear vector =
  trans
    (sym
      (functionalOfListExpansion linear
        (Matrix.coordinates carrier) vector))
    (pointwiseCong linear
      (listCoordinateExpansion
        carrier (Matrix.coordinates carrier) vector)
      vector
      (listExpansionIsVector carrier vector))
