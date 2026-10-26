module DASHI.Biology.IITCubeConcreteNMatrixRecognitionExact where

------------------------------------------------------------------------
-- THE HARD-CODED STANDARD-COORDINATE MATRIX REALLY IS N = B + I
--
-- IITCubeConcreteJordanConjugacyExact gives an explicit matrix N_std and an
-- explicit invertible basis P,Q with Q N_std P = J.  This owner closes the
-- remaining recognition seam by proving every column of N_std is literally
-- nilpotentN applied to the corresponding standard Face9 basis vector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.IITCubeJordanChainCentralizerTargetExact as Jordan
import DASHI.Biology.IITCubeJordanBasisMatrixExact as Basis
import DASHI.Biology.IITCubeConcreteJordanConjugacyExact as Conjugacy

z o : Base.TriTruth
z = Base.tri-low
o = Base.tri-mid

standardBasisFace : Basis.Ix9 → Cube.Face9
standardBasisFace Basis.i0 = Fine.phaseFineTable9 o z z  z z z  z z z
standardBasisFace Basis.i1 = Fine.phaseFineTable9 z o z  z z z  z z z
standardBasisFace Basis.i2 = Fine.phaseFineTable9 z z o  z z z  z z z
standardBasisFace Basis.i3 = Fine.phaseFineTable9 z z z  o z z  z z z
standardBasisFace Basis.i4 = Fine.phaseFineTable9 z z z  z o z  z z z
standardBasisFace Basis.i5 = Fine.phaseFineTable9 z z z  z z o  z z z
standardBasisFace Basis.i6 = Fine.phaseFineTable9 z z z  z z z  o z z
standardBasisFace Basis.i7 = Fine.phaseFineTable9 z z z  z z z  z o z
standardBasisFace Basis.i8 = Fine.phaseFineTable9 z z z  z z z  z z o

concreteNColumn : Basis.Ix9 → Cube.Face9
concreteNColumn column = Basis.columnFace Conjugacy.concreteNMatrix column

concreteNColumnMatchesOperator :
  (column : Basis.Ix9) →
  concreteNColumn column ≡ Jordan.nilpotentN (standardBasisFace column)
concreteNColumnMatchesOperator Basis.i0 = refl
concreteNColumnMatchesOperator Basis.i1 = refl
concreteNColumnMatchesOperator Basis.i2 = refl
concreteNColumnMatchesOperator Basis.i3 = refl
concreteNColumnMatchesOperator Basis.i4 = refl
concreteNColumnMatchesOperator Basis.i5 = refl
concreteNColumnMatchesOperator Basis.i6 = refl
concreteNColumnMatchesOperator Basis.i7 = refl
concreteNColumnMatchesOperator Basis.i8 = refl

record ConcreteNMatrixRecognition : Set where
  constructor concrete-n-matrix-recognition
  field
    standardBasis : Basis.Ix9 → Cube.Face9
    matrixColumn : Basis.Ix9 → Cube.Face9
    everyColumnIsActualNImage :
      (column : Basis.Ix9) →
      matrixColumn column ≡ Jordan.nilpotentN (standardBasis column)
open ConcreteNMatrixRecognition public

canonicalConcreteNMatrixRecognition : ConcreteNMatrixRecognition
canonicalConcreteNMatrixRecognition =
  concrete-n-matrix-recognition
    standardBasisFace
    concreteNColumn
    concreteNColumnMatchesOperator
