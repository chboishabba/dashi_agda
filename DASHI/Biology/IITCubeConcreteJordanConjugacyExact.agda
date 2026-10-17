module DASHI.Biology.IITCubeConcreteJordanConjugacyExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.IITCubeJordanBasisMatrixExact as Basis

z o : Base.TriTruth
z = Base.tri-low
o = Base.tri-mid

-- Standard-coordinate matrix of N = B + I in q00,q01,...,q22 order.
concreteNMatrix : Basis.Matrix9
concreteNMatrix Basis.i0 Basis.i0 = o
concreteNMatrix Basis.i0 Basis.i1 = o
concreteNMatrix Basis.i0 Basis.i3 = o
concreteNMatrix Basis.i1 Basis.i1 = o
concreteNMatrix Basis.i1 Basis.i2 = o
concreteNMatrix Basis.i1 Basis.i4 = o
concreteNMatrix Basis.i2 Basis.i0 = o
concreteNMatrix Basis.i2 Basis.i2 = o
concreteNMatrix Basis.i2 Basis.i5 = o
concreteNMatrix Basis.i3 Basis.i3 = o
concreteNMatrix Basis.i3 Basis.i4 = o
concreteNMatrix Basis.i3 Basis.i6 = o
concreteNMatrix Basis.i4 Basis.i4 = o
concreteNMatrix Basis.i4 Basis.i5 = o
concreteNMatrix Basis.i4 Basis.i7 = o
concreteNMatrix Basis.i5 Basis.i3 = o
concreteNMatrix Basis.i5 Basis.i5 = o
concreteNMatrix Basis.i5 Basis.i8 = o
concreteNMatrix Basis.i6 Basis.i0 = o
concreteNMatrix Basis.i6 Basis.i6 = o
concreteNMatrix Basis.i6 Basis.i7 = o
concreteNMatrix Basis.i7 Basis.i1 = o
concreteNMatrix Basis.i7 Basis.i7 = o
concreteNMatrix Basis.i7 Basis.i8 = o
concreteNMatrix Basis.i8 Basis.i2 = o
concreteNMatrix Basis.i8 Basis.i6 = o
concreteNMatrix Basis.i8 Basis.i8 = o
concreteNMatrix _ _ = z

-- Three nilpotent length-three Jordan blocks in A,B,C chain order.
jordanNMatrix : Basis.Matrix9
jordanNMatrix Basis.i0 Basis.i1 = o
jordanNMatrix Basis.i1 Basis.i2 = o
jordanNMatrix Basis.i3 Basis.i4 = o
jordanNMatrix Basis.i4 Basis.i5 = o
jordanNMatrix Basis.i6 Basis.i7 = o
jordanNMatrix Basis.i7 Basis.i8 = o
jordanNMatrix _ _ = z

conjugatedNMatrix : Basis.Matrix9
conjugatedNMatrix =
  Basis.matrixMul
    Basis.inverseMatrixQ
    (Basis.matrixMul concreteNMatrix Basis.basisMatrixP)

conjugatedNIsJordan : (row column : Basis.Ix9) →
  conjugatedNMatrix row column ≡ jordanNMatrix row column
conjugatedNIsJordan Basis.i0 Basis.i0 = refl
conjugatedNIsJordan Basis.i0 Basis.i1 = refl
conjugatedNIsJordan Basis.i0 Basis.i2 = refl
conjugatedNIsJordan Basis.i0 Basis.i3 = refl
conjugatedNIsJordan Basis.i0 Basis.i4 = refl
conjugatedNIsJordan Basis.i0 Basis.i5 = refl
conjugatedNIsJordan Basis.i0 Basis.i6 = refl
conjugatedNIsJordan Basis.i0 Basis.i7 = refl
conjugatedNIsJordan Basis.i0 Basis.i8 = refl
conjugatedNIsJordan Basis.i1 Basis.i0 = refl
conjugatedNIsJordan Basis.i1 Basis.i1 = refl
conjugatedNIsJordan Basis.i1 Basis.i2 = refl
conjugatedNIsJordan Basis.i1 Basis.i3 = refl
conjugatedNIsJordan Basis.i1 Basis.i4 = refl
conjugatedNIsJordan Basis.i1 Basis.i5 = refl
conjugatedNIsJordan Basis.i1 Basis.i6 = refl
conjugatedNIsJordan Basis.i1 Basis.i7 = refl
conjugatedNIsJordan Basis.i1 Basis.i8 = refl
conjugatedNIsJordan Basis.i2 Basis.i0 = refl
conjugatedNIsJordan Basis.i2 Basis.i1 = refl
conjugatedNIsJordan Basis.i2 Basis.i2 = refl
conjugatedNIsJordan Basis.i2 Basis.i3 = refl
conjugatedNIsJordan Basis.i2 Basis.i4 = refl
conjugatedNIsJordan Basis.i2 Basis.i5 = refl
conjugatedNIsJordan Basis.i2 Basis.i6 = refl
conjugatedNIsJordan Basis.i2 Basis.i7 = refl
conjugatedNIsJordan Basis.i2 Basis.i8 = refl
conjugatedNIsJordan Basis.i3 Basis.i0 = refl
conjugatedNIsJordan Basis.i3 Basis.i1 = refl
conjugatedNIsJordan Basis.i3 Basis.i2 = refl
conjugatedNIsJordan Basis.i3 Basis.i3 = refl
conjugatedNIsJordan Basis.i3 Basis.i4 = refl
conjugatedNIsJordan Basis.i3 Basis.i5 = refl
conjugatedNIsJordan Basis.i3 Basis.i6 = refl
conjugatedNIsJordan Basis.i3 Basis.i7 = refl
conjugatedNIsJordan Basis.i3 Basis.i8 = refl
conjugatedNIsJordan Basis.i4 Basis.i0 = refl
conjugatedNIsJordan Basis.i4 Basis.i1 = refl
conjugatedNIsJordan Basis.i4 Basis.i2 = refl
conjugatedNIsJordan Basis.i4 Basis.i3 = refl
conjugatedNIsJordan Basis.i4 Basis.i4 = refl
conjugatedNIsJordan Basis.i4 Basis.i5 = refl
conjugatedNIsJordan Basis.i4 Basis.i6 = refl
conjugatedNIsJordan Basis.i4 Basis.i7 = refl
conjugatedNIsJordan Basis.i4 Basis.i8 = refl
conjugatedNIsJordan Basis.i5 Basis.i0 = refl
conjugatedNIsJordan Basis.i5 Basis.i1 = refl
conjugatedNIsJordan Basis.i5 Basis.i2 = refl
conjugatedNIsJordan Basis.i5 Basis.i3 = refl
conjugatedNIsJordan Basis.i5 Basis.i4 = refl
conjugatedNIsJordan Basis.i5 Basis.i5 = refl
conjugatedNIsJordan Basis.i5 Basis.i6 = refl
conjugatedNIsJordan Basis.i5 Basis.i7 = refl
conjugatedNIsJordan Basis.i5 Basis.i8 = refl
conjugatedNIsJordan Basis.i6 Basis.i0 = refl
conjugatedNIsJordan Basis.i6 Basis.i1 = refl
conjugatedNIsJordan Basis.i6 Basis.i2 = refl
conjugatedNIsJordan Basis.i6 Basis.i3 = refl
conjugatedNIsJordan Basis.i6 Basis.i4 = refl
conjugatedNIsJordan Basis.i6 Basis.i5 = refl
conjugatedNIsJordan Basis.i6 Basis.i6 = refl
conjugatedNIsJordan Basis.i6 Basis.i7 = refl
conjugatedNIsJordan Basis.i6 Basis.i8 = refl
conjugatedNIsJordan Basis.i7 Basis.i0 = refl
conjugatedNIsJordan Basis.i7 Basis.i1 = refl
conjugatedNIsJordan Basis.i7 Basis.i2 = refl
conjugatedNIsJordan Basis.i7 Basis.i3 = refl
conjugatedNIsJordan Basis.i7 Basis.i4 = refl
conjugatedNIsJordan Basis.i7 Basis.i5 = refl
conjugatedNIsJordan Basis.i7 Basis.i6 = refl
conjugatedNIsJordan Basis.i7 Basis.i7 = refl
conjugatedNIsJordan Basis.i7 Basis.i8 = refl
conjugatedNIsJordan Basis.i8 Basis.i0 = refl
conjugatedNIsJordan Basis.i8 Basis.i1 = refl
conjugatedNIsJordan Basis.i8 Basis.i2 = refl
conjugatedNIsJordan Basis.i8 Basis.i3 = refl
conjugatedNIsJordan Basis.i8 Basis.i4 = refl
conjugatedNIsJordan Basis.i8 Basis.i5 = refl
conjugatedNIsJordan Basis.i8 Basis.i6 = refl
conjugatedNIsJordan Basis.i8 Basis.i7 = refl
conjugatedNIsJordan Basis.i8 Basis.i8 = refl

record ConcreteJordanConjugacyWitness : Set where
  constructor concrete-jordan-conjugacy-witness
  field
    standardNilpotentMatrix : Basis.Matrix9
    basisMatrix : Basis.Matrix9
    inverseBasisMatrix : Basis.Matrix9
    jordanMatrix : Basis.Matrix9
    basisLeftInverse : (row column : Basis.Ix9) →
      Basis.matrixMul basisMatrix inverseBasisMatrix row column
      ≡ Basis.identity9 row column
    basisRightInverse : (row column : Basis.Ix9) →
      Basis.matrixMul inverseBasisMatrix basisMatrix row column
      ≡ Basis.identity9 row column
    conjugacy : (row column : Basis.Ix9) →
      Basis.matrixMul inverseBasisMatrix
        (Basis.matrixMul standardNilpotentMatrix basisMatrix)
        row column
      ≡ jordanMatrix row column
open ConcreteJordanConjugacyWitness public

canonicalConcreteJordanConjugacyWitness : ConcreteJordanConjugacyWitness
canonicalConcreteJordanConjugacyWitness =
  concrete-jordan-conjugacy-witness
    concreteNMatrix
    Basis.basisMatrixP
    Basis.inverseMatrixQ
    jordanNMatrix
    Basis.pTimesQIsIdentity
    Basis.qTimesPIsIdentity
    conjugatedNIsJordan
