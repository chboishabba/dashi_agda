module DASHI.Biology.IITCubeJordanBasisMatrixExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.IITCubeJordanChainCentralizerTargetExact as Jordan

data Ix9 : Set where
  i0 i1 i2 i3 i4 i5 i6 i7 i8 : Ix9

Matrix9 : Set
Matrix9 = Ix9 → Ix9 → Base.TriTruth

z o m : Base.TriTruth
z = Base.tri-low
o = Base.tri-mid
m = Base.tri-high

sum9 : (Ix9 → Base.TriTruth) → Base.TriTruth
sum9 f =
  F3.triAdd (f i0)
    (F3.triAdd (f i1)
      (F3.triAdd (f i2)
        (F3.triAdd (f i3)
          (F3.triAdd (f i4)
            (F3.triAdd (f i5)
              (F3.triAdd (f i6)
                (F3.triAdd (f i7) (f i8))))))))

matrixMul : Matrix9 → Matrix9 → Matrix9
matrixMul a b row column =
  sum9 (λ k → F3.triMul (a row k) (b k column))

identity9 : Matrix9
identity9 i0 i0 = o
identity9 i1 i1 = o
identity9 i2 i2 = o
identity9 i3 i3 = o
identity9 i4 i4 = o
identity9 i5 i5 = o
identity9 i6 i6 = o
identity9 i7 i7 = o
identity9 i8 i8 = o
identity9 _ _ = z

-- Columns: A0,A1,A2,B0,B1,B2,C0,C1,C2.
basisMatrixP : Matrix9
basisMatrixP i0 i0 = o
basisMatrixP i0 i1 = o
basisMatrixP i0 i2 = o
basisMatrixP i0 i3 = m
basisMatrixP i0 i4 = o
basisMatrixP i0 i5 = z
basisMatrixP i0 i6 = o
basisMatrixP i0 i7 = z
basisMatrixP i0 i8 = z
basisMatrixP i1 i0 = o
basisMatrixP i1 i1 = z
basisMatrixP i1 i2 = z
basisMatrixP i1 i3 = o
basisMatrixP i1 i4 = o
basisMatrixP i1 i5 = o
basisMatrixP i1 i6 = m
basisMatrixP i1 i7 = o
basisMatrixP i1 i8 = z
basisMatrixP i2 i0 = m
basisMatrixP i2 i1 = o
basisMatrixP i2 i2 = z
basisMatrixP i2 i3 = o
basisMatrixP i2 i4 = z
basisMatrixP i2 i5 = z
basisMatrixP i2 i6 = o
basisMatrixP i2 i7 = o
basisMatrixP i2 i8 = o
basisMatrixP i3 i0 = o
basisMatrixP i3 i1 = z
basisMatrixP i3 i2 = z
basisMatrixP i3 i3 = z
basisMatrixP i3 i4 = z
basisMatrixP i3 i5 = z
basisMatrixP i3 i6 = z
basisMatrixP i3 i7 = z
basisMatrixP i3 i8 = z
basisMatrixP i4 i0 = z
basisMatrixP i4 i1 = z
basisMatrixP i4 i2 = z
basisMatrixP i4 i3 = o
basisMatrixP i4 i4 = z
basisMatrixP i4 i5 = z
basisMatrixP i4 i6 = z
basisMatrixP i4 i7 = z
basisMatrixP i4 i8 = z
basisMatrixP i5 i0 = z
basisMatrixP i5 i1 = z
basisMatrixP i5 i2 = z
basisMatrixP i5 i3 = z
basisMatrixP i5 i4 = z
basisMatrixP i5 i5 = z
basisMatrixP i5 i6 = o
basisMatrixP i5 i7 = z
basisMatrixP i5 i8 = z
basisMatrixP i6 i0 = m
basisMatrixP i6 i1 = o
basisMatrixP i6 i2 = z
basisMatrixP i6 i3 = m
basisMatrixP i6 i4 = z
basisMatrixP i6 i5 = z
basisMatrixP i6 i6 = z
basisMatrixP i6 i7 = z
basisMatrixP i6 i8 = z
basisMatrixP i7 i0 = z
basisMatrixP i7 i1 = z
basisMatrixP i7 i2 = z
basisMatrixP i7 i3 = m
basisMatrixP i7 i4 = o
basisMatrixP i7 i5 = z
basisMatrixP i7 i6 = m
basisMatrixP i7 i7 = z
basisMatrixP i7 i8 = z
basisMatrixP i8 i0 = m
basisMatrixP i8 i1 = z
basisMatrixP i8 i2 = z
basisMatrixP i8 i3 = z
basisMatrixP i8 i4 = z
basisMatrixP i8 i5 = z
basisMatrixP i8 i6 = m
basisMatrixP i8 i7 = o
basisMatrixP i8 i8 = z

inverseMatrixQ : Matrix9
inverseMatrixQ i0 i0 = z
inverseMatrixQ i0 i1 = z
inverseMatrixQ i0 i2 = z
inverseMatrixQ i0 i3 = o
inverseMatrixQ i0 i4 = z
inverseMatrixQ i0 i5 = z
inverseMatrixQ i0 i6 = z
inverseMatrixQ i0 i7 = z
inverseMatrixQ i0 i8 = z
inverseMatrixQ i1 i0 = z
inverseMatrixQ i1 i1 = z
inverseMatrixQ i1 i2 = z
inverseMatrixQ i1 i3 = o
inverseMatrixQ i1 i4 = o
inverseMatrixQ i1 i5 = z
inverseMatrixQ i1 i6 = o
inverseMatrixQ i1 i7 = z
inverseMatrixQ i1 i8 = z
inverseMatrixQ i2 i0 = o
inverseMatrixQ i2 i1 = z
inverseMatrixQ i2 i2 = z
inverseMatrixQ i2 i3 = o
inverseMatrixQ i2 i4 = m
inverseMatrixQ i2 i5 = o
inverseMatrixQ i2 i6 = m
inverseMatrixQ i2 i7 = m
inverseMatrixQ i2 i8 = z
inverseMatrixQ i3 i0 = z
inverseMatrixQ i3 i1 = z
inverseMatrixQ i3 i2 = z
inverseMatrixQ i3 i3 = z
inverseMatrixQ i3 i4 = o
inverseMatrixQ i3 i5 = z
inverseMatrixQ i3 i6 = z
inverseMatrixQ i3 i7 = z
inverseMatrixQ i3 i8 = z
inverseMatrixQ i4 i0 = z
inverseMatrixQ i4 i1 = z
inverseMatrixQ i4 i2 = z
inverseMatrixQ i4 i3 = z
inverseMatrixQ i4 i4 = o
inverseMatrixQ i4 i5 = o
inverseMatrixQ i4 i6 = z
inverseMatrixQ i4 i7 = o
inverseMatrixQ i4 i8 = z
inverseMatrixQ i5 i0 = z
inverseMatrixQ i5 i1 = o
inverseMatrixQ i5 i2 = z
inverseMatrixQ i5 i3 = o
inverseMatrixQ i5 i4 = o
inverseMatrixQ i5 i5 = m
inverseMatrixQ i5 i6 = z
inverseMatrixQ i5 i7 = m
inverseMatrixQ i5 i8 = m
inverseMatrixQ i6 i0 = z
inverseMatrixQ i6 i1 = z
inverseMatrixQ i6 i2 = z
inverseMatrixQ i6 i3 = z
inverseMatrixQ i6 i4 = z
inverseMatrixQ i6 i5 = o
inverseMatrixQ i6 i6 = z
inverseMatrixQ i6 i7 = z
inverseMatrixQ i6 i8 = z
inverseMatrixQ i7 i0 = z
inverseMatrixQ i7 i1 = z
inverseMatrixQ i7 i2 = z
inverseMatrixQ i7 i3 = o
inverseMatrixQ i7 i4 = z
inverseMatrixQ i7 i5 = o
inverseMatrixQ i7 i6 = z
inverseMatrixQ i7 i7 = z
inverseMatrixQ i7 i8 = o
inverseMatrixQ i8 i0 = z
inverseMatrixQ i8 i1 = z
inverseMatrixQ i8 i2 = o
inverseMatrixQ i8 i3 = m
inverseMatrixQ i8 i4 = o
inverseMatrixQ i8 i5 = o
inverseMatrixQ i8 i6 = m
inverseMatrixQ i8 i7 = z
inverseMatrixQ i8 i8 = m

pTimesQIsIdentity : (row column : Ix9) →
  matrixMul basisMatrixP inverseMatrixQ row column ≡ identity9 row column
pTimesQIsIdentity i0 i0 = refl
pTimesQIsIdentity i0 i1 = refl
pTimesQIsIdentity i0 i2 = refl
pTimesQIsIdentity i0 i3 = refl
pTimesQIsIdentity i0 i4 = refl
pTimesQIsIdentity i0 i5 = refl
pTimesQIsIdentity i0 i6 = refl
pTimesQIsIdentity i0 i7 = refl
pTimesQIsIdentity i0 i8 = refl
pTimesQIsIdentity i1 i0 = refl
pTimesQIsIdentity i1 i1 = refl
pTimesQIsIdentity i1 i2 = refl
pTimesQIsIdentity i1 i3 = refl
pTimesQIsIdentity i1 i4 = refl
pTimesQIsIdentity i1 i5 = refl
pTimesQIsIdentity i1 i6 = refl
pTimesQIsIdentity i1 i7 = refl
pTimesQIsIdentity i1 i8 = refl
pTimesQIsIdentity i2 i0 = refl
pTimesQIsIdentity i2 i1 = refl
pTimesQIsIdentity i2 i2 = refl
pTimesQIsIdentity i2 i3 = refl
pTimesQIsIdentity i2 i4 = refl
pTimesQIsIdentity i2 i5 = refl
pTimesQIsIdentity i2 i6 = refl
pTimesQIsIdentity i2 i7 = refl
pTimesQIsIdentity i2 i8 = refl
pTimesQIsIdentity i3 i0 = refl
pTimesQIsIdentity i3 i1 = refl
pTimesQIsIdentity i3 i2 = refl
pTimesQIsIdentity i3 i3 = refl
pTimesQIsIdentity i3 i4 = refl
pTimesQIsIdentity i3 i5 = refl
pTimesQIsIdentity i3 i6 = refl
pTimesQIsIdentity i3 i7 = refl
pTimesQIsIdentity i3 i8 = refl
pTimesQIsIdentity i4 i0 = refl
pTimesQIsIdentity i4 i1 = refl
pTimesQIsIdentity i4 i2 = refl
pTimesQIsIdentity i4 i3 = refl
pTimesQIsIdentity i4 i4 = refl
pTimesQIsIdentity i4 i5 = refl
pTimesQIsIdentity i4 i6 = refl
pTimesQIsIdentity i4 i7 = refl
pTimesQIsIdentity i4 i8 = refl
pTimesQIsIdentity i5 i0 = refl
pTimesQIsIdentity i5 i1 = refl
pTimesQIsIdentity i5 i2 = refl
pTimesQIsIdentity i5 i3 = refl
pTimesQIsIdentity i5 i4 = refl
pTimesQIsIdentity i5 i5 = refl
pTimesQIsIdentity i5 i6 = refl
pTimesQIsIdentity i5 i7 = refl
pTimesQIsIdentity i5 i8 = refl
pTimesQIsIdentity i6 i0 = refl
pTimesQIsIdentity i6 i1 = refl
pTimesQIsIdentity i6 i2 = refl
pTimesQIsIdentity i6 i3 = refl
pTimesQIsIdentity i6 i4 = refl
pTimesQIsIdentity i6 i5 = refl
pTimesQIsIdentity i6 i6 = refl
pTimesQIsIdentity i6 i7 = refl
pTimesQIsIdentity i6 i8 = refl
pTimesQIsIdentity i7 i0 = refl
pTimesQIsIdentity i7 i1 = refl
pTimesQIsIdentity i7 i2 = refl
pTimesQIsIdentity i7 i3 = refl
pTimesQIsIdentity i7 i4 = refl
pTimesQIsIdentity i7 i5 = refl
pTimesQIsIdentity i7 i6 = refl
pTimesQIsIdentity i7 i7 = refl
pTimesQIsIdentity i7 i8 = refl
pTimesQIsIdentity i8 i0 = refl
pTimesQIsIdentity i8 i1 = refl
pTimesQIsIdentity i8 i2 = refl
pTimesQIsIdentity i8 i3 = refl
pTimesQIsIdentity i8 i4 = refl
pTimesQIsIdentity i8 i5 = refl
pTimesQIsIdentity i8 i6 = refl
pTimesQIsIdentity i8 i7 = refl
pTimesQIsIdentity i8 i8 = refl

qTimesPIsIdentity : (row column : Ix9) →
  matrixMul inverseMatrixQ basisMatrixP row column ≡ identity9 row column
qTimesPIsIdentity i0 i0 = refl
qTimesPIsIdentity i0 i1 = refl
qTimesPIsIdentity i0 i2 = refl
qTimesPIsIdentity i0 i3 = refl
qTimesPIsIdentity i0 i4 = refl
qTimesPIsIdentity i0 i5 = refl
qTimesPIsIdentity i0 i6 = refl
qTimesPIsIdentity i0 i7 = refl
qTimesPIsIdentity i0 i8 = refl
qTimesPIsIdentity i1 i0 = refl
qTimesPIsIdentity i1 i1 = refl
qTimesPIsIdentity i1 i2 = refl
qTimesPIsIdentity i1 i3 = refl
qTimesPIsIdentity i1 i4 = refl
qTimesPIsIdentity i1 i5 = refl
qTimesPIsIdentity i1 i6 = refl
qTimesPIsIdentity i1 i7 = refl
qTimesPIsIdentity i1 i8 = refl
qTimesPIsIdentity i2 i0 = refl
qTimesPIsIdentity i2 i1 = refl
qTimesPIsIdentity i2 i2 = refl
qTimesPIsIdentity i2 i3 = refl
qTimesPIsIdentity i2 i4 = refl
qTimesPIsIdentity i2 i5 = refl
qTimesPIsIdentity i2 i6 = refl
qTimesPIsIdentity i2 i7 = refl
qTimesPIsIdentity i2 i8 = refl
qTimesPIsIdentity i3 i0 = refl
qTimesPIsIdentity i3 i1 = refl
qTimesPIsIdentity i3 i2 = refl
qTimesPIsIdentity i3 i3 = refl
qTimesPIsIdentity i3 i4 = refl
qTimesPIsIdentity i3 i5 = refl
qTimesPIsIdentity i3 i6 = refl
qTimesPIsIdentity i3 i7 = refl
qTimesPIsIdentity i3 i8 = refl
qTimesPIsIdentity i4 i0 = refl
qTimesPIsIdentity i4 i1 = refl
qTimesPIsIdentity i4 i2 = refl
qTimesPIsIdentity i4 i3 = refl
qTimesPIsIdentity i4 i4 = refl
qTimesPIsIdentity i4 i5 = refl
qTimesPIsIdentity i4 i6 = refl
qTimesPIsIdentity i4 i7 = refl
qTimesPIsIdentity i4 i8 = refl
qTimesPIsIdentity i5 i0 = refl
qTimesPIsIdentity i5 i1 = refl
qTimesPIsIdentity i5 i2 = refl
qTimesPIsIdentity i5 i3 = refl
qTimesPIsIdentity i5 i4 = refl
qTimesPIsIdentity i5 i5 = refl
qTimesPIsIdentity i5 i6 = refl
qTimesPIsIdentity i5 i7 = refl
qTimesPIsIdentity i5 i8 = refl
qTimesPIsIdentity i6 i0 = refl
qTimesPIsIdentity i6 i1 = refl
qTimesPIsIdentity i6 i2 = refl
qTimesPIsIdentity i6 i3 = refl
qTimesPIsIdentity i6 i4 = refl
qTimesPIsIdentity i6 i5 = refl
qTimesPIsIdentity i6 i6 = refl
qTimesPIsIdentity i6 i7 = refl
qTimesPIsIdentity i6 i8 = refl
qTimesPIsIdentity i7 i0 = refl
qTimesPIsIdentity i7 i1 = refl
qTimesPIsIdentity i7 i2 = refl
qTimesPIsIdentity i7 i3 = refl
qTimesPIsIdentity i7 i4 = refl
qTimesPIsIdentity i7 i5 = refl
qTimesPIsIdentity i7 i6 = refl
qTimesPIsIdentity i7 i7 = refl
qTimesPIsIdentity i7 i8 = refl
qTimesPIsIdentity i8 i0 = refl
qTimesPIsIdentity i8 i1 = refl
qTimesPIsIdentity i8 i2 = refl
qTimesPIsIdentity i8 i3 = refl
qTimesPIsIdentity i8 i4 = refl
qTimesPIsIdentity i8 i5 = refl
qTimesPIsIdentity i8 i6 = refl
qTimesPIsIdentity i8 i7 = refl
qTimesPIsIdentity i8 i8 = refl

columnFace : Matrix9 → Ix9 → Cube.Face9
columnFace matrix column = Fine.phaseFineTable9
  (matrix i0 column) (matrix i1 column) (matrix i2 column)
  (matrix i3 column) (matrix i4 column) (matrix i5 column)
  (matrix i6 column) (matrix i7 column) (matrix i8 column)

columnA0 : columnFace basisMatrixP i0 ≡ Jordan.chainA0
columnA0 = refl
columnA1 : columnFace basisMatrixP i1 ≡ Jordan.chainA1
columnA1 = refl
columnA2 : columnFace basisMatrixP i2 ≡ Jordan.chainA2
columnA2 = refl
columnB0 : columnFace basisMatrixP i3 ≡ Jordan.chainB0
columnB0 = refl
columnB1 : columnFace basisMatrixP i4 ≡ Jordan.chainB1
columnB1 = refl
columnB2 : columnFace basisMatrixP i5 ≡ Jordan.chainB2
columnB2 = refl
columnC0 : columnFace basisMatrixP i6 ≡ Jordan.chainC0
columnC0 = refl
columnC1 : columnFace basisMatrixP i7 ≡ Jordan.chainC1
columnC1 = refl
columnC2 : columnFace basisMatrixP i8 ≡ Jordan.chainC2
columnC2 = refl

record ConcreteJordanBasisMatrixWitness : Set where
  constructor concrete-jordan-basis-matrix-witness
  field
    basisMatrix : Matrix9
    inverseMatrix : Matrix9
    leftInverse : (row column : Ix9) →
      matrixMul basisMatrix inverseMatrix row column ≡ identity9 row column
    rightInverse : (row column : Ix9) →
      matrixMul inverseMatrix basisMatrix row column ≡ identity9 row column
    a0Column : columnFace basisMatrix i0 ≡ Jordan.chainA0
    a1Column : columnFace basisMatrix i1 ≡ Jordan.chainA1
    a2Column : columnFace basisMatrix i2 ≡ Jordan.chainA2
    b0Column : columnFace basisMatrix i3 ≡ Jordan.chainB0
    b1Column : columnFace basisMatrix i4 ≡ Jordan.chainB1
    b2Column : columnFace basisMatrix i5 ≡ Jordan.chainB2
    c0Column : columnFace basisMatrix i6 ≡ Jordan.chainC0
    c1Column : columnFace basisMatrix i7 ≡ Jordan.chainC1
    c2Column : columnFace basisMatrix i8 ≡ Jordan.chainC2

canonicalConcreteJordanBasisMatrixWitness : ConcreteJordanBasisMatrixWitness
canonicalConcreteJordanBasisMatrixWitness =
  concrete-jordan-basis-matrix-witness
    basisMatrixP inverseMatrixQ
    pTimesQIsIdentity qTimesPIsIdentity
    columnA0 columnA1 columnA2
    columnB0 columnB1 columnB2
    columnC0 columnC1 columnC2
