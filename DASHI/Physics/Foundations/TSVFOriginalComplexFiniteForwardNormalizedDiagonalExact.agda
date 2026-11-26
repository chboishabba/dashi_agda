{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalComplexFiniteForwardNormalizedDiagonalExact where

------------------------------------------------------------------------
-- HIL01 concrete original physical-complex STATE positive sector.
--
-- This file does NOT assume an abstract normalized Ket. It consumes
-- the existing ACTUAL finiteComplexQuantum and finiteComplexEnsemble
-- from TSVF2017OriginalComplexABLSelectedExact. For every selected
-- gamma/environment input the original forward Ket is (1,1), whose
-- Hermitian self-pair is EXACTLY 2, not 1.
--
-- The actual original complex source can nevertheless define a
-- normalized faithful state on its selected real-diagonal operator
-- subalgebra, omega(diag(a,b))=(a+b)/2. The proof obtains that
-- formula from Q.forwardState, Q.QuantumSurface.apply/pair and the
-- ORIGINAL complex Hermitian product, not a second invented state.
--
-- It then proves omega(I)=1, complex diagonal norm equality and
-- positivity omega(A* A)>=0 for ALL diagonal operators from
-- rational square nonnegativity, plus actual source multiplication.
--
-- This is a finite noncommutative-source COMMUTATIVE subalgebra,
-- not a full infinite-dimensional complex C*-state, GNS or OS.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym; subst)

import DASHI.Quantum.TSVF as Q
import DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact as Original
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as Env
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact
  as C
import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order


-- This is the real diagonal subalgebra of the original selected
-- finite complex 2D Hilbert carrier. It includes identity and
-- both projectors and has actual complex-coordinate action.
RealDiagonal : Set
RealDiagonal = ℚ × ℚ

diagIdentity : RealDiagonal
diagIdentity = 1ℚ , 1ℚ

diagProduct : RealDiagonal → RealDiagonal → RealDiagonal
diagProduct (a , b) (c , d) = (a * c) , (b * d)

diagStar : RealDiagonal → RealDiagonal
diagStar a = a

actualOriginalComplexDiagonalOperator :
  RealDiagonal →
  Q.QuantumSurface.Operator Original.finiteComplexQuantum
actualOriginalComplexDiagonalOperator (a , b)
    (Env.pointerRecord x y) =
  Env.pointerRecord
    (C._*c_ (C.complex a 0ℚ) x)
    (C._*c_ (C.complex b 0ℚ) y)

-- The source-selected diagonal operators have actual identity,
-- composition and Hermitian-adjoint action, not merely an abstract
-- positive quadratic polynomial. This makes the finite original
-- observer's selected real *-subalgebra executable in complex coords.
actualOriginalDiagonalIdentityActs :
  ∀ ket →
  actualOriginalComplexDiagonalOperator diagIdentity ket ≡ ket
actualOriginalDiagonalIdentityActs
    (Env.pointerRecord (C.complex x y) (C.complex z w)) =
  cong₂ Env.pointerRecord
    (C.complexExt
      (solve (x ∷ y ∷ []))
      (solve (x ∷ y ∷ [])))
    (C.complexExt
      (solve (z ∷ w ∷ []))
      (solve (z ∷ w ∷ [])))

actualOriginalDiagonalComposition :
  ∀ left right ket →
  actualOriginalComplexDiagonalOperator (diagProduct left right) ket
  ≡
  actualOriginalComplexDiagonalOperator left
    (actualOriginalComplexDiagonalOperator right ket)
actualOriginalDiagonalComposition
    (a , b) (c , d)
    (Env.pointerRecord (C.complex x y) (C.complex z w)) =
  cong₂ Env.pointerRecord
    (C.complexExt
      (solve (a ∷ c ∷ x ∷ y ∷ []))
      (solve (a ∷ c ∷ x ∷ y ∷ [])))
    (C.complexExt
      (solve (b ∷ d ∷ z ∷ w ∷ []))
      (solve (b ∷ d ∷ z ∷ w ∷ [])))

-- The source's ACTUAL Hermitian pair, so its physical star is not
-- a new arbitrary operator-adjoint record on this real subalgebra.
actualOriginalDiagonalHermitianAdjoint :
  ∀ diagonal left right →
  Env.hermitianPair
    (actualOriginalComplexDiagonalOperator diagonal left) right
  ≡
  Env.hermitianPair left
    (actualOriginalComplexDiagonalOperator (diagStar diagonal) right)
actualOriginalDiagonalHermitianAdjoint
    (a , b)
    (Env.pointerRecord (C.complex x y) (C.complex z w))
    (Env.pointerRecord (C.complex p q) (C.complex r s)) =
  C.complexExt
    (solve (a ∷ b ∷ x ∷ y ∷ z ∷ w ∷ p ∷ q ∷ r ∷ s ∷ []))
    (solve (a ∷ b ∷ x ∷ y ∷ z ∷ w ∷ p ∷ q ∷ r ∷ s ∷ []))

-- The SAME original Q.TSVF selected forward state, for every
-- admissible gamma/environment choice and k.
module _
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord)
  (k : Nat)
  where

  originalSelectedEnsemble :
    Q.TSVFEnsemble Original.finiteComplexQuantum
  originalSelectedEnsemble =
    Original.finiteComplexEnsemble
      rightGammas wrongGammas right wrong k

  originalComplexForwardKet : Env.ComplexPointerRecord
  originalComplexForwardKet = Q.forwardState originalSelectedEnsemble

  originalSelectedForwardKetIsOneOne :
    originalComplexForwardKet
    ≡ Env.pointerRecord C.oneC C.oneC
  originalSelectedForwardKetIsOneOne = refl

  originalComplexForwardSelfPair :
    C.RationalComplex
  originalComplexForwardSelfPair =
    Q.QuantumSurface.pair Original.finiteComplexQuantum
      originalComplexForwardKet originalComplexForwardKet

  -- An actual source normalization correction: ||(1,1)||^2=2.
  -- This refutes silently applying an omega(I)=1 record with the
  -- UNnormalized original chosen forward ket.
  originalComplexForwardNormIsTwo :
    originalComplexForwardSelfPair
      ≡ C.complex (1ℚ + 1ℚ) 0ℚ
  originalComplexForwardNormIsTwo =
    C.complexExt (solve []) (solve [])

  originalSourceComplexDiagonalAmplitude :
    RealDiagonal → C.RationalComplex
  originalSourceComplexDiagonalAmplitude diagonal =
    Q.QuantumSurface.pair Original.finiteComplexQuantum
      originalComplexForwardKet
      (Q.QuantumSurface.apply Original.finiteComplexQuantum
        (actualOriginalComplexDiagonalOperator diagonal)
        originalComplexForwardKet)

  -- Genuine Hermitian pair from the original Q, NOT an arbitrary
  -- diagonal expectation carrier and NOT an ABL postselected state.
  originalDiagonalAmplitudeIsRealTrace :
    (a b : ℚ) →
    originalSourceComplexDiagonalAmplitude (a , b)
      ≡ C.complex (a + b) 0ℚ
  originalDiagonalAmplitudeIsRealTrace a b =
    C.complexExt
      (solve (a ∷ b ∷ []))
      (solve (a ∷ b ∷ []))

  originalNormalizedDiagonalState : RealDiagonal → ℚ
  originalNormalizedDiagonalState diagonal =
    ½ * C.re (originalSourceComplexDiagonalAmplitude diagonal)

  originalNormalizedDiagonalIsHalfTrace :
    ∀ a b →
    originalNormalizedDiagonalState (a , b)
      ≡ ½ * (a + b)
  originalNormalizedDiagonalIsHalfTrace a b =
    cong (λ value → ½ * value)
      (cong C.re (originalDiagonalAmplitudeIsRealTrace a b))

  originalNormalizedDiagonalUnit :
    originalNormalizedDiagonalState diagIdentity ≡ 1ℚ
  originalNormalizedDiagonalUnit =
    trans
      (originalNormalizedDiagonalIsHalfTrace 1ℚ 1ℚ)
      (solve [])

  originalDiagonalStarSquare : RealDiagonal → RealDiagonal
  originalDiagonalStarSquare diagonal =
    diagProduct (diagStar diagonal) diagonal

  originalDiagonalStarSquareIsPointwiseSquare :
    ∀ a b →
    originalDiagonalStarSquare (a , b)
      ≡ (a * a) , (b * b)
  originalDiagonalStarSquareIsPointwiseSquare a b = refl

  originalDiagonalStarSquareNormalized :
    ∀ a b →
    originalNormalizedDiagonalState
      (originalDiagonalStarSquare (a , b))
    ≡ ½ * ((a * a) + (b * b))
  originalDiagonalStarSquareNormalized a b =
    originalNormalizedDiagonalIsHalfTrace (a * a) (b * b)

  -- Physical finite positivity has a FULL ℚ ORDER certificate,
  -- not merely the opaque QuantumSurface.Positive Weight predicate.
  originalDiagonalStarSquarePositive :
    ∀ a b →
    0ℚ ≤ originalNormalizedDiagonalState
      (originalDiagonalStarSquare (a , b))
  originalDiagonalStarSquarePositive a b =
    subst
      (λ value → 0ℚ ≤ value)
      (sym (originalDiagonalStarSquareNormalized a b))
      halfTimesSquaresPositive
    where
      sumNonnegative :
        0ℚ ≤ ((a * a) + (b * b))
      sumNonnegative =
        Order.addNonnegative
          (Order.squareNonnegative a)
          (Order.squareNonnegative b)

      halfNonnegative : 0ℚ ≤ ½
      halfNonnegative = ℚP.0≤∣p∣ ½

      instance
        halfNN : NonNegative ½
        halfNN = nonNegative halfNonnegative

        sumNN : NonNegative ((a * a) + (b * b))
        sumNN = nonNegative sumNonnegative

        productNN : NonNegative
          (½ * ((a * a) + (b * b)))
        productNN = ℚP.nonNeg*nonNeg⇒nonNeg
          ½ ((a * a) + (b * b))

      halfTimesSquaresPositive :
        0ℚ ≤ ½ * ((a * a) + (b * b))
      halfTimesSquaresPositive =
        ℚP.nonNegative⁻¹
          (½ * ((a * a) + (b * b)))

-- Original complex finite forward state has norm 2. An infinite
-- observer reconstruction must normalize or divide by Z, build the
-- complete noncommutative star algebra and its positive GNS null
-- ideal, then match the actual independent YM OS (not this subalgebra).


------------------------------------------------------------------------
-- AW1: full rational-complex LINEAR matrix action on the original
-- pointer carrier. Reuses the original quantum apply/pair; does not
-- claim every function Operator is linear, or identify the ABL
-- denominator predicate with nonnegative Hilbert squared norm.
------------------------------------------------------------------------
record Matrix2C : Set where
  constructor matrix2
  field
    aa ab ba bb : C.RationalComplex

matrixAction : Matrix2C → Q.QuantumSurface.Operator Original.finiteComplexQuantum
matrixAction (matrix2 a b c d) (Env.pointerRecord x y) =
  Env.pointerRecord (C._+c_ (C._*c_ a x) (C._*c_ b y))
                    (C._+c_ (C._*c_ c x) (C._*c_ d y))

matrixProduct : Matrix2C → Matrix2C → Matrix2C
matrixProduct (matrix2 a b c d) (matrix2 e f g h) =
  matrix2 (C._+c_ (C._*c_ a e) (C._*c_ b g))
          (C._+c_ (C._*c_ a f) (C._*c_ b h))
          (C._+c_ (C._*c_ c e) (C._*c_ d g))
          (C._+c_ (C._*c_ c f) (C._*c_ d h))

matrixAdjoint : Matrix2C → Matrix2C
matrixAdjoint (matrix2 a b c d) =
  matrix2 (C.conjugateC a) (C.conjugateC c)
          (C.conjugateC b) (C.conjugateC d)

matrixIdentity : Matrix2C
matrixIdentity = matrix2 C.oneC C.zeroC C.zeroC C.oneC

matrixIdentityActs : ∀ ket → matrixAction matrixIdentity ket ≡ ket
matrixIdentityActs (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) =
  cong₂ Env.pointerRecord
    (C.complexExt (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))
    (C.complexExt (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))

matrixProductActs : ∀ a b ket →
  matrixAction (matrixProduct a b) ket ≡ matrixAction a (matrixAction b ket)
matrixProductActs (matrix2 (C.complex a0 a1) (C.complex a2 a3) (C.complex a4 a5) (C.complex a6 a7)) (matrix2 (C.complex b0 b1) (C.complex b2 b3) (C.complex b4 b5) (C.complex b6 b7)) (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) =
  cong₂ Env.pointerRecord
    (C.complexExt (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))
    (C.complexExt (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))

matrixAdjointPair : ∀ a left right →
  Env.hermitianPair (matrixAction a left) right
  ≡ Env.hermitianPair left (matrixAction (matrixAdjoint a) right)
matrixAdjointPair (matrix2 (C.complex a0 a1) (C.complex a2 a3) (C.complex a4 a5) (C.complex a6 a7)) (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) (Env.pointerRecord (C.complex v0 v1) (C.complex v2 v3)) =
  C.complexExt (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ []))
               (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ []))

-- An explicit cyclic section (not an inverse on the whole matrix
-- algebra). The second column is zero, so the original (1,1) reopens.
matrixCyclicSection : Env.ComplexPointerRecord → Matrix2C
matrixCyclicSection (Env.pointerRecord x y) = matrix2 x C.zeroC y C.zeroC

matrixCyclicSectionReopens : ∀ ket →
  matrixAction (matrixCyclicSection ket) (Env.pointerRecord C.oneC C.oneC) ≡ ket
matrixCyclicSectionReopens (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) =
  cong₂ Env.pointerRecord
    (C.complexExt (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))
    (C.complexExt (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))

module _
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord)
  (k : Nat)
  where

  awForward : Env.ComplexPointerRecord
  awForward = originalComplexForwardKet rightGammas wrongGammas right wrong k

  originalMatrixForwardPair : Matrix2C → C.RationalComplex
  originalMatrixForwardPair a = Q.QuantumSurface.pair Original.finiteComplexQuantum
    awForward (Q.QuantumSurface.apply Original.finiteComplexQuantum (matrixAction a) awForward)

  originalMatrixCyclicGram : ∀ a b →
    originalMatrixForwardPair (matrixProduct (matrixAdjoint a) b)
    ≡ Env.hermitianPair (matrixAction a awForward) (matrixAction b awForward)
  originalMatrixCyclicGram a b =
    trans (cong (Env.hermitianPair awForward)
                (matrixProductActs (matrixAdjoint a) b awForward))
          (sym (matrixAdjointPair a awForward (matrixAction b awForward)))

  originalMatrixCyclicSectionReopens : ∀ ket →
    matrixAction (matrixCyclicSection ket) awForward ≡ ket
  originalMatrixCyclicSectionReopens = matrixCyclicSectionReopens

  -- Exact normalization by the original norm²=2. This is the forward
  -- state, NOT a weak value and NOT an ABL denominator.
  originalNormalizedMatrixState : Matrix2C → C.RationalComplex
  originalNormalizedMatrixState a =
    C._*c_ (C.complex ½ 0ℚ) (originalMatrixForwardPair a)

  originalNormalizedMatrixUnit : originalNormalizedMatrixState matrixIdentity ≡ C.oneC
  originalNormalizedMatrixUnit =
    trans (cong (λ ket → C._*c_ (C.complex ½ 0ℚ) (Env.hermitianPair awForward ket))
                (matrixIdentityActs awForward))
          (C.complexExt (solve []) (solve []))


------------------------------------------------------------------------
-- AX: inhabit the repaired ORIGINAL Hilbert compiler on the selected
-- linear matrix restriction of the actual pointer. The pairing is
-- normalized by the original norm²=2. This is a forward-only Hilbert
-- view; the original ABL QuantumSurface and certificate are unchanged.
------------------------------------------------------------------------
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact as Forward
import DASHI.Physics.Foundations.TSVFOriginalForwardCyclicCrossGramExact as Cyclic
import DASHI.Physics.Foundations.TSVFOriginalForwardCyclicActionQuotientExact as Quotient

matrixAdd : Matrix2C → Matrix2C → Matrix2C
matrixAdd (matrix2 a b c d) (matrix2 e f g h) =
  matrix2 (C._+c_ a e) (C._+c_ b f) (C._+c_ c g) (C._+c_ d h)

matrixScale : C.RationalComplex → Matrix2C → Matrix2C
matrixScale z (matrix2 a b c d) =
  matrix2 (C._*c_ z a) (C._*c_ z b) (C._*c_ z c) (C._*c_ z d)

pointerScale : C.RationalComplex → Env.ComplexPointerRecord → Env.ComplexPointerRecord
pointerScale z (Env.pointerRecord a b) =
  Env.pointerRecord (C._*c_ z a) (C._*c_ z b)

normalizedPair : Env.ComplexPointerRecord → Env.ComplexPointerRecord → C.RationalComplex
normalizedPair u v = C._*c_ (C.complex ½ 0ℚ) (Env.hermitianPair u v)

matrixAddActs : ∀ a b ket →
  matrixAction (matrixAdd a b) ket ≡ Original.pointerAdd (matrixAction a ket) (matrixAction b ket)
matrixAddActs (matrix2 (C.complex a0 a1) (C.complex a2 a3) (C.complex a4 a5) (C.complex a6 a7)) (matrix2 (C.complex b0 b1) (C.complex b2 b3) (C.complex b4 b5) (C.complex b6 b7)) (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) =
  cong₂ Env.pointerRecord
    (C.complexExt (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))
    (C.complexExt (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))

matrixScaleActs : ∀ z a ket →
  matrixAction (matrixScale z a) ket ≡ pointerScale z (matrixAction a ket)
matrixScaleActs (C.complex z0 z1) (matrix2 (C.complex a0 a1) (C.complex a2 a3) (C.complex a4 a5) (C.complex a6 a7)) (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) =
  cong₂ Env.pointerRecord
    (C.complexExt (solve (z0 ∷ z1 ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (z0 ∷ z1 ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))
    (C.complexExt (solve (z0 ∷ z1 ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])) (solve (z0 ∷ z1 ∷ a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ u0 ∷ u1 ∷ u2 ∷ u3 ∷ [])))

normalizedPairRightAdd : ∀ u v w →
  normalizedPair u (Original.pointerAdd v w) ≡ C._+c_ (normalizedPair u v) (normalizedPair u w)
normalizedPairRightAdd (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) (Env.pointerRecord (C.complex v0 v1) (C.complex v2 v3)) (Env.pointerRecord (C.complex w0 w1) (C.complex w2 w3)) =
  C.complexExt (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ w0 ∷ w1 ∷ w2 ∷ w3 ∷ [])) (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ w0 ∷ w1 ∷ w2 ∷ w3 ∷ []))

normalizedPairRightScale : ∀ u z v →
  normalizedPair u (pointerScale z v) ≡ C._*c_ z (normalizedPair u v)
normalizedPairRightScale (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) (C.complex z0 z1) (Env.pointerRecord (C.complex v0 v1) (C.complex v2 v3)) =
  C.complexExt (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ z0 ∷ z1 ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ [])) (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ z0 ∷ z1 ∷ v0 ∷ v1 ∷ v2 ∷ v3 ∷ []))

RealNonnegativeComplex : C.RationalComplex → Set
RealNonnegativeComplex z = (C.im z ≡ 0ℚ) × (0ℚ ≤ C.re z)

normalizedSelfPairNonnegative : ∀ u → RealNonnegativeComplex (normalizedPair u u)
normalizedSelfPairNonnegative (Env.pointerRecord (C.complex u0 u1) (C.complex u2 u3)) =
  solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ []) ,
  subst (λ value → 0ℚ ≤ value) (sym (solve (u0 ∷ u1 ∷ u2 ∷ u3 ∷ []))) halfTimes
  where
  sumSquares : ℚ
  sumSquares = (u0 * u0 + u1 * u1) + (u2 * u2 + u3 * u3)

  sumNNProof : 0ℚ ≤ sumSquares
  sumNNProof = Order.addNonnegative
    (Order.addNonnegative (Order.squareNonnegative u0) (Order.squareNonnegative u1))
    (Order.addNonnegative (Order.squareNonnegative u2) (Order.squareNonnegative u3))

  instance
    halfNN : NonNegative ½
    halfNN = nonNegative (ℚP.0≤∣p∣ ½)
    sumNN : NonNegative sumSquares
    sumNN = nonNegative sumNNProof
    productNN : NonNegative (½ * sumSquares)
    productNN = ℚP.nonNeg*nonNeg⇒nonNeg ½ sumSquares

  halfTimes : 0ℚ ≤ ½ * sumSquares
  halfTimes = ℚP.nonNegative⁻¹ (½ * sumSquares)

matrixHilbertQuantum : Q.QuantumSurface
matrixHilbertQuantum = record
  { Scalar = C.RationalComplex
  ; Weight = Q.QuantumSurface.Weight Original.finiteComplexQuantum
  ; Ket = Env.ComplexPointerRecord
  ; Bra = Env.ComplexPointerRecord
  ; Operator = Matrix2C
  ; Time = Q.QuantumSurface.Time Original.finiteComplexQuantum
  ; evolveKet = Q.QuantumSurface.evolveKet Original.finiteComplexQuantum
  ; evolveBra = Q.QuantumSurface.evolveBra Original.finiteComplexQuantum
  ; apply = matrixAction
  ; pair = normalizedPair
  ; normSquared = Q.QuantumSurface.normSquared Original.finiteComplexQuantum
  ; divideWeight = Q.QuantumSurface.divideWeight Original.finiteComplexQuantum
  ; Positive = Q.QuantumSurface.Positive Original.finiteComplexQuantum
  }

module _
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord)
  (k : Nat)
  where

  private
    original : Q.TSVFEnsemble Original.finiteComplexQuantum
    original = originalSelectedEnsemble rightGammas wrongGammas right wrong k

  matrixHilbertEnsemble : Q.TSVFEnsemble matrixHilbertQuantum
  matrixHilbertEnsemble = Q.prePostSelected
    (Q.initialTime original) (Q.middleTime original) (Q.finalTime original)
    (Q.initialKet original) (Q.finalBra original)

  matrixForwardReopens : Q.forwardState matrixHilbertEnsemble ≡ Q.forwardState original
  matrixForwardReopens = refl

  matrixHilbertLaws : Forward.OriginalPhysicalInnerProductLaws matrixHilbertEnsemble
  matrixHilbertLaws = record
    { braOfKet = λ ket → ket
    ; operatorAdjoint = matrixAdjoint
    ; operatorCompose = matrixProduct
    ; selectedComposition = matrixProductActs
    ; adjointLaw = λ a u v →
        cong (C._*c_ (C.complex ½ 0ℚ)) (sym (matrixAdjointPair a u v))
    ; oneScalar = C.oneC
    ; operatorIdentity = matrixIdentity
    ; identityActs = matrixIdentityActs
    ; originalSelectedNormIsOne = C.complexExt (solve []) (solve [])
    ; operatorAdd = matrixAdd
    ; ketAdd = Original.pointerAdd
    ; scalarAdd = C._+c_
    ; addActs = matrixAddActs
    ; pairRightAdditive = normalizedPairRightAdd
    ; operatorScale = matrixScale
    ; ketScale = pointerScale
    ; scaleActs = matrixScaleActs
    ; scalarMultiply = C._*c_
    ; pairRightHomogeneous = normalizedPairRightScale
    ; HilbertNonnegative = RealNonnegativeComplex
    ; scalarSelfPairNonnegative = normalizedSelfPairNonnegative
    }

  matrixOriginalNormalizedFunctional :
    ∀ a → Forward.originalForwardFunctional matrixHilbertEnsemble matrixHilbertLaws a
      ≡ originalNormalizedMatrixState rightGammas wrongGammas right wrong k a
  matrixOriginalNormalizedFunctional a = refl

  matrixOriginalCyclicNonnegative : ∀ a →
    RealNonnegativeComplex (Cyclic.originalObserverCrossGram matrixHilbertEnsemble matrixHilbertLaws a a)
  matrixOriginalCyclicNonnegative =
    Cyclic.originalAllCyclicDiagonalsNonnegative matrixHilbertEnsemble matrixHilbertLaws


  -- Consume the original quotient theorem rather than prove a second
  -- abstract kernel congruence. The selected matrix action is now an
  -- actual source-written input of that theorem.
  matrixCyclicLeftKernel :
    ∀ left a b →
    matrixAction a (Q.forwardState matrixHilbertEnsemble)
      ≡ matrixAction b (Q.forwardState matrixHilbertEnsemble) →
    matrixAction (matrixProduct left a) (Q.forwardState matrixHilbertEnsemble)
      ≡ matrixAction (matrixProduct left b) (Q.forwardState matrixHilbertEnsemble)
  matrixCyclicLeftKernel =
    Quotient.originalLeftActionPreservesCyclicKernel matrixHilbertEnsemble matrixHilbertLaws

  matrixCyclicImageSection : ∀ ket →
    Cyclic.originalCyclicVector matrixHilbertEnsemble matrixHilbertLaws (matrixCyclicSection ket)
      ≡ ket
  matrixCyclicImageSection = matrixCyclicSectionReopens
