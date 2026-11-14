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
