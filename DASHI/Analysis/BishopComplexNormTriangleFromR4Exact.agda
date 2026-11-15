module DASHI.Analysis.BishopComplexNormTriangleFromR4Exact where

------------------------------------------------------------------------
-- FINITE BISHOP COMPLEX EUCLIDEAN TRIANGLE VIA EXISTING R4 MINKOWSKI.
--
-- Native source carriers: the exact BishopComplex pair of vendored
-- Bishop.ℝ, BishopComplexAlgebraExact._+C_, original normSqC, and
-- the existing PROVED Balaban P33 four-vector Cauchy/Minkowski
-- derivation. Only its previously explicit BishopSquareRootCalculus
-- input remains a parameter: there is NO assumed triangle field.
--
-- Consequence: the literal shifted log prefix satisfies the genuine
-- one-step Euclidean NORM triangle, not two independent component
-- envelopes. This avoids a false sqrt(2) loss in P1.L.
--
-- Pending: actual inhabitant of BishopSquareRootCalculus, term
-- majorant in the same norm, finite geometric comparison, and
-- order-preserving limit of the original Bishop series. No claim
-- that this constructs a square root or the 8/27 analytic bound.
-- Local Agda 2.9 kernel admission pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as R4
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticSourceNormFactorExact as Source

-- Faithful embedding into the first two REAL coordinates of the
-- pre-existing four-dimensional Euclidean square norm.
embedOriginalComplexR4 : Complex.BishopComplex → R4.Vec4B
embedOriginalComplexR4 (Complex.complex a b) =
  R4.vec4B a b BishopReal.0ℝ BishopReal.0ℝ

-- This is the literal original norm, not an independently chosen
-- Euclidean or sup-norm surrogate.
originalBishopComplexNorm :
  R4.BishopSquareRootCalculus → Complex.BishopComplex → BishopReal.ℝ
originalBishopComplexNorm roots z = R4.root roots (Norm.normSqC z)

-- The two unused R4 coordinates disappear by the original Bishop
-- polynomial ring solver. No extraneous sqrt or quotient oracle.
embeddedNormSquareIsOriginal :
  ∀ z →
  BishopReal._≃_
    (R4.normSq4 (embedOriginalComplexR4 z))
    (Norm.normSqC z)
embeddedNormSquareIsOriginal (Complex.complex a b) =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ a b →
      ((a ⊗ a) ⊕
        ((b ⊗ b) ⊕
          (((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ)) ⊕
            ((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ)))))
      ⊜
      ((a ⊗ a) ⊕ (b ⊗ b)))
    BishopP.≃-refl a b

-- The original complex addition embeds into R4 addition up to
-- BISHOP SETOID equality (the last two R4 coordinates are 0+0).
embeddedOriginalAdditionNormSquare :
  ∀ x y →
  BishopReal._≃_
    (R4.normSq4
      (embedOriginalComplexR4 (Algebra._+C_ x y)))
    (R4.normSq4
      (R4.add4 (embedOriginalComplexR4 x)
               (embedOriginalComplexR4 y)))
embeddedOriginalAdditionNormSquare
    (Complex.complex a b) (Complex.complex c d) =
  let open BishopP.ℝ-Solver
  in solve 4
    (λ a b c d →
      (((a ⊕ c) ⊗ (a ⊕ c)) ⊕
        (((b ⊕ d) ⊗ (b ⊕ d)) ⊕
          (((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ)) ⊕
            ((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ)))))
      ⊜
      (((a ⊕ c) ⊗ (a ⊕ c)) ⊕
        (((b ⊕ d) ⊗ (b ⊕ d)) ⊕
          ((((Κ 0ℚᵘ) ⊕ (Κ 0ℚᵘ)) ⊗
             ((Κ 0ℚᵘ) ⊕ (Κ 0ℚᵘ))) ⊕
            (((Κ 0ℚᵘ) ⊕ (Κ 0ℚᵘ)) ⊗
             ((Κ 0ℚᵘ) ⊕ (Κ 0ℚᵘ)))))))
    BishopP.≃-refl a b c d

-- Actual original Bishop Cauchy/Minkowski, DERIVED from the existing
-- R4 theorem rather than assumed for arbitrary complex pairs.
originalBishopComplexNormTriangle :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ x y →
  BishopReal._≤_
    (originalBishopComplexNorm roots (Algebra._+C_ x y))
    (BishopReal._+_
      (originalBishopComplexNorm roots x)
      (originalBishopComplexNorm roots y))
originalBishopComplexNormTriangle roots x y =
  let
    leftIsEmbedded =
      R4.rootCongruent roots
        (BishopP.≃-symm
          (embeddedNormSquareIsOriginal
            (Algebra._+C_ x y)))
    embeddedAddition =
      R4.rootCongruent roots
        (embeddedOriginalAdditionNormSquare x y)
    leftEqualsR4 =
      BishopP.≃-trans leftIsEmbedded embeddedAddition
    rightEqualsOriginal =
      BishopP.+-cong
        (R4.rootCongruent roots (embeddedNormSquareIsOriginal x))
        (R4.rootCongruent roots (embeddedNormSquareIsOriginal y))
  in
  BishopP.≤-respʳ-≃
    rightEqualsOriginal
    (BishopP.≤-respˡ-≃
      leftEqualsR4
      (R4.norm4Triangle roots
        (embedOriginalComplexR4 x)
        (embedOriginalComplexR4 y)))

-- Norm congruence for the actual componentwise Bishop COMPLEX setoid.
originalBishopNormSquareCongruent :
  ∀ {x y} →
  Complex._≈C_ x y →
  BishopReal._≃_ (Norm.normSqC x) (Norm.normSqC y)
originalBishopNormSquareCongruent
    {Complex.complex a b} {Complex.complex c d}
    (a≈c , b≈d) =
  BishopP.+-cong
    (BishopP.*-cong a≈c a≈c)
    (BishopP.*-cong b≈d b≈d)

originalBishopComplexNormCongruent :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {x y} →
  Complex._≈C_ x y →
  BishopReal._≃_
    (originalBishopComplexNorm roots x)
    (originalBishopComplexNorm roots y)
originalBishopComplexNormCongruent roots same =
  R4.rootCongruent roots (originalBishopNormSquareCongruent same)

-- This is a property of the actual original shifted-log partial
-- sums, not a synthetic sequence of norm estimates. The scalar
-- SeriesOf recursion literally adds the next genuine source term.
originalBishopQuadraticTailPrefixSuccessor :
  ∀ w n →
  Complex._≈C_
    (Finite.originalBishopLogQuadraticTailPrefix w (suc n))
    (Algebra._+C_
      (Finite.originalBishopLogQuadraticTailPrefix w n)
      (Source.originalBishopQuadraticSourceTerm w n))
originalBishopQuadraticTailPrefixSuccessor w n =
  BishopP.≃-refl , BishopP.≃-refl

-- The missing finite complex-triangle producer of the original
-- P1.L source: controls each NEXT shifted-log partial sum by the
-- previous partial-sum norm plus the TRUE original term norm.
originalBishopQuadraticTailPrefixNormStep :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w n →
  BishopReal._≤_
    (originalBishopComplexNorm roots
      (Finite.originalBishopLogQuadraticTailPrefix w (suc n)))
    (BishopReal._+_
      (originalBishopComplexNorm roots
        (Finite.originalBishopLogQuadraticTailPrefix w n))
      (originalBishopComplexNorm roots
        (Source.originalBishopQuadraticSourceTerm w n)))
originalBishopQuadraticTailPrefixNormStep roots w n =
  BishopP.≤-respˡ-≃
    (originalBishopComplexNormCongruent roots
      (originalBishopQuadraticTailPrefixSuccessor w n))
    (originalBishopComplexNormTriangle roots
      (Finite.originalBishopLogQuadraticTailPrefix w n)
      (Source.originalBishopQuadraticSourceTerm w n))
