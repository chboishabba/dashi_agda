module DASHI.Moonshine.AbelBishopLogQuadraticTrueNormFiniteMajorantExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG: SHARP TRUE-DISPLACEMENT FINITE NORM MAJORANT.
--
-- Consume the existing SAME-SOURCE quadratic coefficient norm-square
-- estimate and the NEW original complex triangle, both derived
-- from arithmetic, not independently postulated triangle axioms.
--
-- With r = sqrt(N(w)) in the EXISTING Balaban R4 square-root
-- calculus, every original shifted logarithm term satisfies
--
--   ||a_(n+1)(w)|| <= (1/2) r^(n+2).
--
-- Consequently, EVERY genuine finite shifted-log partial sum obeys
--
--   ||sum_{k<n} a_(k+1)(w)||
--     <= sum_{k<n} (1/2) r^(k+2).
--
-- Crucially r is the ACTUAL original |w|, not the earlier disk-radius
-- envelope. This makes the triangle/source-coefficient combination
-- finite and exact. The R4 BishopSquareRootCalculus is an EXISTING
-- explicit input and remains UNINHABITED on this branch. Similarly,
-- the finite geometric majorant and Bishop-limit order comparison
-- are NOT silently assumed as results of these finite estimates.
--
-- Source-written only; pinned Agda 2.9 elaboration pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as R4
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact as Half
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticSourceNormFactorExact as Source
import DASHI.Analysis.BishopComplexNormTriangleFromR4Exact as Triangle

-- The canonical original Bishop complex has its own honest Euclidean
-- norm once the already-defined scalar root calculus is inhabited.
trueBishopRadius :
  R4.BishopSquareRootCalculus →
  Complex.BishopComplex → BishopReal.ℝ
trueBishopRadius = Triangle.originalBishopComplexNorm

-- The norm of w is an EXACT radius for the original setoid norm
-- square, hence a closed-disk radius, without replacing it by 2/27.
originalBishopOwnNormDisk :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  Upper.BishopComplexNormSquareUpperRadius
    w (trueBishopRadius roots w)
originalBishopOwnNormDisk roots w =
  let
    nonnegative = Upper.normSquareNonnegative w
  in record
    { Upper.radiusNonnegative =
        R4.rootNonnegative roots (Norm.normSqC w) nonnegative
    ; Upper.normSqBelowRadiusSquare =
        BishopP.≤-respʳ-≃
          (BishopP.≃-symm
            (R4.rootSquare roots (Norm.normSqC w) nonnegative))
          BishopP.≤-refl
    }

-- Literal real ring algebra used to compare norm squares with the
-- square of the product majorant. No extra square-root rule.
bishopSquareProductAgreement :
  ∀ left right →
  BishopReal._≃_
    (BishopReal._*_
      (Norm.square left) (Norm.square right))
    (Norm.square (BishopReal._*_ left right))
bishopSquareProductAgreement left right =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ x y →
      ((x ⊗ x) ⊗ (y ⊗ y))
        ⊜ ((x ⊗ y) ⊗ (x ⊗ y)))
    BishopP.≃-refl left right

-- The exact source norm square is controlled by the square of
-- (1/2) times the TRUE original norm power, not the disk radius.
originalBishopShiftedTermTrueNormSquareUpper :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w n →
  BishopReal._≤_
    (Norm.normSqC (Source.originalBishopQuadraticSourceTerm w n))
    (Norm.square
      (BishopReal._*_ Half.bishopHalf
        (BishopReal.pow (trueBishopRadius roots w)
          (suc (suc n)))))
originalBishopShiftedTermTrueNormSquareUpper roots w n =
  let
    exponent = suc (suc n)
    radius = trueBishopRadius roots w
    power = BishopReal.pow radius exponent
    powerNormUpper :
      BishopReal._≤_
        (BishopReal.pow (Norm.normSqC w) exponent)
        (Norm.square power)
    powerNormUpper =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (Norm.normSqPower w exponent))
        (Upper.normSquarePowerUpper
          (originalBishopOwnNormDisk roots w) exponent)
  in
  BishopP.≤-respʳ-≃
    (bishopSquareProductAgreement Half.bishopHalf power)
    (BishopP.≤-trans
      (Source.originalBishopQuadraticSourceNormSquareUpper w n)
      (BishopP.*-monoˡ-≤-nonNeg
        powerNormUpper
        (SquareNN.bishopSquareNonnegative Half.bishopHalf)))

-- Take the square root by monotonicity and use positivity to
-- simplify sqrt((half*r^n)^2) to half*r^n.
originalBishopShiftedTermTrueNormUpper :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w n →
  BishopReal._≤_
    (trueBishopRadius roots
      (Source.originalBishopQuadraticSourceTerm w n))
    (BishopReal._*_ Half.bishopHalf
      (BishopReal.pow (trueBishopRadius roots w)
        (suc (suc n))))
originalBishopShiftedTermTrueNormUpper roots w n =
  let
    exponent = suc (suc n)
    radius = trueBishopRadius roots w
    power = BishopReal.pow radius exponent
    bound = BishopReal._*_ Half.bishopHalf power
    boundNonnegative =
      BishopP.nonNegx,y⇒nonNegx*y
        Half.bishopHalfNonnegative
        (BishopSequence.nonNegx⇒nonNegxⁿ exponent
          (Upper.radiusNonnegative
            (originalBishopOwnNormDisk roots w)))
    rooted =
      R4.rootMonotone roots
        (Upper.normSquareNonnegative
          (Source.originalBishopQuadraticSourceTerm w n))
        (originalBishopShiftedTermTrueNormSquareUpper
          roots w n)
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-trans
      (R4.rootOfSquare roots bound)
      (BishopP.nonNegx⇒∣x∣≃x boundNonnegative))
    rooted

-- Exact original finite geometric majorant: first n SHIFTED terms,
-- with each exponent n+2 and the literal HALF coefficient.
trueBishopQuadraticFiniteMajorant :
  (roots : R4.BishopSquareRootCalculus) →
  Complex.BishopComplex → Nat → BishopReal.ℝ
trueBishopQuadraticFiniteMajorant roots w n =
  BishopSequence.SeriesOf
    (λ k →
      BishopReal._*_ Half.bishopHalf
        (BishopReal.pow (trueBishopRadius roots w)
          (suc (suc k))))
    n

-- n=0 has the genuine zero partial sum in both complex components.
originalBishopQuadraticZeroPrefixNormIsZero :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  BishopReal._≃_
    (trueBishopRadius roots
      (Finite.originalBishopLogQuadraticTailPrefix w zero))
    BishopReal.0ℝ
originalBishopQuadraticZeroPrefixNormIsZero roots w =
  let
    zeroSquare :
      BishopReal._≃_
        (Norm.normSqC
          (Finite.originalBishopLogQuadraticTailPrefix w zero))
        (Norm.square BishopReal.0ℝ)
    zeroSquare =
      let open BishopP.ℝ-Solver
      in solve 0
        (((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ)) ⊕
          ((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ))
          ⊜ ((Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ)))
        BishopP.≃-refl
    zeroNonnegative =
      BishopP.0≤x⇒nonNegx
        (BishopP.≤-refl {a = BishopReal.0ℝ})
  in
  BishopP.≃-trans
    (R4.rootCongruent roots zeroSquare)
    (BishopP.≃-trans
      (R4.rootOfSquare roots BishopReal.0ℝ)
      (BishopP.nonNegx⇒∣x∣≃x zeroNonnegative))

-- True finite scalar majorant by induction, using exactly the
-- one-step original shifted-source complex Minkowski theorem.
originalBishopQuadraticFiniteTrueNormBound :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w n →
  BishopReal._≤_
    (trueBishopRadius roots
      (Finite.originalBishopLogQuadraticTailPrefix w n))
    (trueBishopQuadraticFiniteMajorant roots w n)
originalBishopQuadraticFiniteTrueNormBound roots w zero =
  BishopP.≤-respˡ-≃
    (originalBishopQuadraticZeroPrefixNormIsZero roots w)
    BishopP.≤-refl
originalBishopQuadraticFiniteTrueNormBound roots w (suc n) =
  BishopP.≤-trans
    (Triangle.originalBishopQuadraticTailPrefixNormStep roots w n)
    (BishopP.+-mono-≤
      (originalBishopQuadraticFiniteTrueNormBound roots w n)
      (originalBishopShiftedTermTrueNormUpper roots w n))
