module DASHI.Physics.YangMills.BalabanCMP109BishopKarcherFiveFourthSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", Dalhousie, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Constructive square-root-free core of the fallback Karcher metric bridge.
-- On the whole nonnegative Bishop half-ball, the existing checked estimate
--
--       sin t >= (23/24)t
--
-- is stronger than the requested 4/5 chord lower factor. Since the literal
-- quaternion chord square contains sin(t)^2 as a nonnegative summand,
--
--       (16/25)t^2 <= chord(exp X,1)^2.
--
-- The rational margin is large:
--
--       (23/24)^2 - (4/5)^2 = 4009/14400 > 0.
--
-- Thus the only remaining step from this theorem to
--       d_geo(I,U) <= (5/4) d_ch(I,U)
-- is transport through the repository's scalar square-root metric backend;
-- no further trigonometric estimate is needed.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpActualEndpointModulusExact as Endpoint
import DASHI.Physics.YangMills.BalabanP33BishopQuaternionExponentialSquaredChordExact as Chord
open import DASHI.Physics.YangMills.CompactLieProofLevel

fourFifthsSquared twentyThreeSquared gap : ℚᵘ
fourFifthsSquared = + 16 / 25
twentyThreeSquared = + 529 / 576
gap = + 4009 / 14400

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

coefficientGapIdentity :
  BishopReal._≃_
    (BishopReal._-_ (embed twentyThreeSquared) (embed fourFifthsSquared))
    (embed gap)
coefficientGapIdentity =
  let open BishopProperties.ℝ-Solver
  in solve 0
    ((Κ (+ 529 / 576) ⊖ Κ (+ 16 / 25)) ⊜ Κ (+ 4009 / 14400))
    BishopProperties.≃-refl

fourFifthsSquaredBelowTwentyThreeSquared :
  BishopReal._≤_ (embed fourFifthsSquared) (embed twentyThreeSquared)
fourFifthsSquaredBelowTwentyThreeSquared =
  Cross.nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm coefficientGapIdentity)
      (BishopProperties.nonNegx⇒0≤x
        (Cross.embeddedRationalNonnegative gap nonNeg)))

strongCoefficientSquareIdentity : ∀ value →
  BishopReal._≃_
    (BishopReal._*_
      (embed twentyThreeSquared)
      (Chord.square value))
    (Chord.square
      (BishopReal._*_ (embed Endpoint.twentyThreeTwentyFourth) value))
strongCoefficientSquareIdentity value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      Κ (+ 529 / 576) ⊗ (t ⊗ t)
      ⊜ ((Κ (+ 23 / 24) ⊗ t) ⊗ (Κ (+ 23 / 24) ⊗ t)))
    BishopProperties.≃-refl value

fourFifthsSquareBelowStrongSquare :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_ (embed fourFifthsSquared) (Chord.square value))
    (Chord.square
      (BishopReal._*_ (embed Endpoint.twentyThreeTwentyFourth) value))
fourFifthsSquareBelowStrongSquare {value = value} inputs =
  let
    squareNonnegative =
      Cross.squareNonnegativeFromInput value (Concrete.valueNonnegative inputs)
    scaled = BishopProperties.*-monoˡ-≤-nonNeg
      fourFifthsSquaredBelowTwentyThreeSquared squareNonnegative
  in
  BishopProperties.≤-respʳ-≃
    (strongCoefficientSquareIdentity value)
    (BishopProperties.≤-respˡ-≃
      (BishopProperties.*-comm
        (Chord.square value) (embed fourFifthsSquared))
      (BishopProperties.≤-respʳ-≃
        (BishopProperties.*-comm
          (Chord.square value) (embed twentyThreeSquared))
        scaled))

strongSquareBelowSineSquare :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (Chord.square
      (BishopReal._*_ (embed Endpoint.twentyThreeTwentyFourth) value))
    (Chord.square (Elementary.bishopSin dataSet value))
strongSquareBelowSineSquare {dataSet} {value} inputs =
  Chord.squareMonotoneNonnegative
    (BishopProperties.nonNegx,y⇒nonNegx*y
      (Cross.embeddedRationalNonnegative Endpoint.twentyThreeTwentyFourth nonNeg)
      (Concrete.valueNonnegative inputs))
    (Endpoint.coarseSineLower inputs)

sineSquareBelowActualChord :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (Chord.square (Elementary.bishopSin dataSet value))
    (Chord.actualSquaredChord dataSet value)
sineSquareBelowActualChord {dataSet} {value} inputs =
  let
    defectBounds = Low.defectTaylorBounds inputs
    defectNonnegative = BishopProperties.0≤x⇒nonNegx
      (Low.cosineDefectNonnegative defectBounds)
    defectSquareNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx*y defectNonnegative defectNonnegative
    raw = BishopProperties.+-mono-≤
      (BishopProperties.nonNegx⇒0≤x defectSquareNonnegative)
      BishopProperties.≤-refl
  in
  BishopProperties.≤-respˡ-≃
    (let open BishopProperties.ℝ-Solver
     in solve 1
       (λ s → s ⊗ s ⊜ Κ (+ 0 / 1) ⊕ (s ⊗ s))
       BishopProperties.≃-refl (Elementary.bishopSin dataSet value))
    raw

fourFifthsSquaredRadiusBelowActualChord :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_ (embed fourFifthsSquared) (Chord.square value))
    (Chord.actualSquaredChord dataSet value)
fourFifthsSquaredRadiusBelowActualChord inputs =
  BishopProperties.≤-trans
    (fourFifthsSquareBelowStrongSquare inputs)
    (BishopProperties.≤-trans
      (strongSquareBelowSineSquare inputs)
      (sineSquareBelowActualChord inputs))

cmp109BishopKarcherFiveFourthSquaredLevel : ProofLevel
cmp109BishopKarcherFiveFourthSquaredLevel = machineChecked
