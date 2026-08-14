module DASHI.Physics.YangMills.BalabanCMP109BishopKarcherFiveFourthMetricExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Hermann Karcher, "Riemannian Center of Mass and Mollifier Smoothing",
-- Communications on Pure and Applied Mathematics 30 (1977), 509--541.
-- DOI: 10.1002/cpa.3160300502.
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations",
-- second edition, Springer, 2015. DOI: 10.1007/978-3-319-13467-3.
-- Errett Bishop and Douglas Bridges, "Constructive Analysis",
-- Springer, 1985. DOI: 10.1007/978-3-642-61667-9.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopLiteralQuaternionExponentialChordExact as Literal
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as Metric
import DASHI.Physics.YangMills.BalabanCMP109BishopKarcherFiveFourthSquaredExact as Squared
open import DASHI.Physics.YangMills.CompactLieProofLevel

fourFifths fiveFourths : ℚᵘ
fourFifths = + 4 / 5
fiveFourths = + 5 / 4

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

fourFifthsNonnegative : BishopReal.NonNegative (embed fourFifths)
fourFifthsNonnegative = Cross.embeddedRationalNonnegative fourFifths nonNeg

fiveFourthsNonnegative : BishopReal.NonNegative (embed fiveFourths)
fiveFourthsNonnegative = Cross.embeddedRationalNonnegative fiveFourths nonNeg

scaledRadiusSquareExact : ∀ radius →
  BishopReal._≃_
    (Metric.square (BishopReal._*_ (embed fourFifths) radius))
    (BishopReal._*_ (embed Squared.fourFifthsSquared) (Metric.square radius))
scaledRadiusSquareExact radius =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t → ((Κ (+ 4 / 5) ⊗ t) ⊗ (Κ (+ 4 / 5) ⊗ t))
      ⊜ Κ (+ 16 / 25) ⊗ (t ⊗ t))
    BishopProperties.≃-refl radius

fourFifthsTimesFiveFourthsCancels : ∀ radius →
  BishopReal._≃_
    (BishopReal._*_ (embed fiveFourths)
      (BishopReal._*_ (embed fourFifths) radius))
    radius
fourFifthsTimesFiveFourthsCancels radius =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t → Κ (+ 5 / 4) ⊗ (Κ (+ 4 / 5) ⊗ t) ⊜ t)
    BishopProperties.≃-refl radius

literalFourFifthsRadiusBelowChord :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ {dataSet radius}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius)
    (radiusCase : Positive.NonnegativeRadiusCase radius)
    (radial : Literal.PureQuaternionRadius radius) →
  BishopReal._≤_
    (BishopReal._*_ (embed fourFifths) radius)
    (Metric.literalChordDistance roots
      (Literal.literalPureQuaternionExponential inputs radiusCase radial)
      Literal.oneQuaternion)
literalFourFifthsRadiusBelowChord roots {radius = radius} inputs radiusCase radial =
  let
    exponential = Literal.literalPureQuaternionExponential inputs radiusCase radial
    targetSquared = Squared.fourFifthsSquaredRadiusBelowActualChord inputs

    literalSquared :
      BishopReal._≤_
        (Metric.square (BishopReal._*_ (embed fourFifths) radius))
        (Literal.chordSquared exponential Literal.oneQuaternion)
    literalSquared =
      BishopProperties.≤-respʳ-≃
        (BishopProperties.≃-symm
          (Literal.literalExponentialChordSquaredExact inputs radiusCase radial))
        (BishopProperties.≤-respˡ-≃
          (scaledRadiusSquareExact radius)
          targetSquared)

    scaledNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx*y
        fourFifthsNonnegative (Concrete.valueNonnegative inputs)

    rooted = Metric.rootMonotone roots
      (Metric.squareNonnegative roots
        (BishopReal._*_ (embed fourFifths) radius))
      literalSquared

    rootScaledIsScaled :
      BishopReal._≃_
        (Metric.root roots
          (Metric.square (BishopReal._*_ (embed fourFifths) radius)))
        (BishopReal._*_ (embed fourFifths) radius)
    rootScaledIsScaled = BishopProperties.≃-trans
      (Metric.rootOfSquare roots (BishopReal._*_ (embed fourFifths) radius))
      (BishopProperties.nonNegx⇒∣x∣≃x scaledNonnegative)
  in
  BishopProperties.≤-respˡ-≃ rootScaledIsScaled rooted

literalGeodesicRadiusBelowFiveFourthChord :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ {dataSet radius}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius)
    (radiusCase : Positive.NonnegativeRadiusCase radius)
    (radial : Literal.PureQuaternionRadius radius) →
  BishopReal._≤_ radius
    (BishopReal._*_ (embed fiveFourths)
      (Metric.literalChordDistance roots
        (Literal.literalPureQuaternionExponential inputs radiusCase radial)
        Literal.oneQuaternion))
literalGeodesicRadiusBelowFiveFourthChord roots {radius = radius} inputs radiusCase radial =
  let
    base = literalFourFifthsRadiusBelowChord roots inputs radiusCase radial
    scaled = BishopProperties.*-monoˡ-≤-nonNeg base fiveFourthsNonnegative
  in
  BishopProperties.≤-respˡ-≃
    (fourFifthsTimesFiveFourthsCancels radius)
    scaled

cmp109BishopKarcherFiveFourthMetricLevel : ProofLevel
cmp109BishopKarcherFiveFourthMetricLevel = machineChecked

bishopSquareRootBackendForKarcherLevel : ProofLevel
bishopSquareRootBackendForKarcherLevel = conditional
