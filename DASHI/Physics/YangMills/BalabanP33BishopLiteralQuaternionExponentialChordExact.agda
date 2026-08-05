module DASHI.Physics.YangMills.BalabanP33BishopLiteralQuaternionExponentialChordExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- The endpoint-safe split is the same mathematical split used by the formal
-- quaternion exponential in mathlib: the pure-imaginary formula is treated
-- separately and the removable sin(t)/t value at t=0 is explicit.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the literal Bishop quaternion
--
--   exp(0,v) = (cos t, sinc(t) v),       ||v||^2 = t^2,
--
-- with
--
--   sinc(0)=1,
--   sinc(t)=sin(t)t^{-1} for t>0.
--
-- Both branches prove, rather than assume, the cancellation
--
--   sinc(t)^2 t^2 = sin(t)^2.
--
-- It follows by exact coordinate algebra that the ambient quaternion squared
-- chord from exp(0,v) to 1 is precisely
--
--   (1-cos t)^2 + sin(t)^2.
--
-- The preceding actual-function theorem then yields the literal squared bound
--
--   chordSquared(exp X,1) <= t^2.
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₂)

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanP33BishopQuaternionExponentialSquaredChordExact as Chord
import DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact as Quaternion
open import DASHI.Physics.YangMills.CompactLieProofLevel

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

vectorNormSquared : Quaternion.Vec3B → BishopReal.ℝ
vectorNormSquared value = Quaternion.dotB value value

quaternionNormSquared : Quaternion.QuaternionB → BishopReal.ℝ
quaternionNormSquared value =
  BishopReal._+_
    (square (Quaternion.scalar value))
    (vectorNormSquared (Quaternion.vector value))

subVec : Quaternion.Vec3B → Quaternion.Vec3B → Quaternion.Vec3B
subVec (Quaternion.vec3B ax ay az) (Quaternion.vec3B bx by bz) =
  Quaternion.vec3B
    (BishopReal._-_ ax bx)
    (BishopReal._-_ ay by)
    (BishopReal._-_ az bz)

subQuaternion : Quaternion.QuaternionB → Quaternion.QuaternionB → Quaternion.QuaternionB
subQuaternion left right =
  Quaternion.quaternionB
    (BishopReal._-_ (Quaternion.scalar left) (Quaternion.scalar right))
    (subVec (Quaternion.vector left) (Quaternion.vector right))

zeroVec : Quaternion.Vec3B
zeroVec = Quaternion.vec3B BishopReal.0ℝ BishopReal.0ℝ BishopReal.0ℝ

oneQuaternion : Quaternion.QuaternionB
oneQuaternion = Quaternion.quaternionB BishopReal.1ℝ zeroVec

chordSquared : Quaternion.QuaternionB → Quaternion.QuaternionB → BishopReal.ℝ
chordSquared left right = quaternionNormSquared (subQuaternion left right)

record PureQuaternionRadius
    (radius : BishopReal.ℝ) : Set where
  field
    direction : Quaternion.Vec3B
    directionNormSquared :
      BishopReal._≃_ (vectorNormSquared direction) (square radius)

open PureQuaternionRadius public

radiusNonzeroFromPositive :
  ∀ {radius} →
  BishopReal._<_ BishopReal.0ℝ radius →
  BishopReal._≄_ radius BishopReal.0ℝ
radiusNonzeroFromPositive radiusPositive = inj₂ radiusPositive

positiveSinc :
  Elementary.BishopElementaryPowerSeriesData →
  (radius : BishopReal.ℝ) →
  BishopReal._≄_ radius BishopReal.0ℝ →
  BishopReal.ℝ
positiveSinc dataSet radius radiusNonzero =
  BishopReal._*_
    (Elementary.bishopSin dataSet radius)
    (BishopInverse._⁻¹ radius radiusNonzero)

positiveSincCancellation :
  ∀ dataSet radius
    (radiusNonzero : BishopReal._≄_ radius BishopReal.0ℝ) →
  BishopReal._≃_
    (BishopReal._*_
      (square (positiveSinc dataSet radius radiusNonzero))
      (square radius))
    (square (Elementary.bishopSin dataSet radius))
positiveSincCancellation dataSet radius radiusNonzero =
  let
    sineValue = Elementary.bishopSin dataSet radius
    inverseRadius = BishopInverse._⁻¹ radius radiusNonzero
    rearrange :
      BishopReal._≃_
        (BishopReal._*_
          (square (BishopReal._*_ sineValue inverseRadius))
          (square radius))
        (BishopReal._*_
          (square sineValue)
          (square (BishopReal._*_ radius inverseRadius)))
    rearrange =
      let open BishopProperties.ℝ-Solver
      in solve 3
        (λ s r ri →
          (((s ⊗ ri) ⊗ (s ⊗ ri)) ⊗ (r ⊗ r))
          ⊜ ((s ⊗ s) ⊗ ((r ⊗ ri) ⊗ (r ⊗ ri))))
        BishopProperties.≃-refl sineValue radius inverseRadius
    cancel = BishopInverse.*-inverseʳ radius radiusNonzero
  in
  BishopProperties.≃-trans rearrange
    (BishopProperties.≃-trans
      (BishopProperties.*-cong BishopProperties.≃-refl
        (BishopProperties.*-cong cancel cancel))
      (let open BishopProperties.ℝ-Solver
       in solve 1
         (λ s → (s ⊗ s) ⊗
           (Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1))
           ⊜ s ⊗ s)
         BishopProperties.≃-refl sineValue))

sineAtZero :
  ∀ {dataSet radius} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius) →
  BishopReal._≃_ radius BishopReal.0ℝ →
  BishopReal._≃_ (Elementary.bishopSin dataSet radius) BishopReal.0ℝ
sineAtZero inputs radiusZero =
  let
    bounds = Low.polynomialTaylorBounds inputs
    sineBelowZero =
      BishopProperties.≤-respʳ-≃ radiusZero
        (Low.sineLinearUpper bounds)
    zeroBelowSine =
      BishopProperties.nonNegx⇒0≤x
        (Chord.actualSineNonnegative inputs)
  in
  BishopProperties.≤-antisym sineBelowZero zeroBelowSine

zeroSincCancellation :
  ∀ {dataSet radius} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius) →
  (radiusZero : BishopReal._≃_ radius BishopReal.0ℝ) →
  BishopReal._≃_
    (BishopReal._*_ (square BishopReal.1ℝ) (square radius))
    (square (Elementary.bishopSin dataSet radius))
zeroSincCancellation {dataSet} {radius} inputs radiusZero =
  let sineZero = sineAtZero inputs radiusZero
  in
  BishopProperties.≃-trans
    (let open BishopProperties.ℝ-Solver
     in solve 1
       (λ r →
         (Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1)) ⊗ (r ⊗ r)
         ⊜ r ⊗ r)
       BishopProperties.≃-refl radius)
    (BishopProperties.≃-trans
      (BishopProperties.*-cong radiusZero radiusZero)
      (BishopProperties.≃-symm
        (BishopProperties.*-cong sineZero sineZero)))

sincExtended :
  ∀ {dataSet radius} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet radius →
  Positive.NonnegativeRadiusCase radius →
  BishopReal.ℝ
sincExtended inputs (Positive.zeroRadius radiusZero) = BishopReal.1ℝ
sincExtended {dataSet} {radius} inputs
    (Positive.positiveRadius radiusPositive) =
  positiveSinc dataSet radius (radiusNonzeroFromPositive radiusPositive)

sincExtendedCancellation :
  ∀ {dataSet radius}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius)
    (radiusCase : Positive.NonnegativeRadiusCase radius) →
  BishopReal._≃_
    (BishopReal._*_
      (square (sincExtended inputs radiusCase))
      (square radius))
    (square (Elementary.bishopSin dataSet radius))
sincExtendedCancellation inputs (Positive.zeroRadius radiusZero) =
  zeroSincCancellation inputs radiusZero
sincExtendedCancellation {dataSet} {radius} inputs
    (Positive.positiveRadius radiusPositive) =
  positiveSincCancellation dataSet radius
    (radiusNonzeroFromPositive radiusPositive)

literalPureQuaternionExponential :
  ∀ {dataSet radius} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius) →
  Positive.NonnegativeRadiusCase radius →
  PureQuaternionRadius radius →
  Quaternion.QuaternionB
literalPureQuaternionExponential {dataSet} {radius}
    inputs radiusCase radial =
  Quaternion.quaternionB
    (Elementary.bishopCos dataSet radius)
    (Quaternion.scaleVecB
      (sincExtended inputs radiusCase)
      (direction radial))

scaledVectorNormIdentity :
  ∀ scale (value : Quaternion.Vec3B) →
  BishopReal._≃_
    (vectorNormSquared (Quaternion.scaleVecB scale value))
    (BishopReal._*_ (square scale) (vectorNormSquared value))
scaledVectorNormIdentity scale (Quaternion.vec3B x y z) =
  let open BishopProperties.ℝ-Solver
  in solve 4
    (λ a x y z →
      ((a ⊗ x) ⊗ (a ⊗ x))
        ⊕ (((a ⊗ y) ⊗ (a ⊗ y))
          ⊕ ((a ⊗ z) ⊗ (a ⊗ z)))
      ⊜ (a ⊗ a) ⊗
        ((x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z))))
    BishopProperties.≃-refl scale x y z

literalChordCoordinateExpansion :
  ∀ scalarValue scaleValue (value : Quaternion.Vec3B) →
  BishopReal._≃_
    (chordSquared
      (Quaternion.quaternionB scalarValue
        (Quaternion.scaleVecB scaleValue value))
      oneQuaternion)
    (BishopReal._+_
      (square (BishopReal._-_ scalarValue BishopReal.1ℝ))
      (vectorNormSquared (Quaternion.scaleVecB scaleValue value)))
literalChordCoordinateExpansion scalarValue scaleValue
    (Quaternion.vec3B x y z) =
  let open BishopProperties.ℝ-Solver
  in solve 5
    (λ c a x y z →
      (((c ⊖ Κ (+ 1 / 1)) ⊗ (c ⊖ Κ (+ 1 / 1)))
        ⊕ (((a ⊗ x) ⊖ Κ (+ 0 / 1))
              ⊗ ((a ⊗ x) ⊖ Κ (+ 0 / 1))
          ⊕ ((((a ⊗ y) ⊖ Κ (+ 0 / 1))
                ⊗ ((a ⊗ y) ⊖ Κ (+ 0 / 1)))
            ⊕ (((a ⊗ z) ⊖ Κ (+ 0 / 1))
                ⊗ ((a ⊗ z) ⊖ Κ (+ 0 / 1))))))
      ⊜ (((c ⊖ Κ (+ 1 / 1)) ⊗ (c ⊖ Κ (+ 1 / 1)))
        ⊕ (((a ⊗ x) ⊗ (a ⊗ x))
          ⊕ (((a ⊗ y) ⊗ (a ⊗ y))
            ⊕ ((a ⊗ z) ⊗ (a ⊗ z))))))
    BishopProperties.≃-refl scalarValue scaleValue x y z

literalExponentialChordSquaredExact :
  ∀ {dataSet radius}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius)
    (radiusCase : Positive.NonnegativeRadiusCase radius)
    (radial : PureQuaternionRadius radius) →
  BishopReal._≃_
    (chordSquared
      (literalPureQuaternionExponential inputs radiusCase radial)
      oneQuaternion)
    (Chord.actualSquaredChord dataSet radius)
literalExponentialChordSquaredExact {dataSet} {radius}
    inputs radiusCase radial =
  let
    scale = sincExtended inputs radiusCase
    sineValue = Elementary.bishopSin dataSet radius
    cosineValue = Elementary.bishopCos dataSet radius
    scaledNorm = scaledVectorNormIdentity scale (direction radial)
    radiusMeaning = directionNormSquared radial
    sincMeaning = sincExtendedCancellation inputs radiusCase
    coordinateExpansion =
      literalChordCoordinateExpansion
        cosineValue scale (direction radial)
    scalarOrientation :
      BishopReal._≃_
        (square (BishopReal._-_ cosineValue BishopReal.1ℝ))
        (square (BishopReal._-_ BishopReal.1ℝ cosineValue))
    scalarOrientation =
      let open BishopProperties.ℝ-Solver
      in solve 1
        (λ c →
          (c ⊖ Κ (+ 1 / 1)) ⊗ (c ⊖ Κ (+ 1 / 1))
          ⊜ (Κ (+ 1 / 1) ⊖ c) ⊗ (Κ (+ 1 / 1) ⊖ c))
        BishopProperties.≃-refl cosineValue
  in
  BishopProperties.≃-trans coordinateExpansion
    (BishopProperties.≃-trans
      (BishopProperties.+-cong
        scalarOrientation scaledNorm)
      (BishopProperties.≃-trans
        (BishopProperties.+-cong BishopProperties.≃-refl
          (BishopProperties.*-cong BishopProperties.≃-refl radiusMeaning))
        (BishopProperties.+-cong BishopProperties.≃-refl sincMeaning)))

literalExponentialSquaredChordBelowRadiusSquared :
  ∀ {dataSet radius}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius)
    (radiusCase : Positive.NonnegativeRadiusCase radius)
    (radial : PureQuaternionRadius radius) →
  BishopReal._≤_
    (chordSquared
      (literalPureQuaternionExponential inputs radiusCase radial)
      oneQuaternion)
    (square radius)
literalExponentialSquaredChordBelowRadiusSquared
    inputs radiusCase radial =
  BishopProperties.≤-respˡ-≃
    (literalExponentialChordSquaredExact inputs radiusCase radial)
    (Chord.actualSquaredChordBelowRadiusSquared inputs)

p33LiteralBishopQuaternionExponentialLevel : ProofLevel
p33LiteralBishopQuaternionExponentialLevel = machineChecked

p33LiteralSincEndpointCancellationLevel : ProofLevel
p33LiteralSincEndpointCancellationLevel = machineChecked

p33LiteralQuaternionSquaredChordBoundLevel : ProofLevel
p33LiteralQuaternionSquaredChordBoundLevel = machineChecked

bishopEuclideanSquareRootMetricLevel : ProofLevel
bishopEuclideanSquareRootMetricLevel = conditional
