module DASHI.Physics.YangMills.BalabanClayGate4HalfContractionInvariantBallExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact as Construction

------------------------------------------------------------------------
-- Source-aligned invariant-ball arithmetic for the background gauge slice.
--
-- Bałaban's gauge-fixing proof obtains contraction factor 1/2 on a domain of
-- radius beta alpha_4 with beta=1/4.  The abstract arithmetic needed is simply
--
--   q <= 1/2,
--   q r <= r/2,
--   f <= r/2,
--   r/2 + r/2 <= r.
------------------------------------------------------------------------

record HalfContractionBudget
    {Point Bound : Set}
    (triangle : Construction.MetricTriangleBudget Point Bound) : Set₁ where
  field
    half : Bound
    halfBelowOne :
      Quantitative.StrictlyBelowOne (Construction.metric triangle) half

    halfRadius : Bound → Bound

    halfTimesRadius : ∀ radius →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.multiply (Construction.metric triangle) half radius)
        (halfRadius radius)

    twoHalvesFit : ∀ radius →
      Quantitative.LessEqual (Construction.metric triangle)
        (Construction.add triangle
          (halfRadius radius) (halfRadius radius))
        radius

    belowHalfBelowOne : ∀ {value} →
      Quantitative.LessEqual (Construction.metric triangle) value half →
      Quantitative.StrictlyBelowOne (Construction.metric triangle) value

    multiplyMonotone : ∀ {left leftUpper right rightUpper} →
      Quantitative.LessEqual (Construction.metric triangle) left leftUpper →
      Quantitative.LessEqual (Construction.metric triangle) right rightUpper →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.multiply (Construction.metric triangle) left right)
        (Quantitative.multiply (Construction.metric triangle)
          leftUpper rightUpper)

open HalfContractionBudget public

halfContractionForcingFits :
  ∀ {Point Bound}
    {triangle : Construction.MetricTriangleBudget Point Bound}
    (budget : HalfContractionBudget triangle)
    contraction forcing radius →
  Quantitative.LessEqual (Construction.metric triangle)
    contraction (half budget) →
  Quantitative.LessEqual (Construction.metric triangle)
    forcing (halfRadius budget radius) →
  Quantitative.LessEqual (Construction.metric triangle)
    (Construction.add triangle
      (Quantitative.multiply (Construction.metric triangle)
        contraction radius)
      forcing)
    radius
halfContractionForcingFits {triangle = triangle}
    budget contraction forcing radius contractionBound forcingBound =
  Quantitative.transitive (Construction.metric triangle)
    (Construction.addMonotone triangle
      (Quantitative.transitive (Construction.metric triangle)
        (multiplyMonotone budget contractionBound
          (Quantitative.reflexive (Construction.metric triangle) radius))
        (halfTimesRadius budget radius))
      forcingBound)
    (twoHalvesFit budget radius)

record HalfContractionBall
    {Point Bound : Set}
    {triangle : Construction.MetricTriangleBudget Point Bound}
    (budget : HalfContractionBudget triangle) : Set₁ where
  field
    centre : Point
    radius contraction forcing : Bound
    map : Point → Point

    InBall : Point → Set
    inBallMeaning : ∀ point →
      InBall point ≡ Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle) point centre)
        radius

    centreInBall : InBall centre

    centreDisplacement :
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle)
          (map centre) centre)
        forcing

    contractionEstimate : ∀ left right →
      InBall left → InBall right →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle)
          (map left) (map right))
        (Quantitative.multiply (Construction.metric triangle)
          contraction
          (Quantitative.distance (Construction.metric triangle) left right))

    contractionBelowHalf :
      Quantitative.LessEqual (Construction.metric triangle)
        contraction (half budget)

    forcingBelowHalfRadius :
      Quantitative.LessEqual (Construction.metric triangle)
        forcing (halfRadius budget radius)

    multiplyRadiusMonotone : ∀ value →
      Quantitative.LessEqual (Construction.metric triangle) value radius →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.multiply (Construction.metric triangle)
          contraction value)
        (Quantitative.multiply (Construction.metric triangle)
          contraction radius)

open HalfContractionBall public

asContractionBallConstruction :
  ∀ {Point Bound}
    {triangle : Construction.MetricTriangleBudget Point Bound}
    {budget : HalfContractionBudget triangle} →
  HalfContractionBall budget →
  Construction.ContractionBallConstruction triangle
asContractionBallConstruction {triangle = triangle} {budget = budget} ball = record
  { centre = centre ball
  ; radius = radius ball
  ; contractionFactor = contraction ball
  ; forcing = forcing ball
  ; map = map ball
  ; InBall = InBall ball
  ; inBallMeaning = inBallMeaning ball
  ; centreInBall = centreInBall ball
  ; centreDisplacement =
      centreDisplacement ball
  ; contractionEstimate =
      contractionEstimate ball
  ; contractionFactorBelowOne =
      belowHalfBelowOne budget (contractionBelowHalf ball)
  ; multiplyRadiusMonotone =
      multiplyRadiusMonotone ball
  ; contractedRadiusPlusForcingFits =
      halfContractionForcingFits budget
        (contraction ball) (forcing ball) (radius ball)
        (contractionBelowHalf ball) (forcingBelowHalfRadius ball)
  }

halfContractionInvariantArithmeticLevel : ProofLevel
halfContractionInvariantArithmeticLevel = machineChecked

halfContractionBallAdapterLevel : ProofLevel
halfContractionBallAdapterLevel = machineChecked
