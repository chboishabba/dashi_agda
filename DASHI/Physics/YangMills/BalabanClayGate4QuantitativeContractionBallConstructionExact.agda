module DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative

------------------------------------------------------------------------
-- Constructing an invariant ball from quantitative estimates.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Marco Papi,
-- "On the Domain of the Implicit Function and Applications",
-- Journal of Inequalities and Applications 2005 (2005), 221--234.
-- DOI: 10.1155/JIA.2005.221.
--
-- The common IFT layer consumes an invariant contraction ball.  This module
-- derives map invariance from the estimates produced in applications:
--
--   distance(T centre, centre) <= forcing,
--   distance(T x, T y) <= q distance(x,y),
--   q radius + forcing <= radius.
--
-- The centre-membership proof is kept explicit because it belongs to the
-- selected scalar order and radius convention.
------------------------------------------------------------------------

record MetricTriangleBudget
    (Point Bound : Set) : Set₁ where
  field
    metric : Quantitative.QuantitativeMetricAlgebra Point Bound
    add : Bound → Bound → Bound

    addMonotone : ∀ {left lower right upper} →
      Quantitative.LessEqual metric left lower →
      Quantitative.LessEqual metric right upper →
      Quantitative.LessEqual metric
        (add left right) (add lower upper)

    distanceTriangle : ∀ left middle right →
      Quantitative.LessEqual metric
        (Quantitative.distance metric left right)
        (add
          (Quantitative.distance metric left middle)
          (Quantitative.distance metric middle right))

open MetricTriangleBudget public

record ContractionBallConstruction
    {Point Bound : Set}
    (triangle : MetricTriangleBudget Point Bound) : Set₁ where
  field
    centre : Point
    radius contractionFactor forcing : Bound
    map : Point → Point

    InBall : Point → Set
    inBallMeaning : ∀ point →
      InBall point ≡ Quantitative.LessEqual (metric triangle)
        (Quantitative.distance (metric triangle) point centre)
        radius

    centreInBall : InBall centre

    centreDisplacement :
      Quantitative.LessEqual (metric triangle)
        (Quantitative.distance (metric triangle) (map centre) centre)
        forcing

    contractionEstimate : ∀ left right →
      InBall left → InBall right →
      Quantitative.LessEqual (metric triangle)
        (Quantitative.distance (metric triangle) (map left) (map right))
        (Quantitative.multiply (metric triangle) contractionFactor
          (Quantitative.distance (metric triangle) left right))

    contractionFactorBelowOne :
      Quantitative.StrictlyBelowOne (metric triangle) contractionFactor

    multiplyRadiusMonotone : ∀ value →
      Quantitative.LessEqual (metric triangle) value radius →
      Quantitative.LessEqual (metric triangle)
        (Quantitative.multiply (metric triangle) contractionFactor value)
        (Quantitative.multiply (metric triangle) contractionFactor radius)

    contractedRadiusPlusForcingFits :
      Quantitative.LessEqual (metric triangle)
        (add triangle
          (Quantitative.multiply (metric triangle)
            contractionFactor radius)
          forcing)
        radius

open ContractionBallConstruction public

pointDistanceBelowRadius :
  ∀ {Point Bound}
    {triangle : MetricTriangleBudget Point Bound}
    (construction : ContractionBallConstruction triangle)
    point → InBall construction point →
  Quantitative.LessEqual (metric triangle)
    (Quantitative.distance (metric triangle)
      point (centre construction))
    (radius construction)
pointDistanceBelowRadius construction point pointIn =
  subst
    (λ proposition → proposition)
    (inBallMeaning construction point)
    pointIn

mapPreservesConstructedBall :
  ∀ {Point Bound}
    {triangle : MetricTriangleBudget Point Bound}
    (construction : ContractionBallConstruction triangle)
    point → InBall construction point →
  InBall construction (map construction point)
mapPreservesConstructedBall {triangle = triangle}
    construction point pointIn =
  subst
    (λ proposition → proposition)
    (sym (inBallMeaning construction (map construction point)))
    (Quantitative.transitive (metric triangle)
      (distanceTriangle triangle
        (map construction point)
        (map construction (centre construction))
        (centre construction))
      (Quantitative.transitive (metric triangle)
        (addMonotone triangle
          (Quantitative.transitive (metric triangle)
            (contractionEstimate construction
              point (centre construction)
              pointIn (centreInBall construction))
            (multiplyRadiusMonotone construction
              (Quantitative.distance (metric triangle)
                point (centre construction))
              (pointDistanceBelowRadius construction point pointIn)))
          (centreDisplacement construction))
        (contractedRadiusPlusForcingFits construction)))

asInvariantContractionBall :
  ∀ {Point Bound}
    {triangle : MetricTriangleBudget Point Bound} →
  ContractionBallConstruction triangle →
  Quantitative.InvariantContractionBall (metric triangle)
asInvariantContractionBall construction = record
  { centre = centre construction
  ; radius = radius construction
  ; contractionFactor =
      contractionFactor construction
  ; map = map construction
  ; InBall = InBall construction
  ; inBallMeaning =
      inBallMeaning construction
  ; mapPreservesBall =
      mapPreservesConstructedBall construction
  ; mapContractive =
      contractionEstimate construction
  ; contractionFactorBelowOne =
      contractionFactorBelowOne construction
  }

quantitativeBallInvarianceFromScalarBudgetLevel : ProofLevel
quantitativeBallInvarianceFromScalarBudgetLevel = machineChecked

quantitativeContractionBallConstructionLevel : ProofLevel
quantitativeContractionBallConstructionLevel = machineChecked

physicalCentreMembershipAndScalarBudgetInputsLevel : ProofLevel
physicalCentreMembershipAndScalarBudgetInputsLevel = conditional
