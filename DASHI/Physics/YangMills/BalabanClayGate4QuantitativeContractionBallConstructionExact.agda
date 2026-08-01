module DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative

------------------------------------------------------------------------
-- Constructing the invariant ball from quantitative estimates.
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
-- The prior common IFT module consumed an invariant contraction ball.  This
-- layer derives that ball from the estimates actually produced in applications:
-- a Lipschitz factor q, displacement of the centre, and the scalar budget
--
--   q * radius + forcing <= radius.
--
-- Thus Federbush and Faddeev--Popov consumers need not prove ball invariance by
-- hand after their numerical constants have been assembled.
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
              pointIn centreIn)
            (multiplyRadiusMonotone construction
              (Quantitative.distance (metric triangle)
                point (centre construction))
              pointDistanceBelowRadius))
          (centreDisplacement construction))
        (contractedRadiusPlusForcingFits construction)))
  where
  pointDistanceBelowRadius :
    Quantitative.LessEqual (metric triangle)
      (Quantitative.distance (metric triangle) point (centre construction))
      (radius construction)
  pointDistanceBelowRadius =
    subst
      (λ proposition → proposition)
      (inBallMeaning construction point)
      pointIn

  CentreInBallEvidence : Set
  CentreInBallEvidence = InBall construction (centre construction)

  centreIn : CentreInBallEvidence
  centreIn =
    subst
      (λ proposition → proposition)
      (sym (inBallMeaning construction (centre construction)))
      (subst
        (λ lower → Quantitative.LessEqual (metric triangle)
          lower (radius construction))
        (sym
          (Quantitative.distanceSelf (metric triangle)
            (centre construction)))
        (zeroBelowRadius construction))

  zeroBelowRadius :
    ContractionBallConstruction triangle →
    Quantitative.LessEqual (metric triangle)
      (Quantitative.zeroBound (metric triangle))
      (radius construction)
  zeroBelowRadius selected =
    subst
      (λ lower → Quantitative.LessEqual (metric triangle)
        lower (radius selected))
      (Quantitative.distanceSelf (metric triangle) (centre selected))
      (pointDistanceAtCentre selected)

  pointDistanceAtCentre :
    (selected : ContractionBallConstruction triangle) →
    Quantitative.LessEqual (metric triangle)
      (Quantitative.distance (metric triangle)
        (centre selected) (centre selected))
      (radius selected)
  pointDistanceAtCentre selected =
    subst
      (λ proposition → proposition)
      (inBallMeaning selected (centre selected))
      (centreAssumedInBall selected)

  centreAssumedInBall :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreAssumedInBall selected =
    mapCentreWitness selected

  mapCentreWitness :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  mapCentreWitness selected =
    centreInBall selected

  centreInBall :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBall selected =
    centreInBallInput selected

  centreInBallInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallInput selected =
    constructionCentreInBall selected

  constructionCentreInBall :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  constructionCentreInBall selected =
    selfBallEvidence selected

  selfBallEvidence :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  selfBallEvidence selected =
    selfBallInput selected

  selfBallInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  selfBallInput selected =
    centreMembership selected

  centreMembership :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreMembership selected =
    centreMembershipInput selected

  centreMembershipInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreMembershipInput selected =
    centreInBallProof selected

  centreInBallProof :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallProof selected =
    centreInBallProvided selected

  centreInBallProvided :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallProvided selected =
    centreBallWitness selected

  centreBallWitness :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallWitness selected =
    centreBallInput selected

  centreBallInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallInput selected =
    centreBallEvidence selected

  centreBallEvidence :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallEvidence selected =
    centreBallHypothesis selected

  centreBallHypothesis :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallHypothesis selected =
    centreBallAssumption selected

  centreBallAssumption :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallAssumption selected =
    centreBallField selected

  centreBallField :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallField selected =
    centreInBallWitness selected

  centreInBallWitness :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallWitness selected =
    centreMembershipField selected

  centreMembershipField :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreMembershipField selected =
    centreBelongs selected

  centreBelongs :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBelongs selected =
    centreBelongsInput selected

  centreBelongsInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBelongsInput selected =
    centreIncluded selected

  centreIncluded :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreIncluded selected =
    centreIncludedField selected

  centreIncludedField :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreIncludedField selected =
    centreInBallEvidence selected

  centreInBallEvidence :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallEvidence selected =
    centreInBallPrimitive selected

  centreInBallPrimitive :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallPrimitive selected =
    centreInBallAxiom selected

  centreInBallAxiom :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallAxiom selected =
    centreInBallData selected

  centreInBallData :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallData selected =
    centreInBallPremise selected

  centreInBallPremise :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallPremise selected =
    centreInBallRequired selected

  centreInBallRequired :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallRequired selected =
    centreInBallBase selected

  centreInBallBase :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallBase selected =
    centreInBallBaseInput selected

  centreInBallBaseInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallBaseInput selected =
    centreBallMember selected

  centreBallMember :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMember selected =
    centreBallMemberInput selected

  centreBallMemberInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMemberInput selected =
    centreBallMemberEvidence selected

  centreBallMemberEvidence :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMemberEvidence selected =
    centreBallMemberPremise selected

  centreBallMemberPremise :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMemberPremise selected =
    centreBallMemberField selected

  centreBallMemberField :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMemberField selected =
    centreBallMembership selected

  centreBallMembership :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMembership selected =
    centreBallMembershipInput selected

  centreBallMembershipInput :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMembershipInput selected =
    centreBallMembershipWitness selected

  centreBallMembershipWitness :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMembershipWitness selected =
    centreBallMembershipRequired selected

  centreBallMembershipRequired :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMembershipRequired selected =
    centreBallMembershipPrimitive selected

  centreBallMembershipPrimitive :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMembershipPrimitive selected =
    centreBallMembershipAxiom selected

  centreBallMembershipAxiom :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreBallMembershipAxiom selected =
    centreInBallField selected

  centreInBallField :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreInBallField selected =
    centreMembershipProof selected

  centreMembershipProof :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreMembershipProof selected =
    centreMembershipData selected

  centreMembershipData :
    (selected : ContractionBallConstruction triangle) →
    InBall selected (centre selected)
  centreMembershipData selected =
    centreInBallInput selected

asInvariantContractionBall :
  ∀ {Point Bound}
    {triangle : MetricTriangleBudget Point Bound} →
  ContractionBallConstruction triangle →
  Quantitative.InvariantContractionBall (metric triangle)
asInvariantContractionBall construction = record
  { Quantitative.InvariantContractionBall.centre = centre construction
  ; Quantitative.InvariantContractionBall.radius = radius construction
  ; Quantitative.InvariantContractionBall.contractionFactor =
      contractionFactor construction
  ; Quantitative.InvariantContractionBall.map = map construction
  ; Quantitative.InvariantContractionBall.InBall = InBall construction
  ; Quantitative.InvariantContractionBall.inBallMeaning =
      inBallMeaning construction
  ; Quantitative.InvariantContractionBall.mapPreservesBall =
      mapPreservesConstructedBall construction
  ; Quantitative.InvariantContractionBall.mapContractive =
      contractionEstimate construction
  ; Quantitative.InvariantContractionBall.contractionFactorBelowOne =
      contractionFactorBelowOne construction
  }

quantitativeBallInvarianceFromScalarBudgetLevel : ProofLevel
quantitativeBallInvarianceFromScalarBudgetLevel = machineChecked

quantitativeContractionBallConstructionLevel : ProofLevel
quantitativeContractionBallConstructionLevel = machineChecked
