module DASHI.Physics.Closure.NSTriadKNFixedEigenvalueCircleSchurDecayNoGoRound101Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Jean Bourgain; Zeev Rudnick.
-- Title: "On the nodal sets of toral eigenfunctions".
-- Inventiones Mathematicae 185 (2011), 199--237.
-- DOI: 10.1007/s00222-010-0307-2.
--
-- Authors: Jean Bourgain; Zeev Rudnick.
-- Title: "On the geometry of the nodal lines of eigenfunctions of the
-- two-dimensional torus".
-- Annales Henri Poincare 12 (2011), 1027--1053.
-- DOI: 10.1007/s00023-011-0098-z.
--
-- ROUND101 / WHAT THE ARITHMETIC CIRCLE CAN AND CANNOT BUY
--
-- Round100 identified each fixed (m,l,n,k) resonance fibre with an arithmetic
-- circle.  The useful number-theoretic fact is sparsity of lattice points on
-- circles/arcs.  But a Schur coefficient obtained by the crude route
--
--      theta = (# incidences) * (one-incidence majorant)
--
-- can NEVER have more radial decay than the one-incidence majorant itself:
-- every nonempty circle has count >= 1, so for nonnegative weight w,
--
--      w <= count * w.
--
-- In particular, if the physical coefficient has a positive nondecaying floor
-- on a family of nonempty resonant circles, arithmetic counting alone cannot
-- manufacture a summable separation kernel.  Circle sparsity can reduce a
-- multiplicity LOSS; it cannot create a new negative power of the radius.
--
-- This formally corrects the proposed `FixedEigenvalueResonantCircleSchur`
-- attack: its summable Theta must obtain decay from the literal interaction
-- coefficient, angular cancellation/orthogonality, or a short-arc mechanism.
-- Full-circle cardinality by itself is not the missing exponent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

circleCountingMajorant : ℚ → ℚ → ℚ
circleCountingMajorant count oneIncidenceWeight = count * oneIncidenceWeight

nonemptyCountCannotImproveWeight :
  ∀ count weight →
  1ℚ ≤ count →
  0ℚ ≤ weight →
  weight ≤ circleCountingMajorant count weight
nonemptyCountCannotImproveWeight count weight oneBelowCount zeroBelowWeight =
  let
    instance
      weightNN : NonNegative weight
      weightNN = nonNegative zeroBelowWeight

    scaled : 1ℚ * weight ≤ count * weight
    scaled = ℚP.*-monoʳ-≤-nonNeg weight oneBelowCount

    oneTimesWeight : 1ℚ * weight ≡ weight
    oneTimesWeight = solve (weight ∷ [])
  in
  subst
    (λ lhs → lhs ≤ circleCountingMajorant count weight)
    oneTimesWeight
    scaled

positiveWeightFloorSurvivesCounting :
  ∀ count weight floor →
  1ℚ ≤ count →
  0ℚ ≤ weight →
  floor ≤ weight →
  floor ≤ circleCountingMajorant count weight
positiveWeightFloorSurvivesCounting count weight floor countPositive weightNonnegative floorBelowWeight =
  ℚP.≤-trans floorBelowWeight
    (nonemptyCountCannotImproveWeight count weight countPositive weightNonnegative)

twoNonemptyRowsPreserveTwoFloors :
  ∀ count1 count2 weight1 weight2 floor →
  1ℚ ≤ count1 →
  1ℚ ≤ count2 →
  0ℚ ≤ weight1 →
  0ℚ ≤ weight2 →
  floor ≤ weight1 →
  floor ≤ weight2 →
  floor + floor
  ≤ circleCountingMajorant count1 weight1
      + circleCountingMajorant count2 weight2
twoNonemptyRowsPreserveTwoFloors count1 count2 weight1 weight2 floor
    count1Positive count2Positive weight1Nonnegative weight2Nonnegative
    floorBelowWeight1 floorBelowWeight2 =
  ℚP.+-mono-≤
    (positiveWeightFloorSurvivesCounting
      count1 weight1 floor count1Positive weight1Nonnegative floorBelowWeight1)
    (positiveWeightFloorSurvivesCounting
      count2 weight2 floor count2Positive weight2Nonnegative floorBelowWeight2)

round101FullCircleCountingAloneCreatesRadialDecay : Bool
round101FullCircleCountingAloneCreatesRadialDecay = false

round101CircleSchurNeedsWeightedOrCancellationGain : Bool
round101CircleSchurNeedsWeightedOrCancellationGain = true

round101FullCircleCountingAloneCreatesRadialDecayIsFalse :
  round101FullCircleCountingAloneCreatesRadialDecay ≡ false
round101FullCircleCountingAloneCreatesRadialDecayIsFalse = refl
