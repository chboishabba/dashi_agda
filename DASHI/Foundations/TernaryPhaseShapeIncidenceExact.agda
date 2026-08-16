module DASHI.Foundations.TernaryPhaseShapeIncidenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Compute the complete joint incidence of the two independently constructed
-- quotients of the same 27 ternary endomorphisms:
--
--   C3 output phase quotient : 27 -> 9 = 2 units + 7 nonunits
--   S3 conjugacy quotient    : 27 -> 7 functional-graph shapes.
--
-- The 27 phase/class pairs below are exhaustive because
-- T^T = Phase3 x PhaseClass9 exactly.  The resulting table shows:
--
-- * the cyclic unit phase class meets identity once and 3-cycle twice;
-- * the reflective unit class is transposition in every output phase;
-- * the collapsed low/low class is constant in every output phase;
-- * each other nonunit phase class meets each of the three rank-two
--   functional-graph shapes exactly once.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Cognition.PhaseEnrichedTrit as Phase3
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

shapeAtFactor :
  Phase3.Phase3 →
  Phase.PhaseClass9 →
  Shape.ShapeOrbit7
shapeAtFactor phase phaseClass =
  Shape.shapeClass (Phase.unfactorize27 (phase , phaseClass))

phaseShapeIncidence :
  Phase3.Phase3 →
  Phase.PhaseClass9 →
  Phase.PhaseClass9 × Shape.ShapeOrbit7
phaseShapeIncidence phase phaseClass =
  phaseClass , shapeAtFactor phase phaseClass

-- Unit sector.
unitCyclicPhase0IsIdentity :
  shapeAtFactor Phase3.phase0 (inj₁ Phase.unitCyclic)
  ≡ Shape.identityShape
unitCyclicPhase0IsIdentity = refl

unitCyclicPhase1IsThreeCycle :
  shapeAtFactor Phase3.phase1 (inj₁ Phase.unitCyclic)
  ≡ Shape.threeCycleShape
unitCyclicPhase1IsThreeCycle = refl

unitCyclicPhase2IsThreeCycle :
  shapeAtFactor Phase3.phase2 (inj₁ Phase.unitCyclic)
  ≡ Shape.threeCycleShape
unitCyclicPhase2IsThreeCycle = refl

unitReflectivePhase0IsTransposition :
  shapeAtFactor Phase3.phase0 (inj₁ Phase.unitReflective)
  ≡ Shape.transpositionShape
unitReflectivePhase0IsTransposition = refl

unitReflectivePhase1IsTransposition :
  shapeAtFactor Phase3.phase1 (inj₁ Phase.unitReflective)
  ≡ Shape.transpositionShape
unitReflectivePhase1IsTransposition = refl

unitReflectivePhase2IsTransposition :
  shapeAtFactor Phase3.phase2 (inj₁ Phase.unitReflective)
  ≡ Shape.transpositionShape
unitReflectivePhase2IsTransposition = refl

-- Constant nonunit sector.
nonUnitLowLowPhase0IsConstant :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitLowLow)
  ≡ Shape.constantShape
nonUnitLowLowPhase0IsConstant = refl

nonUnitLowLowPhase1IsConstant :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitLowLow)
  ≡ Shape.constantShape
nonUnitLowLowPhase1IsConstant = refl

nonUnitLowLowPhase2IsConstant :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitLowLow)
  ≡ Shape.constantShape
nonUnitLowLowPhase2IsConstant = refl

-- Six remaining nonunit phase classes.  Each hits each rank-two shape once.
nonUnitLowMidPhase0 :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitLowMid)
  ≡ Shape.rank2OneFixedShape
nonUnitLowMidPhase0 = refl

nonUnitLowMidPhase1 :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitLowMid)
  ≡ Shape.rank2TwoFixedShape
nonUnitLowMidPhase1 = refl

nonUnitLowMidPhase2 :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitLowMid)
  ≡ Shape.rank2TwoCycleShape
nonUnitLowMidPhase2 = refl

nonUnitLowHighPhase0 :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitLowHigh)
  ≡ Shape.rank2TwoFixedShape
nonUnitLowHighPhase0 = refl

nonUnitLowHighPhase1 :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitLowHigh)
  ≡ Shape.rank2OneFixedShape
nonUnitLowHighPhase1 = refl

nonUnitLowHighPhase2 :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitLowHigh)
  ≡ Shape.rank2TwoCycleShape
nonUnitLowHighPhase2 = refl

nonUnitMidLowPhase0 :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitMidLow)
  ≡ Shape.rank2TwoFixedShape
nonUnitMidLowPhase0 = refl

nonUnitMidLowPhase1 :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitMidLow)
  ≡ Shape.rank2TwoCycleShape
nonUnitMidLowPhase1 = refl

nonUnitMidLowPhase2 :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitMidLow)
  ≡ Shape.rank2OneFixedShape
nonUnitMidLowPhase2 = refl

nonUnitMidMidPhase0 :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitMidMid)
  ≡ Shape.rank2TwoFixedShape
nonUnitMidMidPhase0 = refl

nonUnitMidMidPhase1 :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitMidMid)
  ≡ Shape.rank2OneFixedShape
nonUnitMidMidPhase1 = refl

nonUnitMidMidPhase2 :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitMidMid)
  ≡ Shape.rank2TwoCycleShape
nonUnitMidMidPhase2 = refl

nonUnitHighLowPhase0 :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitHighLow)
  ≡ Shape.rank2OneFixedShape
nonUnitHighLowPhase0 = refl

nonUnitHighLowPhase1 :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitHighLow)
  ≡ Shape.rank2TwoCycleShape
nonUnitHighLowPhase1 = refl

nonUnitHighLowPhase2 :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitHighLow)
  ≡ Shape.rank2TwoFixedShape
nonUnitHighLowPhase2 = refl

nonUnitHighHighPhase0 :
  shapeAtFactor Phase3.phase0 (inj₂ Phase.nonUnitHighHigh)
  ≡ Shape.rank2TwoFixedShape
nonUnitHighHighPhase0 = refl

nonUnitHighHighPhase1 :
  shapeAtFactor Phase3.phase1 (inj₂ Phase.nonUnitHighHigh)
  ≡ Shape.rank2TwoCycleShape
nonUnitHighHighPhase1 = refl

nonUnitHighHighPhase2 :
  shapeAtFactor Phase3.phase2 (inj₂ Phase.nonUnitHighHigh)
  ≡ Shape.rank2OneFixedShape
nonUnitHighHighPhase2 = refl

data RankTwoShape : Shape.ShapeOrbit7 → Set where
  rankTwoOneFixed :
    RankTwoShape Shape.rank2OneFixedShape
  rankTwoTwoFixed :
    RankTwoShape Shape.rank2TwoFixedShape
  rankTwoTwoCycle :
    RankTwoShape Shape.rank2TwoCycleShape

-- Positive, proof-carrying form for the six genuinely rank-two phase classes.
data NonconstantNonunitPhase6 : Set where
  lowMid lowHigh midLow midMid highLow highHigh :
    NonconstantNonunitPhase6

toNonUnitPhase7 :
  NonconstantNonunitPhase6 → Phase.NonUnitPhase7
toNonUnitPhase7 lowMid = Phase.nonUnitLowMid
toNonUnitPhase7 lowHigh = Phase.nonUnitLowHigh
toNonUnitPhase7 midLow = Phase.nonUnitMidLow
toNonUnitPhase7 midMid = Phase.nonUnitMidMid
toNonUnitPhase7 highLow = Phase.nonUnitHighLow
toNonUnitPhase7 highHigh = Phase.nonUnitHighHigh

nonconstantNonunitIsRankTwo :
  (phase : Phase3.Phase3) →
  (phaseClass : NonconstantNonunitPhase6) →
  RankTwoShape
    (shapeAtFactor phase (inj₂ (toNonUnitPhase7 phaseClass)))
nonconstantNonunitIsRankTwo Phase3.phase0 lowMid = rankTwoOneFixed
nonconstantNonunitIsRankTwo Phase3.phase1 lowMid = rankTwoTwoFixed
nonconstantNonunitIsRankTwo Phase3.phase2 lowMid = rankTwoTwoCycle
nonconstantNonunitIsRankTwo Phase3.phase0 lowHigh = rankTwoTwoFixed
nonconstantNonunitIsRankTwo Phase3.phase1 lowHigh = rankTwoOneFixed
nonconstantNonunitIsRankTwo Phase3.phase2 lowHigh = rankTwoTwoCycle
nonconstantNonunitIsRankTwo Phase3.phase0 midLow = rankTwoTwoFixed
nonconstantNonunitIsRankTwo Phase3.phase1 midLow = rankTwoTwoCycle
nonconstantNonunitIsRankTwo Phase3.phase2 midLow = rankTwoOneFixed
nonconstantNonunitIsRankTwo Phase3.phase0 midMid = rankTwoTwoFixed
nonconstantNonunitIsRankTwo Phase3.phase1 midMid = rankTwoOneFixed
nonconstantNonunitIsRankTwo Phase3.phase2 midMid = rankTwoTwoCycle
nonconstantNonunitIsRankTwo Phase3.phase0 highLow = rankTwoOneFixed
nonconstantNonunitIsRankTwo Phase3.phase1 highLow = rankTwoTwoCycle
nonconstantNonunitIsRankTwo Phase3.phase2 highLow = rankTwoTwoFixed
nonconstantNonunitIsRankTwo Phase3.phase0 highHigh = rankTwoTwoFixed
nonconstantNonunitIsRankTwo Phase3.phase1 highHigh = rankTwoTwoCycle
nonconstantNonunitIsRankTwo Phase3.phase2 highHigh = rankTwoOneFixed

record TernaryPhaseShapeIncidenceBoundary : Set where
  field
    completeTwentySevenIncidenceComputed : Bool
    completeTwentySevenIncidenceComputedIsTrue :
      completeTwentySevenIncidenceComputed ≡ true
    phaseSevenIdentifiedWithShapeSeven : Bool
    phaseSevenIdentifiedWithShapeSevenIsFalse :
      phaseSevenIdentifiedWithShapeSeven ≡ false
    quotientPairTreatedAsIndependentProductOfSixtyThreeStates : Bool
    quotientPairTreatedAsIndependentProductOfSixtyThreeStatesIsFalse :
      quotientPairTreatedAsIndependentProductOfSixtyThreeStates ≡ false

canonicalTernaryPhaseShapeIncidenceBoundary :
  TernaryPhaseShapeIncidenceBoundary
canonicalTernaryPhaseShapeIncidenceBoundary =
  record
    { completeTwentySevenIncidenceComputed = true
    ; completeTwentySevenIncidenceComputedIsTrue = refl
    ; phaseSevenIdentifiedWithShapeSeven = false
    ; phaseSevenIdentifiedWithShapeSevenIsFalse = refl
    ; quotientPairTreatedAsIndependentProductOfSixtyThreeStates = false
    ; quotientPairTreatedAsIndependentProductOfSixtyThreeStatesIsFalse = refl
    }
