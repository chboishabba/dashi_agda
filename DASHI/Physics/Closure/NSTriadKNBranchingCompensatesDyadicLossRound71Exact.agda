module DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Ruilin Hu; Phuoc-Tai Nguyen; Quoc-Hung Nguyen; Ping Zhang.
-- Title: "Quantitative bounds for bounded solutions to the Navier-Stokes
-- equations in endpoint critical Besov spaces".
-- arXiv DOI: 10.48550/arXiv.2411.06483.
--
-- ROUND 71 / BRANCHING CAN COMPENSATE PROPAGATION LOSS
--
-- Round70 proved that ONE event per depth with floor 2^(-j) is summable and
-- therefore cannot contradict a fixed finite funding budget.  That no-go does
-- NOT imply that dyadic per-event loss itself is fatal.  Multiplicity matters.
--
-- This file constructs an exact finite branching model on the same Round70
-- funding carrier.  Start with one unit floor.  At every depth duplicate the
-- entire event-floor block and halve every floor.  Thus the event count doubles
-- while each descendant floor halves.  The TOTAL guaranteed floor is exactly
-- preserved at every depth.
--
-- More generally, scaling the block by any rational weight W gives total floor
-- exactly W at every depth.  Choosing W = E+1 therefore produces, for EVERY
-- finite rational budget E, a finite depth-j floor block whose cumulative
-- required charge is E+1>E, even though its individual descendants have been
-- repeatedly halved.
--
-- Mathematical consequence for the physical propagation theorem:
--
--   viability is controlled by
--
--       branching multiplicity  x  per-event charge floor,
--
--   not by the per-event floor alone.  A future NS propagation theorem may
--   survive exponential pointwise loss if it simultaneously produces enough
--   genuinely separated/non-duplicated physical descendants.  Conversely,
--   Round70 still forbids counting formal duplicates as new funded events.
--
-- No claim is made here that Navier-Stokes actually supplies this branching.
-- The new physical target is to prove a SAME-OBJECT descendant multiplicity /
-- separation theorem on the selected localized trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding

appendFloors : List ℚ → List ℚ → List ℚ
appendFloors [] right = right
appendFloors (x ∷ xs) right = x ∷ appendFloors xs right

scaleFloors : ℚ → List ℚ → List ℚ
scaleFloors scalar [] = []
scaleFloors scalar (x ∷ xs) =
  scalar * x ∷ scaleFloors scalar xs

sumAppendFloors : ∀ left right →
  Funding.sumFloors (appendFloors left right)
  ≡ Funding.sumFloors left + Funding.sumFloors right
sumAppendFloors [] right =
  sym (ℚP.+-identityˡ (Funding.sumFloors right))
sumAppendFloors (x ∷ xs) right =
  trans
    (cong (x +_) (sumAppendFloors xs right))
    (sym
      (ℚP.+-assoc
        x (Funding.sumFloors xs) (Funding.sumFloors right)))

sumScaleFloors : ∀ scalar floors →
  Funding.sumFloors (scaleFloors scalar floors)
  ≡ scalar * Funding.sumFloors floors
sumScaleFloors scalar [] = solve (scalar ∷ [])
sumScaleFloors scalar (x ∷ xs)
  rewrite sumScaleFloors scalar xs =
  solve (scalar ∷ x ∷ Funding.sumFloors xs ∷ [])

-- Recursive doubling is the exact constructive stand-in for 2^depth copies.
dyadicMultiplicity : Nat → Nat
dyadicMultiplicity zero = 1
dyadicMultiplicity (suc depth) =
  dyadicMultiplicity depth + dyadicMultiplicity depth

floorCount : List ℚ → Nat
floorCount [] = zero
floorCount (x ∷ xs) = suc (floorCount xs)

floorCountAppend : ∀ left right →
  floorCount (appendFloors left right)
  ≡ floorCount left + floorCount right
floorCountAppend [] right = refl
floorCountAppend (x ∷ xs) right
  rewrite floorCountAppend xs right = refl

floorCountScale : ∀ scalar floors →
  floorCount (scaleFloors scalar floors) ≡ floorCount floors
floorCountScale scalar [] = refl
floorCountScale scalar (x ∷ xs)
  rewrite floorCountScale scalar xs = refl

-- One unit event at depth zero.  Each propagation step duplicates the block and
-- halves every descendant floor.
dyadicBranchBlock : Nat → List ℚ
dyadicBranchBlock zero = 1ℚ ∷ []
dyadicBranchBlock (suc depth) =
  let halfBlock = scaleFloors Scale.half (dyadicBranchBlock depth)
  in appendFloors halfBlock halfBlock

dyadicBranchBlockCountExact : ∀ depth →
  floorCount (dyadicBranchBlock depth) ≡ dyadicMultiplicity depth
dyadicBranchBlockCountExact zero = refl
dyadicBranchBlockCountExact (suc depth)
  rewrite floorCountAppend
            (scaleFloors Scale.half (dyadicBranchBlock depth))
            (scaleFloors Scale.half (dyadicBranchBlock depth))
        | floorCountScale Scale.half (dyadicBranchBlock depth)
        | dyadicBranchBlockCountExact depth = refl

halfPlusHalfIsOne : Scale.half + Scale.half ≡ 1ℚ
halfPlusHalfIsOne = solve []

-- The key exact conservation law: doubling multiplicity exactly compensates
-- halving the per-descendant guaranteed floor.
dyadicBranchBlockMassExact : ∀ depth →
  Funding.sumFloors (dyadicBranchBlock depth) ≡ 1ℚ
dyadicBranchBlockMassExact zero = solve []
dyadicBranchBlockMassExact (suc depth) =
  let
    oldMass = Funding.sumFloors (dyadicBranchBlock depth)

    expanded :
      Funding.sumFloors (dyadicBranchBlock (suc depth))
      ≡ Scale.half * oldMass + Scale.half * oldMass
    expanded =
      trans
        (sumAppendFloors
          (scaleFloors Scale.half (dyadicBranchBlock depth))
          (scaleFloors Scale.half (dyadicBranchBlock depth)))
        (cong₂ _+_
          (sumScaleFloors Scale.half (dyadicBranchBlock depth))
          (sumScaleFloors Scale.half (dyadicBranchBlock depth)))
  in
  trans expanded
    (trans
      (cong
        (λ mass → Scale.half * mass + Scale.half * mass)
        (dyadicBranchBlockMassExact depth))
      (solve []))
  where
  open import Relation.Binary.PropositionalEquality using (cong₂)

weightedDyadicBranchBlock : ℚ → Nat → List ℚ
weightedDyadicBranchBlock weight depth =
  scaleFloors weight (dyadicBranchBlock depth)

weightedDyadicBranchBlockMassExact : ∀ weight depth →
  Funding.sumFloors (weightedDyadicBranchBlock weight depth) ≡ weight
weightedDyadicBranchBlockMassExact weight depth =
  trans
    (sumScaleFloors weight (dyadicBranchBlock depth))
    (trans
      (cong (weight *_) (dyadicBranchBlockMassExact depth))
      (ℚP.*-identityʳ weight))

budgetStrictlyBelowBudgetPlusOne : ∀ energy → energy < energy + 1ℚ
budgetStrictlyBelowBudgetPlusOne energy =
  let
    zeroLessOne : 0ℚ < 1ℚ
    zeroLessOne = ℚP.positive⁻¹ 1ℚ
    shifted : energy + 0ℚ < energy + 1ℚ
    shifted = ℚP.+-monoˡ-< energy zeroLessOne
  in
  subst
    (λ left → left < energy + 1ℚ)
    (ℚP.+-identityʳ energy)
    shifted

weightedBudgetPlusOneBlockOutrunsBudget : ∀ energy depth →
  energy
  < Funding.sumFloors
      (weightedDyadicBranchBlock (energy + 1ℚ) depth)
weightedBudgetPlusOneBlockOutrunsBudget energy depth =
  subst
    (energy <_)
    (sym (weightedDyadicBranchBlockMassExact (energy + 1ℚ) depth))
    (budgetStrictlyBelowBudgetPlusOne energy)

-- At every finite depth, no event ledger can simultaneously meet these floors
-- and fit inside energy E.  This uses the already-constructed Round70 exact
-- scale-dependent funding theorem.
weightedBudgetPlusOneBlockRejectsAnyFunding :
  ∀ energy depth events →
  ¬ Funding.ScaleDependentConcentrationBudget
      energy
      (weightedDyadicBranchBlock (energy + 1ℚ) depth)
      events
weightedBudgetPlusOneBlockRejectsAnyFunding energy depth events =
  Funding.prefixFloorAboveEnergyContradictsBudget
    (weightedBudgetPlusOneBlockOutrunsBudget energy depth)

round71BranchingCompensatesDyadicPerEventLoss : Bool
round71BranchingCompensatesDyadicPerEventLoss = true

round71MultiplicityMustBePhysicalAndDuplicateFree : Bool
round71MultiplicityMustBePhysicalAndDuplicateFree = true

round71PhysicalNSBranchingMultiplicityConstructed : Bool
round71PhysicalNSBranchingMultiplicityConstructed = false

round71BranchingCompensatesDyadicPerEventLossIsTrue :
  round71BranchingCompensatesDyadicPerEventLoss ≡ true
round71BranchingCompensatesDyadicPerEventLossIsTrue = refl

round71PhysicalNSBranchingMultiplicityConstructedIsFalse :
  round71PhysicalNSBranchingMultiplicityConstructed ≡ false
round71PhysicalNSBranchingMultiplicityConstructedIsFalse = refl
