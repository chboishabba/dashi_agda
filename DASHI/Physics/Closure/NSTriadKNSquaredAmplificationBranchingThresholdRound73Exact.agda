module DASHI.Physics.Closure.NSTriadKNSquaredAmplificationBranchingThresholdRound73Exact where

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
-- ROUND73 / AMPLITUDE LOSS MUST BE SQUARED BEFORE FUNDING
--
-- Round71's first branching model treated the propagated quantity itself as a
-- charge floor: binary branching exactly compensates a per-event 1/2 floor.
-- After Round73 normalization the derived physical floor is instead mu^2.
-- Therefore a 1/2 loss in AMPLITUDE produces a 1/4 loss in charge.
--
-- This file makes that distinction exact.  The dyadic amplitude
--
--      mu_{j+1} = (1/2) mu_j
--
-- satisfies
--
--      mu_{j+1}^2 = (1/4) mu_j^2.
--
-- Reusing the already-proved Round72 four-way 1/4-loss block then gives the
-- exact critical multiplicity threshold: four genuine descendants per step
-- preserve one unit of total squared-amplification floor.
--
-- Thus binary branching is insufficient for a half-amplitude propagation
-- loss once the concentration charge is quadratic.  No claim is made that the
-- Navier--Stokes propagation theorem supplies four physical descendants.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNPolynomialComplexityMultiplicityThresholdRound72Exact as Threshold
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding

halfAmplitude : Nat → ℚ
halfAmplitude zero = 1ℚ
halfAmplitude (suc depth) = Scale.half * halfAmplitude depth

halfAmplitudeSuccessor : ∀ depth →
  halfAmplitude (suc depth) ≡ Scale.half * halfAmplitude depth
halfAmplitudeSuccessor depth = refl

halfAmplitudeSquareSuccessor : ∀ depth →
  L2.square (halfAmplitude (suc depth))
  ≡ Threshold.quarter * L2.square (halfAmplitude depth)
halfAmplitudeSquareSuccessor depth = solve (halfAmplitude depth ∷ [])

fourWaySquaredAmplitudeFloorBlock : Nat → Agda.Builtin.List.List ℚ
fourWaySquaredAmplitudeFloorBlock = Threshold.quadraticComplexityBranchBlock

fourWaySquaredAmplitudeFloorMassExact : ∀ depth →
  Funding.sumFloors (fourWaySquaredAmplitudeFloorBlock depth) ≡ 1ℚ
fourWaySquaredAmplitudeFloorMassExact = Threshold.quadraticBranchMassExact

fourWaySquaredAmplitudeFloorCountExact : ∀ depth →
  DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact.floorCount
    (fourWaySquaredAmplitudeFloorBlock depth)
  ≡ Threshold.quadrupleMultiplicity depth
fourWaySquaredAmplitudeFloorCountExact = Threshold.quadraticBranchCountExact

round73HalfAmplitudeMeansQuarterChargeFloor : Bool
round73HalfAmplitudeMeansQuarterChargeFloor = true

round73FourWayMultiplicityIsCriticalForHalfAmplitudeLoss : Bool
round73FourWayMultiplicityIsCriticalForHalfAmplitudeLoss = true

round73BinaryMultiplicitySufficesForHalfAmplitudeLoss : Bool
round73BinaryMultiplicitySufficesForHalfAmplitudeLoss = false

round73PhysicalFourWayDescendantsConstructed : Bool
round73PhysicalFourWayDescendantsConstructed = false

round73HalfAmplitudeMeansQuarterChargeFloorIsTrue :
  round73HalfAmplitudeMeansQuarterChargeFloor ≡ true
round73HalfAmplitudeMeansQuarterChargeFloorIsTrue = refl

round73BinaryMultiplicitySufficesForHalfAmplitudeLossIsFalse :
  round73BinaryMultiplicitySufficesForHalfAmplitudeLoss ≡ false
round73BinaryMultiplicitySufficesForHalfAmplitudeLossIsFalse = refl
