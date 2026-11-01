module DASHI.Physics.Closure.NSTriadKNDavisKahanClusterGapRound80Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Chandler Davis; W. M. Kahan.
-- Title: "The Rotation of Eigenvectors by a Perturbation. III".
-- SIAM Journal on Numerical Analysis 7 (1970), 1--46.
-- DOI: 10.1137/0707001.
--
-- Authors: Yi Yu; Tengyao Wang; Richard J. Samworth.
-- Title: "A useful variant of the Davis--Kahan theorem for statisticians".
-- Biometrika 102 (2015), 315--323.
-- DOI: 10.1093/biomet/asv008.
--
-- Authors: Moritz Jirak; Martin Wahl.
-- Title: "Perturbation bounds for eigenspaces under a relative gap condition".
-- Proceedings of the AMS 148 (2020), 479--494.
-- DOI: 10.1090/proc/14714.
--
-- ROUND80 / EXACT C4 PERTURBATION-THEORY BOUNDARY
--
-- Davis--Kahan is naturally a theorem about invariant SUBSPACES.  Written in
-- the division-free currency already adopted by Round79, its schematic core is
--
--   clusterGap * subspaceDistance <= perturbationSize.
--
-- Yu--Wang--Samworth reduce which spectrum must supply the separation; they do
-- not remove separation.  Jirak--Wahl replace an absolute-gap regime by a
-- relative-gap regime; they likewise retain a separation hypothesis.
--
-- This module formalizes the exact scalar logic needed by C4: a positive gap
-- converts a perturbation estimate into a rotation budget, while gap=0 makes
-- the cross-multiplied inequality vacuous for every nonnegative distance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

record ClusterProjectorPerturbationBudget : Set where
  constructor cluster-projector-perturbation-budget
  field
    clusterGap : ℚ
    subspaceDistance : ℚ
    perturbationSize : ℚ
    clusterGapNonnegative : 0ℚ ≤ clusterGap
    distanceNonnegative : 0ℚ ≤ subspaceDistance
    perturbationNonnegative : 0ℚ ≤ perturbationSize
    crossMultipliedSinThetaBound :
      clusterGap * subspaceDistance ≤ perturbationSize

open ClusterProjectorPerturbationBudget public

record RelativePerturbationBudget
    (datum : ClusterProjectorPerturbationBudget) : Set where
  constructor relative-perturbation-budget
  field
    rotationBudget : ℚ
    rotationBudgetNonnegative : 0ℚ ≤ rotationBudget
    perturbationFitsGap :
      perturbationSize datum ≤ rotationBudget * clusterGap datum

open RelativePerturbationBudget public

clusterDistanceFitsRotationBudget :
  (datum : ClusterProjectorPerturbationBudget) →
  (relative : RelativePerturbationBudget datum) →
  clusterGap datum * subspaceDistance datum
  ≤ rotationBudget relative * clusterGap datum
clusterDistanceFitsRotationBudget datum relative =
  ℚP.≤-trans
    (crossMultipliedSinThetaBound datum)
    (perturbationFitsGap relative)

zeroGapBoundIsVacuous :
  (distance perturbation : ℚ) →
  0ℚ ≤ perturbation →
  0ℚ * distance ≤ perturbation
zeroGapBoundIsVacuous distance perturbation perturbationNN =
  subst
    (_≤ perturbation)
    (sym zeroTimes)
    perturbationNN
  where
  zeroTimes : 0ℚ * distance ≡ 0ℚ
  zeroTimes = solve (distance ∷ [])

record PositiveClusterSeparation : Set where
  constructor positive-cluster-separation
  field
    gap : ℚ
    gapPositive : 0ℚ < gap

round80DavisKahanControlsSpectralSubspaces : Bool
round80DavisKahanControlsSpectralSubspaces = true

round80YuWangSamworthRemovesAllGapConditions : Bool
round80YuWangSamworthRemovesAllGapConditions = false

round80RelativeGapTheoryIsGapFree : Bool
round80RelativeGapTheoryIsGapFree = false

round80ProjectorC4StillNeedsClusterSeparationOrAlternativeInvariant : Bool
round80ProjectorC4StillNeedsClusterSeparationOrAlternativeInvariant = true

round80YuWangSamworthRemovesAllGapConditionsIsFalse :
  round80YuWangSamworthRemovesAllGapConditions ≡ false
round80YuWangSamworthRemovesAllGapConditionsIsFalse = refl
