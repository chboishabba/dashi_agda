{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR445LocalizedTVInferenceNoGoExact where

------------------------------------------------------------------------
-- ORIGINAL R445 MAXIMUM-CUT LOGICAL AUDIT: THREE EXACT FINITE
-- COUNTERMODELS TO PROPOSED *IMPLICATIONS*, NOT TO YANG--MILLS.
--
-- This file deliberately has no YM physical input and is NOT an
-- original Wilson action counterexample. It proves that the three
-- deduction rules in the new R445 proposal are NOT generally valid.
--
-- [1] Spatial block ratio 1/4 with exponent 2 at EACH step does not
--     automatically become (1/4)^(2k). Already at k=2,
--           4^2=16, 4^(2*2)=256.
--
-- [2] If Q has correlated interior/exterior variables, a perturbation
--     of the EXTERIOR weight alone changes its INTERIOR marginal,
--     even though the perturbing term never touches interior X.
--     Q(x,y) has integer weights (3,1,1,3)/8, and w(y)=(1,3).
--     Then P_X=(6,10)/16=(3/8,5/8) while Q_X=(4,4)/8.
--     So the naive "sum only polymer terms intersecting X" formula
--     requires conditional-decoupling or influence estimates.
--
-- [3] TV(P_X,Q_X)=0 at every volume does NOT force either P or Q
--     to cluster. Take P=Q supported equally on the all-zero and
--     all-one configurations on arbitrarily separated sites.
--     E[X]=E[Y]=1/2, E[XY]=1/2, Cov(X,Y)=1/4.
--     Four times the covariance is exactly 2*1-1*1=1, independent
--     of the separation.
--
-- These are Agda --safe, postulate-free finite arithmetic receipts.
-- Agda 2.9 pinned kernel execution is still required. The physical
-- R445 F19/P0 Wilson conditional TV estimate, cutoff summability,
-- RG clustering, E1/D1/D2 remain OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_∸_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

-- A fixed single-step (1/4)^2 factor is 1/16, NOT 16^(-k).
singleStepDenominator : 4 * 4 ≡ 16
singleStepDenominator = refl

inventedSecondStepDenominator : 4 * 4 * 4 * 4 ≡ 256
inventedSecondStepDenominator = refl

secondStepExtrapolationIsFalse : 16 ≡ 256 → Empty
secondStepExtrapolationIsFalse ()

-- Literal Q(x,y) joint mass table scaled by 8, in ordering
-- (0,0),(0,1),(1,0),(1,1).
data Spin : Set where
  low high : Spin

originalCorrelatedQMass8 : Spin → Spin → Nat
originalCorrelatedQMass8 low  low  = 3
originalCorrelatedQMass8 low  high = 1
originalCorrelatedQMass8 high low  = 1
originalCorrelatedQMass8 high high = 3

-- The perturbation is ONLY a function of the exterior spin y.
outsideWeight : Spin → Nat
outsideWeight low = 1
outsideWeight high = 3

outsideOnlyQTotal8 : Nat
outsideOnlyQTotal8 =
  originalCorrelatedQMass8 low low
  + originalCorrelatedQMass8 low high
  + originalCorrelatedQMass8 high low
  + originalCorrelatedQMass8 high high

outsideOnlyPTotalUnnormalised8 : Nat
outsideOnlyPTotalUnnormalised8 =
  originalCorrelatedQMass8 low low * outsideWeight low
  + originalCorrelatedQMass8 low high * outsideWeight high
  + originalCorrelatedQMass8 high low * outsideWeight low
  + originalCorrelatedQMass8 high high * outsideWeight high

outsideOnlyTotalQ8 : outsideOnlyQTotal8 ≡ 8
outsideOnlyTotalQ8 = refl

outsideOnlyTotalWeightedQ8 : outsideOnlyPTotalUnnormalised8 ≡ 16
outsideOnlyTotalWeightedQ8 = refl

outsideOnlyOriginalInterior0MassQ8 : Nat
outsideOnlyOriginalInterior0MassQ8 =
  originalCorrelatedQMass8 low low + originalCorrelatedQMass8 low high

outsideOnlyPerturbedInterior0MassP16 : Nat
outsideOnlyPerturbedInterior0MassP16 =
  originalCorrelatedQMass8 low low * outsideWeight low
  + originalCorrelatedQMass8 low high * outsideWeight high

outsideOnlyOriginalInterior0IsFour :
  outsideOnlyOriginalInterior0MassQ8 ≡ 4
outsideOnlyOriginalInterior0IsFour = refl

outsideOnlyPerturbedInterior0IsSix :
  outsideOnlyPerturbedInterior0MassP16 ≡ 6
outsideOnlyPerturbedInterior0IsSix = refl

-- P_X(low)=6/16, Q_X(low)=4/8. They are different.
-- No reference to any varying-in-X action is involved.
exteriorOnlyChangeOfInteriorMarginal :
  (outsideOnlyPerturbedInterior0MassP16
    * outsideOnlyQTotal8)
  ≡
  (outsideOnlyOriginalInterior0MassQ8
    * outsideOnlyPTotalUnnormalised8)
  → Empty
exteriorOnlyChangeOfInteriorMarginal ()

-- A distance-parametric positively correlated common measure P=Q.
-- The two jointly observed sites may be separated by ANY distance.
-- Its two equally weighted atoms are (low,low),(high,high).
bitValue : Spin → Nat
bitValue low = zero
bitValue high = suc zero

synchronousLeftMass2 : Nat → Nat
synchronousLeftMass2 distance =
  bitValue low + bitValue high

synchronousRightMass2 : Nat → Nat
synchronousRightMass2 distance =
  bitValue low + bitValue high

synchronousProductMass2 : Nat → Nat
synchronousProductMass2 distance =
  bitValue low * bitValue low
  + bitValue high * bitValue high

-- Four times actual Cov = 2*sum(FG)-sum(F)*sum(G) = 1.
-- The numerator is independent of the distance.
fourTimesSynchronousCovarianceIsOne :
  (distance : Nat) →
  ((2 * synchronousProductMass2 distance)
    ∸
    (synchronousLeftMass2 distance
      * synchronousRightMass2 distance)) ≡ 1
fourTimesSynchronousCovarianceIsOne distance = refl

-- If both source measures are literally the same two-atom law,
-- every local TV discrepancy is zero while the covariance above
-- remains exactly 1/4 at arbitrary separation.
identicalProbabilitiesHaveZeroTVNumerator :
  (distance : Nat) →
  (synchronousProductMass2 distance
    ∸ synchronousProductMass2 distance) ≡ zero
identicalProbabilitiesHaveZeroTVNumerator distance = refl
