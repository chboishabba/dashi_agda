{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017HeterogeneousRateExact where

-- P01: ALL-SITE HETEROGENEOUS robustness, in the original exact
-- natural-number cross-multiplied Born-ratio coordinate convention.
--
-- Unlike a fixed (25/9)^k example, independent surviving sites can have
-- different right and wrong calibrated raw Born masses. Requiring EVERY
-- site to give at least a factor-two advantage proves a factor 2^k
-- advantage for k surviving sites, with no constant-site assumption.
-- This specializes to the earlier 25/9 proof and is sharp at k=0.
--
-- The required site-by-site certificates are real mathematical inputs,
-- not claims derived from an arbitrary physical environment. Attaching
-- these Nat masses to the genuine complex tensor model, including scale
-- normalization and the selected 2017 dynamics, remains a separate gate.
-- Original owners: TSVF2017QuantitativeRateExact and
-- TSVFAdmissibleQuantumOverlapRobustnessExact; same published 2017 source.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Quantum.TSVF2017QuantitativeRateExact as Rate
import DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact as Finite

record CalibratedSite : Set where
  constructor calibratedSite
  field
    rightRaw wrongRaw : Nat
    atLeastTwoToOne : 2 * wrongRaw ≤ rightRaw

open CalibratedSite public

length : List CalibratedSite → Nat
length [] = zero
length (_ ∷ ss) = suc (length ss)

rightProduct : List CalibratedSite → Nat
rightProduct [] = 1
rightProduct (s ∷ ss) = rightRaw s * rightProduct ss

wrongProduct : List CalibratedSite → Nat
wrongProduct [] = 1
wrongProduct (s ∷ ss) = wrongRaw s * wrongProduct ss

-- No site homogeneity is used anywhere in this induction.
heterogeneousExponentialRate :
  (ss : List CalibratedSite) →
  Finite.power 2 (length ss) * wrongProduct ss ≤ rightProduct ss
heterogeneousExponentialRate [] = ℕₚ.≤-refl
heterogeneousExponentialRate (s ∷ ss)
  rewrite Finite.tensorRearrange
    2 (Finite.power 2 (length ss)) (wrongRaw s) (wrongProduct ss) =
  ℕₚ.*-mono-≤
    (atLeastTwoToOne s)
    (heterogeneousExponentialRate ss)

weightedHeterogeneousRate :
  (gammaRight gammaWrong : Nat) (ss : List CalibratedSite) →
  gammaWrong ≤ gammaRight →
  Finite.power 2 (length ss) * (gammaWrong * wrongProduct ss)
    ≤ gammaRight * rightProduct ss
weightedHeterogeneousRate gammaRight gammaWrong ss gammaOrder
  rewrite Rate.swapTwoFactors
    (Finite.power 2 (length ss)) gammaWrong (wrongProduct ss) =
  ℕₚ.*-mono-≤ gammaOrder (heterogeneousExponentialRate ss)

weightedTotal : Nat → Nat → List CalibratedSite → Nat
weightedTotal gammaRight gammaWrong ss =
  gammaRight * rightProduct ss + gammaWrong * wrongProduct ss

-- For a STRICTLY POSITIVE selected total, this cross inequality is
-- precisely P_wrong <= 1/(2^k + 1). No fraction with zero denominator
-- is asserted to be an actual ABL probability.
heterogeneousWrongProbabilityCrossBound :
  (gammaRight gammaWrong : Nat) (ss : List CalibratedSite) →
  gammaWrong ≤ gammaRight →
  (Finite.power 2 (length ss) + 1)
    * (gammaWrong * wrongProduct ss)
  ≤ weightedTotal gammaRight gammaWrong ss
heterogeneousWrongProbabilityCrossBound gammaRight gammaWrong ss order
  rewrite ℕₚ.*-distribʳ-+
    (Finite.power 2 (length ss)) 1 (gammaWrong * wrongProduct ss)
        | ℕₚ.*-identityˡ (gammaWrong * wrongProduct ss) =
  ℕₚ.+-mono-≤
    (weightedHeterogeneousRate gammaRight gammaWrong ss order)
    ℕₚ.≤-refl

------------------------------------------------------------------------
-- Regression bridge: the original 25:9 site is one concrete inhabitant.
-- No claim that arbitrary physical complex gammas satisfy the calibration.
------------------------------------------------------------------------

originalTwentyFiveNineSite : CalibratedSite
originalTwentyFiveNineSite =
  calibratedSite 25 9 Rate.eighteenAtMost25

replicate : CalibratedSite → Nat → List CalibratedSite
replicate s zero = []
replicate s (suc k) = s ∷ replicate s k

repeatLength : (s : CalibratedSite) (k : Nat) →
  length (replicate s k) ≡ k
repeatLength s zero = refl
repeatLength s (suc k) = cong suc (repeatLength s k)

repeatRightProduct : (s : CalibratedSite) (k : Nat) →
  rightProduct (replicate s k) ≡ Finite.power (rightRaw s) k
repeatRightProduct s zero = refl
repeatRightProduct s (suc k) =
  cong (λ v → rightRaw s * v) (repeatRightProduct s k)

repeatWrongProduct : (s : CalibratedSite) (k : Nat) →
  wrongProduct (replicate s k) ≡ Finite.power (wrongRaw s) k
repeatWrongProduct s zero = refl
repeatWrongProduct s (suc k) =
  cong (λ v → wrongRaw s * v) (repeatWrongProduct s k)

-- Thus the earlier uniform 25/9 case is a theorem instance, not a
-- contradictory second definition of environmental robustness.
originalRightProductRecovered : (k : Nat) →
  rightProduct (replicate originalTwentyFiveNineSite k)
    ≡ Finite.rightRaw k
originalRightProductRecovered = repeatRightProduct originalTwentyFiveNineSite

originalWrongProductRecovered : (k : Nat) →
  wrongProduct (replicate originalTwentyFiveNineSite k)
    ≡ Finite.wrongRaw k
originalWrongProductRecovered = repeatWrongProduct originalTwentyFiveNineSite
