module DASHI.Unified.HyperfabricK27SU2LevelFourOriginalSourceCutExact where

-- Reuse the PREEXISTING original k=4 SU(2) integrable WZW
-- primary-owner theorem data. No generic "new CFT" construction.
-- Standard Sugawara:
--   c_SU2(k) = 3k/(k+2); k=4 => c=2.
--   h_j = j(j+1)/(k+2), j=2 => h=1.
-- 26D bosonic string candidate:
--   22 ordinary flat scalars + 1 linear-dilaton scalar (c=2)
--   + SU2_4 WZW (c=2) = 26 matter central charge.
-- The actual VOA states, target S3 flux gerbe and BRST still
-- belong to their other source owners. This is SOURCE arithmetic.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Physics.QFT.SU2Level4Spin1RepReceipt as Original
import DASHI.Physics.QFT.KacMoodyLevelReceipt as Levels

originalLevelFourIsFour : Original.su2Level4 ≡ 4
originalLevelFourIsFour = refl

originalHighestWeightJTwo : Original.doubledSpin Original.j2Rep ≡ 4
originalHighestWeightJTwo = refl

-- The existing source has exactly h_(j=2)=24/24=1.
originalJTwoWeightNumeratorEqualsDenominator :
  Original.wzwConformalWeightNumerator Original.j2Rep
    ≡ Original.wzwConformalWeightDenominator
originalJTwoWeightNumeratorEqualsDenominator = refl

wzwKFourCentralChargeNumerator : Nat
wzwKFourCentralChargeNumerator = 3 * 4

wzwKFourCentralChargeDenominator : Nat
wzwKFourCentralChargeDenominator = 4 + 2

wzwKFourCIsTwo :
  wzwKFourCentralChargeNumerator ≡ 2 * wzwKFourCentralChargeDenominator
wzwKFourCIsTwo = refl

-- A spacelike linear-dilaton charge alphaPrime*V²=1/(k+2)=1/6
-- gives c_(one boson) = 1+6*(1/6)=2.
-- Keep coefficient equality on natural numerator/denominator, no
-- Agda proof term is asserted for constructing the quantum boson VOA.
selectedOneBosonBackgroundChargeC : Nat
selectedOneBosonBackgroundChargeC = 2

selectedTwentyTwoFlatScalarC : Nat
selectedTwentyTwoFlatScalarC = 22

selectedKFourCriticalMatter :
  selectedTwentyTwoFlatScalarC
  + selectedOneBosonBackgroundChargeC
  + 2
  ≡ 26
selectedKFourCriticalMatter = refl

-- Do not equate k4 with the separately sourced conductor-three k3
-- or the 3-state signed-neutral C3 rotation.
