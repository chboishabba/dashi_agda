module DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneWeightExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact scalar normalization for the selected CMP109 radius-one block.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- r = 1 gives L = 3 and L^4 = 81.  Consequently the printed site
-- coefficient L^{-4} is exactly 1/81.  This file keeps that arithmetic concrete
-- over the standard-library rational carrier.
------------------------------------------------------------------------

threeℚ eightyOneℚ oneOverEightyOneℚ : ℚ
threeℚ = + 3 / 1
eightyOneℚ = + 81 / 1
oneOverEightyOneℚ = + 1 / 81

radiusOneSiteWeightCancelsVolume : ∀ value →
  oneOverEightyOneℚ * (eightyOneℚ * value) ≡ value
radiusOneSiteWeightCancelsVolume = ℚRing.solve-∀

radiusOneVolumeCancelsSiteWeight : ∀ value →
  eightyOneℚ * (oneOverEightyOneℚ * value) ≡ value
radiusOneVolumeCancelsSiteWeight = ℚRing.solve-∀

radiusOneSiteWeightIsReciprocal :
  oneOverEightyOneℚ * eightyOneℚ ≡ 1ℚ
radiusOneSiteWeightIsReciprocal =
  radiusOneSiteWeightCancelsVolume 1ℚ

cmp109RadiusOneRationalWeightLevel : ProofLevel
cmp109RadiusOneRationalWeightLevel = machineChecked
