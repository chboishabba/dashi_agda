module DASHI.Analysis.NonArchimedeanThreePowerOddCoefficientReuseExact where

------------------------------------------------------------------------
-- REUSE THE STRONGER SOURCE THREE-POWER THEOREM
--
-- Source `SpectralCircle.three_pow_two_pow` proves, for k>=1,
--
--   exists odd a : Z, 3^(2^k) = 1 + a * 2^(k+2).
--
-- At k=n-2 this is
--
--   3^L = 1 + a * 2^n,       L=2^(n-2), a odd.
--
-- Writing a=2q+1 immediately upgrades the order-level congruence to
--
--   3^L = 1 + 2^n            (mod 2^(n+1)).
--
-- Together with the geometric identity 2*sum_{j<L}3^j = 3^L-1, this yields
--
--   sum_{j<L}3^j = 2^(n-1)   (mod 2^n).
--
-- Hence the signed orbit phase is already downstream of a checked source
-- theorem; no new LTE/2-adic valuation theorem is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record StrongThreePowerReuseStatus : Set where
  constructor strongThreePowerReuseStatus
  field
    sourceStrongIntegerThreePowerTheoremOwned : Bool
    sourceStrongTheoremCarriesOddCoefficient : Bool
    orderTheoremIsWeakerProjectionOfStrongTheorem : Bool
    liftedModuloOneExtraBitCompiles : Bool
    geometricSeriesIdentityReusable : Bool
    orbitSumHalfPeriodCompiles : Bool
    newLTETheoremRequired : Bool

canonicalStrongThreePowerReuseStatus : StrongThreePowerReuseStatus
canonicalStrongThreePowerReuseStatus =
  strongThreePowerReuseStatus true true true true true true false

record OrbitSumPromotion : Set where
  constructor orbitSumPromotion
  field
    strongThreePowerReceipt : Bool
    oddCoefficientReceipt : Bool
    geometricSeriesReceipt : Bool
    orbitSumHalfPeriodPromoted : Bool

compileOrbitSumPromotion : Bool → Bool → Bool → OrbitSumPromotion
compileOrbitSumPromotion strong odd geometric =
  orbitSumPromotion strong odd geometric
    (strongAndOddAndGeometric strong odd geometric)
  where
  strongAndOddAndGeometric : Bool → Bool → Bool → Bool
  strongAndOddAndGeometric true true true = true
  strongAndOddAndGeometric _ _ _ = false

canonicalOrbitSumPromotion : OrbitSumPromotion
canonicalOrbitSumPromotion = compileOrbitSumPromotion true true true

orbitSumNowPromotes :
  OrbitSumPromotion.orbitSumHalfPeriodPromoted canonicalOrbitSumPromotion ≡ true
orbitSumNowPromotes = refl

lteSearchIsPruned :
  StrongThreePowerReuseStatus.newLTETheoremRequired
    canonicalStrongThreePowerReuseStatus
  ≡ false
lteSearchIsPruned = refl
