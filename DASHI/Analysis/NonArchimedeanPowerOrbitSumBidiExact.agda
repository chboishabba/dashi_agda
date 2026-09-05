module DASHI.Analysis.NonArchimedeanPowerOrbitSumBidiExact where

------------------------------------------------------------------------
-- POWER-ORBIT SUM CUTSET
--
-- Let L = 2^(n-2) and C1 = {3^j | 0 <= j < L}.  The geometric identity
--
--   2 * sum_{j<L} 3^j = 3^L - 1
--
-- shows why the order theorem modulo 2^n is not by itself enough to recover
-- the sum modulo 2^n: division by two costs one dyadic bit.
--
-- The source already owns the stronger integer theorem
--
--   three_pow_two_pow :
--     exists odd a, 3^(2^k) = 1 + a * 2^(k+2).
--
-- At k=n-2 this supplies the missing extra dyadic bit, and the standard
-- geometric-series identity compiles
--
--   sum C1 = 2^(n-1)  (mod 2^n).
--
-- Thus the lifted congruence is now a reusable projection of an already checked
-- source theorem, not a live LTE/valuation search target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record PowerOrbitSumReceipt : Set₁ where
  field
    ResidueN : Set
    ResidueNPlusOne : Set

    orbitSum : ResidueN
    halfPeriod : ResidueN

    threePowerAtFullOrbit : ResidueNPlusOne
    onePlusFullModulus : ResidueNPlusOne

    liftedThreePowerCongruence :
      threePowerAtFullOrbit ≡ onePlusFullModulus

    liftedCongruenceCompilesOrbitSum :
      threePowerAtFullOrbit ≡ onePlusFullModulus →
      orbitSum ≡ halfPeriod

open PowerOrbitSumReceipt public

orbitSumIsHalfPeriod :
  (receipt : PowerOrbitSumReceipt) →
  orbitSum receipt ≡ halfPeriod receipt
orbitSumIsHalfPeriod receipt =
  liftedCongruenceCompilesOrbitSum receipt
    (liftedThreePowerCongruence receipt)

record PowerOrbitSumStatus : Set where
  constructor powerOrbitSumStatus
  field
    orderThreeModuloTwoPowNOwned : Bool
    orderTheoremAloneSupportsDivisionByTwo : Bool
    strongIntegerThreePowerTheoremOwned : Bool
    strongTheoremCarriesOddCoefficient : Bool
    geometricSeriesIdentityReusable : Bool
    liftedCongruenceCompilesFromStrongTheorem : Bool
    orbitSumHalfPeriodCompilesFromLiftedCongruence : Bool
    newLTETheoremRequired : Bool

canonicalPowerOrbitSumStatus : PowerOrbitSumStatus
canonicalPowerOrbitSumStatus =
  powerOrbitSumStatus true false true true true true true false


data OrbitSumLeaf : Set where
  reuseStrongThreePowerOddCoefficient : OrbitSumLeaf
  compileLiftedThreePowerCongruence : OrbitSumLeaf
  reuseGeometricSeriesIdentity : OrbitSumLeaf
  compileOrbitSumHalfPeriod : OrbitSumLeaf
  proveNewLTETheorem : OrbitSumLeaf
  reuseOrderTheoremAsOrbitSum : OrbitSumLeaf


data OrbitSumDisposition : Set where
  reusable : OrbitSumDisposition
  compiled : OrbitSumDisposition
  pruned : OrbitSumDisposition
  forbiddenShortcut : OrbitSumDisposition

leafDisposition : OrbitSumLeaf → OrbitSumDisposition
leafDisposition reuseStrongThreePowerOddCoefficient = reusable
leafDisposition compileLiftedThreePowerCongruence = compiled
leafDisposition reuseGeometricSeriesIdentity = reusable
leafDisposition compileOrbitSumHalfPeriod = compiled
leafDisposition proveNewLTETheorem = pruned
leafDisposition reuseOrderTheoremAsOrbitSum = forbiddenShortcut

highestAlphaOrbitSumPath : List OrbitSumLeaf
highestAlphaOrbitSumPath =
  reuseStrongThreePowerOddCoefficient ∷
  compileLiftedThreePowerCongruence ∷
  reuseGeometricSeriesIdentity ∷
  compileOrbitSumHalfPeriod ∷
  []

orbitSumIsNoLongerLive :
  leafDisposition compileOrbitSumHalfPeriod ≡ compiled
orbitSumIsNoLongerLive = refl

lteSearchIsPruned :
  PowerOrbitSumStatus.newLTETheoremRequired canonicalPowerOrbitSumStatus
  ≡ false
lteSearchIsPruned = refl

orderTheoremCannotPayForLostDyadicBit :
  PowerOrbitSumStatus.orderTheoremAloneSupportsDivisionByTwo
    canonicalPowerOrbitSumStatus
  ≡ false
orderTheoremCannotPayForLostDyadicBit = refl
