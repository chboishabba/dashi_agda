module DASHI.Analysis.NonArchimedeanPowerOrbitSumBidiExact where

------------------------------------------------------------------------
-- POWER-ORBIT SUM CUTSET
--
-- Let L = 2^(n-2) and C1 = {3^j | 0 <= j < L}.  The geometric identity
--
--   2 * sum_{j<L} 3^j = 3^L - 1
--
-- shows why the order theorem modulo 2^n is not by itself enough to recover
-- the sum modulo 2^n: division by two costs one dyadic bit.  The exact producer
-- required is the lifted congruence
--
--   3^L = 1 + 2^n  (mod 2^(n+1)),
--
-- which compiles to
--
--   sum C1 = 2^(n-1)  (mod 2^n).
--
-- The module keeps that one-bit strengthening separate from the already-owned
-- order theorem so proof search does not accidentally treat order as an orbit
-- phase theorem.
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
    geometricSeriesIdentityReusable : Bool
    liftedCongruenceOneExtraBitRequired : Bool
    orbitSumHalfPeriodCompilesFromLiftedCongruence : Bool

canonicalPowerOrbitSumStatus : PowerOrbitSumStatus
canonicalPowerOrbitSumStatus =
  powerOrbitSumStatus true false true true true


data OrbitSumLeaf : Set where
  proveLiftedThreePowerCongruence : OrbitSumLeaf
  reuseGeometricSeriesIdentity : OrbitSumLeaf
  compileOrbitSumHalfPeriod : OrbitSumLeaf
  reuseOrderTheoremAsOrbitSum : OrbitSumLeaf


data OrbitSumDisposition : Set where
  live : OrbitSumDisposition
  reusable : OrbitSumDisposition
  downstream : OrbitSumDisposition
  forbiddenShortcut : OrbitSumDisposition

leafDisposition : OrbitSumLeaf → OrbitSumDisposition
leafDisposition proveLiftedThreePowerCongruence = live
leafDisposition reuseGeometricSeriesIdentity = reusable
leafDisposition compileOrbitSumHalfPeriod = downstream
leafDisposition reuseOrderTheoremAsOrbitSum = forbiddenShortcut

highestAlphaOrbitSumPath : List OrbitSumLeaf
highestAlphaOrbitSumPath =
  proveLiftedThreePowerCongruence ∷
  reuseGeometricSeriesIdentity ∷
  compileOrbitSumHalfPeriod ∷
  []

orderTheoremCannotPayForLostDyadicBit :
  PowerOrbitSumStatus.orderTheoremAloneSupportsDivisionByTwo
    canonicalPowerOrbitSumStatus
  ≡ false
orderTheoremCannotPayForLostDyadicBit = refl
