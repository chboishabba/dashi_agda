module DASHI.Physics.Closure.NSTriadKNGate2FactorRouteArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_*_)
open import Data.Nat.Properties as NatP using (≤-refl; m≤m+n; *-mono-≤)
open import DASHI.Physics.Closure.DirectionalFactorTransportBase
  using (DirectionalFactorTransportModel; mkDirectionalFactorTransportModel)
open import DASHI.Physics.Closure.ExactKNAFactorRouteBase
  using (ExactKNAFactorRouteModel; mkExactKNAFactorRouteModel)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance
  using (NatOrderedMonoid)

----------------------------------------------------------------------
-- Concrete arithmetic inhabitant of the exact K_N(A) factor-route kernel.
--
-- This is the simplest end-to-end witness of the live theorem shape:
--
--   directional-factor = 1
--   coarse-factor      = 2
--   seam-rayleigh      = 3
--   transported        = 3
--   coarse-transport   = 6
--   quarter-threshold  = 12
--
-- so the directional route is smaller than the coarse route, and the exact
-- K_N(A) ratio closes once identified with the directional transport.

1# : Nat
1# = suc 0

2# : Nat
2# = suc 1#

3# : Nat
3# = suc 2#

6# : Nat
6# = suc (suc (suc 3#))

12# : Nat
12# = suc (suc (suc (suc (suc (suc 6#)))))

canonicalDirectionalFactorTransportModel :
  DirectionalFactorTransportModel
canonicalDirectionalFactorTransportModel =
  mkDirectionalFactorTransportModel
    NatOrderedMonoid
    _*_
    3#
    1#
    2#
    3#
    6#
    refl
    refl
    NatP.m≤m+n 1# 1#
    (λ a b c d a≤b c≤d → NatP.*-mono-≤ a≤b c≤d)

canonicalExactKNAFactorRouteModel :
  ExactKNAFactorRouteModel
canonicalExactKNAFactorRouteModel =
  mkExactKNAFactorRouteModel
    canonicalDirectionalFactorTransportModel
    3#
    12#
    refl
    (NatP.m≤m+n 6# 6#)

canonicalExactKNAFactorRouteBound :
  ExactKNAFactorRouteModel._≤_
    canonicalExactKNAFactorRouteModel
    (ExactKNAFactorRouteModel.exact-kna-ratio
      canonicalExactKNAFactorRouteModel)
    (ExactKNAFactorRouteModel.quarter-threshold
      canonicalExactKNAFactorRouteModel)
canonicalExactKNAFactorRouteBound =
  ExactKNAFactorRouteModel.exactKNA≤quarter
    canonicalExactKNAFactorRouteModel
