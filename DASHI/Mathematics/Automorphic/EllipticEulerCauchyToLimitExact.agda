module DASHI.Mathematics.Automorphic.EllipticEulerCauchyToLimitExact where

------------------------------------------------------------------------
-- BSD ANALYTIC ROAD: CAUCHY TRUNCATIONS -> CONSTRUCTIVE LIMIT
--
-- Bishop completeness is already machine-checked in-repo.  Therefore the
-- genuinely elliptic obligation is a Cauchy estimate for the literal Euler
-- truncation sequence; once supplied, existence of a constructive limit is
-- compiled rather than reproved or postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop

record EllipticEulerRealTruncation : Set₁ where
  field
    truncation : Nat → Bishop.Bishopℝ

open EllipticEulerRealTruncation public

record EllipticEulerCauchyReceipt
    (system : EllipticEulerRealTruncation) : Set₁ where
  field
    truncationsAreCauchy :
      Bishop.BishopCauchy (truncation system)

open EllipticEulerCauchyReceipt public

cauchyReceiptGivesConstructiveConvergence :
  ∀ {system} →
  EllipticEulerCauchyReceipt system →
  Bishop.BishopConvergent (truncation system)
cauchyReceiptGivesConstructiveConvergence receipt =
  Bishop.bishopCauchyComplete
    (truncationsAreCauchy receipt)

record EllipticEulerCauchyToLimitBoundary : Set where
  constructor elliptic-euler-cauchy-to-limit-boundary
  field
    bishopCompletenessReused : Bool
    cauchyToConstructiveLimitCompilerPaid : Bool
    eulerCauchyEstimatePaid : Bool
    infiniteEulerProductSameObjectPaid : Bool
    mellinRealizationPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticEulerCauchyToLimitBoundary :
  EllipticEulerCauchyToLimitBoundary
canonicalEllipticEulerCauchyToLimitBoundary =
  elliptic-euler-cauchy-to-limit-boundary
    true true false false false false
