module DASHI.Mathematics.Automorphic.EllipticEulerSummableIncrementExact where

------------------------------------------------------------------------
-- ELLIPTIC EULER TRUNCATIONS: SUMMABLE INCREMENTS -> BISHOP CAUCHY
--
-- Reuse the application-neutral rational summable-increment compiler already
-- extracted from the RG/Casimir lanes.  The remaining elliptic mathematics is
-- now exactly an increment majorant plus a bridge from the rational vanishing
-- tail to Bishop's metric Cauchy predicate on the literal Euler truncations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Analysis.SummableIncrementCauchyBidiExact as SumInc
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Mathematics.Automorphic.EllipticEulerCauchyToLimitExact as Euler

record EllipticEulerSummableIncrement
    (system : Euler.EllipticEulerRealTruncation) : Set₁ where
  field
    rationalTailProblem : SumInc.SummableIncrementProblem

    sameLiteralEulerTrajectory : Set

    rationalTailImpliesBishopCauchy :
      SumInc.tailBoundVanishes rationalTailProblem →
      Bishop.BishopCauchy (Euler.truncation system)

open EllipticEulerSummableIncrement public

summableIncrementGivesEulerCauchyReceipt :
  ∀ {system} →
  EllipticEulerSummableIncrement system →
  Euler.EllipticEulerCauchyReceipt system
summableIncrementGivesEulerCauchyReceipt receipt = record
  { Euler.truncationsAreCauchy =
      rationalTailImpliesBishopCauchy receipt
        (SumInc.tailBoundVanishes
          (rationalTailProblem receipt))
  }

summableIncrementGivesConstructiveEulerConvergence :
  ∀ {system} →
  EllipticEulerSummableIncrement system →
  Bishop.BishopConvergent (Euler.truncation system)
summableIncrementGivesConstructiveEulerConvergence receipt =
  Euler.cauchyReceiptGivesConstructiveConvergence
    (summableIncrementGivesEulerCauchyReceipt receipt)

record EllipticEulerSummableIncrementBoundary : Set where
  constructor elliptic-euler-summable-increment-boundary
  field
    applicationNeutralSummableIncrementReused : Bool
    summableIncrementToEulerCauchyCompilerPaid : Bool
    bishopCompletionDownstreamPaid : Bool
    ellipticIncrementMajorantPaid : Bool
    rationalTailToBishopMetricPaid : Bool
    infiniteEulerSameObjectPaid : Bool
    mellinRealizationPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticEulerSummableIncrementBoundary :
  EllipticEulerSummableIncrementBoundary
canonicalEllipticEulerSummableIncrementBoundary =
  elliptic-euler-summable-increment-boundary
    true true true false false false false false
