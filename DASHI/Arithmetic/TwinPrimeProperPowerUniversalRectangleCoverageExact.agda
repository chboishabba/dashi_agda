module DASHI.Arithmetic.TwinPrimeProperPowerUniversalRectangleCoverageExact where

------------------------------------------------------------------------
-- CT10×CT11: FOR ALL NATS U, EVERY P^k, k>=2, p>=2,
-- WITH VALUE <=U OCCURS IN THE ACTUAL DISTINCT-FINITE
-- RECTANGLE CANDIDATE IMAGE.
--
-- The numeric 2^e / floorBinaryExponent owner is imported.
-- The numeric floor-square-root / exact enumeration owners are
-- imported. No second Nat exponentiation, no real logarithm,
-- no ESD edits, no positive prime correlation assumption.
--
-- Source-written; kernel check pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_)
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Root
import DASHI.Arithmetic.TwinPrimeProperPowerBinaryCutoffNatExact as Cutoff
import DASHI.Arithmetic.TwinPrimeProperPowerRectangleEnumerationExact as Rect

properPowerInComputedRectangle :
  (basePredecessor k upper : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  Rect._member_
    (Power.natPow (suc (suc basePredecessor)) (suc (suc k)))
    (Rect.powerValueRectangle
      (Root.floorSquareRoot upper)
      (Cutoff.floorBinaryExponent upper))
properPowerInComputedRectangle basePredecessor k upper bound =
  Rect.properPowerCoveredByRootRectangle
    basePredecessor k upper
    (Cutoff.floorBinaryExponent upper)
    bound
    (Cutoff.properPowerExponentBelowCutoff
      basePredecessor k upper bound)

properPowerInDedupComputedRectangle :
  (basePredecessor k upper : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  Rect._member_
    (Power.natPow (suc (suc basePredecessor)) (suc (suc k)))
    (Rect.dedupPowerValues
      (Rect.powerValueRectangle
        (Root.floorSquareRoot upper)
        (Cutoff.floorBinaryExponent upper)))
properPowerInDedupComputedRectangle basePredecessor k upper bound =
  Rect.dedupPreservesMember
    (Rect.powerValueRectangle
      (Root.floorSquareRoot upper)
      (Cutoff.floorBinaryExponent upper))
    (properPowerInComputedRectangle basePredecessor k upper bound)

------------------------------------------------------------------------
-- CT11 computed, duplicate-safe finite counting receipt.
-- This bound is about the actual finite candidate image, including
-- all genuine proper prime powers with value <=upper; composite-base
-- candidates may overcount, never undercount.
------------------------------------------------------------------------

computedCandidateDistinctCountBound :
  (upper : Nat) →
  Rect.properPowerCandidateDistinctCount
    (Root.floorSquareRoot upper)
    (Cutoff.floorBinaryExponent upper)
  ≤ Root.floorSquareRoot upper * Cutoff.floorBinaryExponent upper
computedCandidateDistinctCountBound upper =
  Rect.properPowerCandidateDistinctCountBound
    (Root.floorSquareRoot upper)
    (Cutoff.floorBinaryExponent upper)

computedCandidateImageNoDuplicates :
  (upper : Nat) →
  Rect.DistinctValues
    (Rect.dedupPowerValues
      (Rect.powerValueRectangle
        (Root.floorSquareRoot upper)
        (Cutoff.floorBinaryExponent upper)))
computedCandidateImageNoDuplicates upper =
  Rect.dedupValuesDistinct
    (Rect.powerValueRectangle
      (Root.floorSquareRoot upper)
      (Cutoff.floorBinaryExponent upper))

------------------------------------------------------------------------
-- CT11 ALTERNATIVE CANONICAL RECTANGLE:
-- original floor-square-root × standard-library floor-log₂,
-- with the same precise prime-power membership guarantee.
-- No independent logarithm implementation or real analytic scalar.
------------------------------------------------------------------------

properPowerInStdlibLogRectangle :
  (basePredecessor k upper : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  Rect._member_
    (Power.natPow (suc (suc basePredecessor)) (suc (suc k)))
    (Rect.powerValueRectangle
      (Root.floorSquareRoot upper)
      (Cutoff.canonicalStdlibFloorLog₂ upper))
properPowerInStdlibLogRectangle basePredecessor k upper bound =
  Rect.properPowerCoveredByRootRectangle
    basePredecessor k upper
    (Cutoff.canonicalStdlibFloorLog₂ upper)
    bound
    (Cutoff.properPowerExponentBelowStdlibLog
      basePredecessor k upper bound)

properPowerInStdlibLogDedupRectangle :
  (basePredecessor k upper : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  Rect._member_
    (Power.natPow (suc (suc basePredecessor)) (suc (suc k)))
    (Rect.dedupPowerValues
      (Rect.powerValueRectangle
        (Root.floorSquareRoot upper)
        (Cutoff.canonicalStdlibFloorLog₂ upper)))
properPowerInStdlibLogDedupRectangle basePredecessor k upper bound =
  Rect.dedupPreservesMember
    (Rect.powerValueRectangle
      (Root.floorSquareRoot upper)
      (Cutoff.canonicalStdlibFloorLog₂ upper))
    (properPowerInStdlibLogRectangle
      basePredecessor k upper bound)

stdlibLogCandidateDistinctCountBound :
  (upper : Nat) →
  Rect.properPowerCandidateDistinctCount
    (Root.floorSquareRoot upper)
    (Cutoff.canonicalStdlibFloorLog₂ upper)
  ≤
  Root.floorSquareRoot upper * Cutoff.canonicalStdlibFloorLog₂ upper
stdlibLogCandidateDistinctCountBound upper =
  Rect.properPowerCandidateDistinctCountBound
    (Root.floorSquareRoot upper)
    (Cutoff.canonicalStdlibFloorLog₂ upper)
