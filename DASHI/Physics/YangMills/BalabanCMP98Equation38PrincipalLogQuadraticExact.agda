module DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- SOURCE LOCATION / NORMALIZATION
--
-- Equations (34)--(38), p. 23.  Bałaban writes
--
--   (1/i) log (exp(iX) exp(iY))
--     = Y + g^{-1}(-i ad_Y) X + Psi(X;Y)
--
-- and explicitly states that the absolute constant O(1)=24 may be used on
--
--   |X| <= 1/20,     |Y| <= 1/12.
--
-- This module records those literal source radii rather than the earlier
-- vague "sufficiently small" interface, and proves the exact conversion from
-- the quadratic source bound to the epsilon/little-o form consumed by CMP109.
-- The source norm is Bałaban's matrix norm; any later identification with the
-- repository Lie-3 l1 carrier must be supplied by the same-coordinate physical
-- producer, never silently by norm equivalence.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

sourceQuadraticConstant : ℚ
sourceQuadraticConstant = + 24 / 1

sourceXRadius : ℚ
sourceXRadius = + 1 / 20

sourceYRadius : ℚ
sourceYRadius = + 1 / 12

record Equation38SourceChart
    (inputMagnitude baseMagnitude : ℚ) : Set where
  field
    inputNonnegative : 0ℚ ≤ inputMagnitude
    baseNonnegative : 0ℚ ≤ baseMagnitude
    inputInsideSourceChart : inputMagnitude ≤ sourceXRadius
    baseInsideSourceChart : baseMagnitude ≤ sourceYRadius

open Equation38SourceChart public

record Equation38QuadraticRemainder
    (inputMagnitude remainderMagnitude : ℚ) : Set where
  field
    inputNonnegative : 0ℚ ≤ inputMagnitude
    remainderNonnegative : 0ℚ ≤ remainderMagnitude
    sourceQuadraticBound :
      remainderMagnitude
      ≤ (sourceQuadraticConstant * inputMagnitude) * inputMagnitude

open Equation38QuadraticRemainder public

equation38RemainderLittleOEpsilon :
  ∀ inputMagnitude remainderMagnitude epsilon →
  Equation38QuadraticRemainder inputMagnitude remainderMagnitude →
  sourceQuadraticConstant * inputMagnitude ≤ epsilon →
  remainderMagnitude ≤ epsilon * inputMagnitude
equation38RemainderLittleOEpsilon inputMagnitude remainderMagnitude epsilon data small =
  ℚP.≤-trans
    (sourceQuadraticBound data)
    (ℚP.*-monoʳ-≤-nonNeg inputMagnitude small)

-- A useful exact threshold specialization: if |X| <= epsilon/24, the source
-- remainder is epsilon |X|-small.  The division itself is left to callers so
-- no positivity side condition on epsilon is hidden in this theorem.
equation38RemainderLittleOFromTwentyFourTimesInput :
  ∀ inputMagnitude remainderMagnitude epsilon →
  Equation38QuadraticRemainder inputMagnitude remainderMagnitude →
  sourceQuadraticConstant * inputMagnitude ≤ epsilon →
  remainderMagnitude ≤ epsilon * inputMagnitude
equation38RemainderLittleOFromTwentyFourTimesInput =
  equation38RemainderLittleOEpsilon

cmp98Equation38SourceChartLevel : ProofLevel
cmp98Equation38SourceChartLevel = machineChecked

cmp98Equation38QuadraticRemainderLevel : ProofLevel
cmp98Equation38QuadraticRemainderLevel = machineChecked

cmp98Equation38LittleOEpsilonLevel : ProofLevel
cmp98Equation38LittleOEpsilonLevel = machineChecked
