module DASHI.Physics.Closure.NSTriadKNLuoLowHighExponentBookkeepingCorrectedExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- PURPOSE
-- Resolve the branch-label discrepancy in the centered (L6,L3) dyadic
-- commutator calculation before it enters the physical carrier.
--
-- With p=q, the two raw Bernstein exponents are
--
--   B1 = -2 q + 3 r + (3/2) q = -(1/2) q + 3 r,
--   B2 = -2 q + 2 r + (5/2) q =  (1/2) q + 2 r.
--
-- Relative to the critical/output exponent
--
--   C = (3/2) r + q,
--
-- they are exactly
--
--   B1 = C - (3/2)(q-r),
--   B2 = C - (1/2)(q-r).
--
-- Thus the first Taylor branch has the stronger 2^(-3(q-r)/2) gain, while
-- the second branch has the weaker 2^(-(q-r)/2) gain and matches the final
-- displayed LH target exactly. For p=q+s, the same identities acquire only
-- the bounded comparable-shell factors (3/2)s and (5/2)s respectively.
-- Squaring gives the already-implemented kernels 2^(-3d) and 2^(-d), with
-- the strong branch dominated by the weak.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; _/_; _+_; _*_; _-_; -_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as Scale

half threeHalves two three fiveHalves : ℚ
half = Int.+ 1 / 2
threeHalves = Int.+ 3 / 2
two = Int.+ 2 / 1
three = Int.+ 3 / 1
fiveHalves = Int.+ 5 / 2

minusTwo minusHalf minusThreeHalves : ℚ
minusTwo = - two
minusHalf = - half
minusThreeHalves = - threeHalves

branchOneRawExponent : ℚ → ℚ → ℚ
branchOneRawExponent q r =
  minusTwo * q + three * r + threeHalves * q

branchTwoRawExponent : ℚ → ℚ → ℚ
branchTwoRawExponent q r =
  minusTwo * q + two * r + fiveHalves * q

branchOneComparableExponent : ℚ → ℚ → ℚ → ℚ
branchOneComparableExponent q r p =
  minusTwo * q + three * r + threeHalves * p

branchTwoComparableExponent : ℚ → ℚ → ℚ → ℚ
branchTwoComparableExponent q r p =
  minusTwo * q + two * r + fiveHalves * p

criticalOutputExponent : ℚ → ℚ → ℚ
criticalOutputExponent q r = threeHalves * r + q

strongGapExponent : ℚ → ℚ → ℚ
strongGapExponent q r =
  criticalOutputExponent q r - threeHalves * (q - r)

weakGapExponent : ℚ → ℚ → ℚ
weakGapExponent q r =
  criticalOutputExponent q r - half * (q - r)

branchOneRawSimplifies :
  (q r : ℚ) →
  branchOneRawExponent q r ≡ minusHalf * q + three * r
branchOneRawSimplifies q r = solve (q ∷ r ∷ [])

branchTwoRawSimplifies :
  (q r : ℚ) →
  branchTwoRawExponent q r ≡ half * q + two * r
branchTwoRawSimplifies q r = solve (q ∷ r ∷ [])

branchOneIsStrongGap :
  (q r : ℚ) →
  branchOneRawExponent q r ≡ strongGapExponent q r
branchOneIsStrongGap q r = solve (q ∷ r ∷ [])

branchTwoIsWeakGap :
  (q r : ℚ) →
  branchTwoRawExponent q r ≡ weakGapExponent q r
branchTwoIsWeakGap q r = solve (q ∷ r ∷ [])

finalDisplayedTargetMatchesBranchTwo :
  (q r : ℚ) →
  minusHalf * (q - r) + threeHalves * r + q
  ≡ branchTwoRawExponent q r
finalDisplayedTargetMatchesBranchTwo q r = solve (q ∷ r ∷ [])

firstBranchCriticalFactorization :
  (q r : ℚ) →
  minusThreeHalves * (q - r) + threeHalves * r + q
  ≡ branchOneRawExponent q r
firstBranchCriticalFactorization q r = solve (q ∷ r ∷ [])

branchOneComparableOffset :
  (q r offset : ℚ) →
  branchOneComparableExponent q r (q + offset)
  ≡ strongGapExponent q r + threeHalves * offset
branchOneComparableOffset q r offset = solve (q ∷ r ∷ offset ∷ [])

branchTwoComparableOffset :
  (q r offset : ℚ) →
  branchTwoComparableExponent q r (q + offset)
  ≡ weakGapExponent q r + fiveHalves * offset
branchTwoComparableOffset q r offset = solve (q ∷ r ∷ offset ∷ [])

branchTwoComparableMatchesDisplayedTarget :
  (q r offset : ℚ) →
  branchTwoComparableExponent q r (q + offset)
  ≡ minusHalf * (q - r) + threeHalves * r + q
    + fiveHalves * offset
branchTwoComparableMatchesDisplayedTarget q r offset =
  solve (q ∷ r ∷ offset ∷ [])

strongSquaredGapBelowWeakSquaredGap :
  (gap : Nat) →
  Scale.strongBranchSquaredGap gap ≤ Scale.weakBranchSquaredGap gap
strongSquaredGapBelowWeakSquaredGap =
  Scale.strongBranchDominatedByWeak
