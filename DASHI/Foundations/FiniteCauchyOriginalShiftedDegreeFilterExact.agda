module DASHI.Foundations.FiniteCauchyOriginalShiftedDegreeFilterExact where

------------------------------------------------------------------------
-- Section42: exact ORIGINAL finite rectangle/triangle shift indices.
--
-- The actual source rows are indexed by i+j, while the CMP102 A
-- wing has an extra X and the B wing has two extra powers of X.
-- This proves the all-Nat degree extraction without assuming any
-- analytic series, polynomial positivity, or unsigned Cauchy tail.
--
-- Full Bishop-ℝ filtered finite sum/order still has to be welded
-- to the existing BishopFiniteCauchyShiftedWingAbsoluteExact
-- and original CMP109 factorial source. Agda --safe not yet run.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP

-- A's literal original cutoff at count c=suc n is n: every
-- retained original rectangle cell i,j has i+j>=n.
-- Multiplication by the original leading X makes its degree >=c.
aOriginalShiftedCellDegree :
  ∀ (n i j : Nat) →
  n ≤ (i + j) →
  suc n ≤ suc (i + j)
aOriginalShiftedCellDegree n i j bound = s≤s bound

-- For B the literal triangle cutoff at c=suc(suc n)
-- is n. Multiplication by the original leading X²
-- raises each selected cell's degree by exactly two.
bOriginalShiftedCellDegree :
  ∀ (n i j : Nat) →
  n ≤ (i + j) →
  suc (suc n) ≤ suc (suc (i + j))
bOriginalShiftedCellDegree n i j bound = s≤s (s≤s bound)

-- At original count c=1, c∸2=0 and the B rectangle is the
-- genuine singleton b₀². Its degree after X² is two, and
-- cannot be treated as if the c>=2 shifted tail had a row.
bOriginalCountOneDegree :
  ∀ (i j : Nat) → suc zero ≤ suc (suc (i + j))
bOriginalCountOneDegree i j = s≤s z≤n

-- Any nonzero real power extraction uses the same source integer
-- degree, not an arbitrary truncation exponent.
aOriginalCellDegreeUnshift :
  ∀ (n i j : Nat) → n ≤ i + j → n ≤ suc (i + j)
aOriginalCellDegreeUnshift n i j h =
  NP.≤-trans h (NP.n≤1+n (i + j))

-- The degree order is constructive for arbitrary signed input:
-- negativity is handled later by the original Bishop |X^m|
-- identity and the nonnegative absolute-power order.
bOriginalCellDegreeUnshift :
  ∀ (n i j : Nat) →
  n ≤ i + j → n ≤ suc (suc (i + j))
bOriginalCellDegreeUnshift n i j h =
  NP.≤-trans h
    (NP.≤-trans
      (NP.n≤1+n (i + j))
      (NP.n≤1+n (suc (i + j))))
