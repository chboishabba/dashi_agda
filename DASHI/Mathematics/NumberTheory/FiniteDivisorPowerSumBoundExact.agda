module DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundExact where

------------------------------------------------------------------------
-- EXECUTABLE SIGMA_k AND COARSE POLYNOMIAL GROWTH
--
-- Reuses the repository's positive-divisor enumeration.  For k >= 0,
--
--   sigma_k(n) = sum_{d|n,d>0} d^k.
--
-- Every positive divisor d of n lies in 1..n, hence d^k <= n^k and there are
-- at most n candidates.  Therefore
--
--   sigma_k(n) <= n * n^k = n^(k+1).
--
-- This deliberately coarse estimate is sufficient for the E4/E6 q-series:
--
--   sigma_3(n) <= n^4,
--   sigma_5(n) <= n^6.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.List.Base using (filter)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_; z≤n)
open import Data.Nat.Divisibility using (_∣?_)
import Data.Nat.Properties as NatP
open import Data.Product using (proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumBoundExact as Sigma1Bound
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Exact executable divisor-power sum.
------------------------------------------------------------------------

sigmaPower : Nat → Nat → Nat
sigmaPower exponent n =
  Reindex.foldNat
    (λ d → Hecke.powNat d exponent)
    (Divisor.positiveDivisors n)

sigma3 : Nat → Nat
sigma3 = sigmaPower 3

sigma5 : Nat → Nat
sigma5 = sigmaPower 5

sigma3One : sigma3 1 ≡ 1
sigma3One = refl

sigma3Two : sigma3 2 ≡ 9
sigma3Two = refl

sigma3Three : sigma3 3 ≡ 28
sigma3Three = refl

sigma5One : sigma5 1 ≡ 1
sigma5One = refl

sigma5Two : sigma5 2 ≡ 33
sigma5Two = refl

sigma5Three : sigma5 3 ≡ 244
sigma5Three = refl

------------------------------------------------------------------------
-- Monotonicity of natural powers.
------------------------------------------------------------------------

powNatMonotone :
  (exponent : Nat) →
  ∀ {left right : Nat} →
  left ≤ right →
  Hecke.powNat left exponent ≤ Hecke.powNat right exponent
powNatMonotone zero left≤right = NatP.≤-refl
powNatMonotone (suc exponent) left≤right =
  NatP.*-mono left≤right (powNatMonotone exponent left≤right)

------------------------------------------------------------------------
-- Generic bounded filtered fold.
------------------------------------------------------------------------

filteredWeightedFoldBound :
  (n bound : Nat) →
  (weight : Nat → Nat) →
  (candidates : List Nat) →
  All.All (λ d → d ≤ n) candidates →
  (∀ d → d ≤ n → weight d ≤ bound) →
  Reindex.foldNat weight
    (filter (λ d → d ∣? n) candidates)
  ≤ bound * Reindex.listLength candidates
filteredWeightedFoldBound n bound weight [] All.[] pointwise = z≤n
filteredWeightedFoldBound
  n bound weight (d ∷ ds) (All._∷_ d≤n rest) pointwise
  with d ∣? n
... | yes dividesProof =
  NatP.+-mono
    (pointwise d d≤n)
    (filteredWeightedFoldBound n bound weight ds rest pointwise)
... | no notDivides =
  NatP.≤-trans
    (filteredWeightedFoldBound n bound weight ds rest pointwise)
    tailBelowNext
  where
  tail : Nat
  tail = bound * Reindex.listLength ds

  tailBelowNext : tail ≤ bound + tail
  tailBelowNext =
    NatP.≤-trans
      (NatP.m≤m+n tail bound)
      (NatP.≤-reflexive (NatP.+-comm tail bound))

------------------------------------------------------------------------
-- sigma_k(n) <= n^(k+1).
------------------------------------------------------------------------

sigmaPowerBound :
  (exponent n : Nat) →
  sigmaPower exponent n ≤ Hecke.powNat n (suc exponent)
sigmaPowerBound exponent n =
  NatP.≤-trans
    raw
    (NatP.≤-reflexive
      (NatP.*-comm (Hecke.powNat n exponent) n))
  where
  raw :
    sigmaPower exponent n
    ≤ Hecke.powNat n exponent * n
  raw =
    subst
      (λ length →
        sigmaPower exponent n
        ≤ Hecke.powNat n exponent * length)
      (Sigma1Bound.oneToLength n)
      (filteredWeightedFoldBound
        n
        (Hecke.powNat n exponent)
        (λ d → Hecke.powNat d exponent)
        (Hecke.oneTo n)
        (Sigma1Bound.upperBoundsOnly (OneTo.oneToAllBounds n))
        (λ d d≤n → powNatMonotone exponent d≤n))

sigma3QuarticBound :
  (n : Nat) →
  sigma3 n ≤ Hecke.powNat n 4
sigma3QuarticBound = sigmaPowerBound 3

sigma5SexticBound :
  (n : Nat) →
  sigma5 n ≤ Hecke.powNat n 6
sigma5SexticBound = sigmaPowerBound 5

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

data DivisorPowerSumStatus : Set where
  finiteExact : DivisorPowerSumStatus
  coarsePolynomialBound : DivisorPowerSumStatus

sigma3Status : DivisorPowerSumStatus
sigma3Status = coarsePolynomialBound

sigma5Status : DivisorPowerSumStatus
sigma5Status = coarsePolynomialBound
