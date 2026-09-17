module DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundExact where

------------------------------------------------------------------------
-- FINITE DIVISOR-POWER GROWTH BOUND
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- `FiniteDivisorSumBoundExact` already proves sigma1(n) <= n^2 from the
-- repository's shared `oneTo` enumeration, bounded-membership proof, divisor
-- filter and natural-valued fold.  Reuse exactly that finite architecture for
-- the power sums now consumed by the E4/E6 lane.
--
-- For every d in 1,...,n and every natural k,
--
--   d^k <= n^k.
--
-- There are at most n candidates before divisibility filtering, so
--
--   sigma_k(n) <= n^k * n.
--
-- In particular the internally computed Eisenstein coefficients satisfy the
-- coarse polynomial envelopes sigma_3(n) <= n^4 and sigma_5(n) <= n^6 (written
-- below in the repository's executable `powNat` normal form).
--
-- This is finite arithmetic only.  It does not prove q-series convergence,
-- choose a complex norm, or upgrade OEIS parity coordinates to authority.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (filter)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_; z≤n)
open import Data.Nat.Divisibility using (_∣?_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Power
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumBoundExact as Sigma1Bound
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Monotonicity of the repository-owned executable natural power.
------------------------------------------------------------------------

powNatMonotone :
  (exponent : Nat) ->
  ∀ {left right : Nat} ->
  left ≤ right ->
  Power.powNat left exponent ≤ Power.powNat right exponent
powNatMonotone zero left≤right = NatP.≤-refl
powNatMonotone (suc exponent) left≤right =
  NatP.*-mono-≤
    left≤right
    (powNatMonotone exponent left≤right)

------------------------------------------------------------------------
-- Filtering a bounded candidate list by divisibility cannot make the weighted
-- power fold exceed n^k times the original candidate count.
------------------------------------------------------------------------

divisorPowerFilteredFoldBound :
  (exponent n : Nat) ->
  (candidates : List Nat) ->
  All.All (λ d -> d ≤ n) candidates ->
  Reindex.foldNat (λ d -> Power.powNat d exponent)
    (filter (λ d -> d ∣? n) candidates)
  ≤ Power.powNat n exponent * Reindex.listLength candidates
divisorPowerFilteredFoldBound exponent n [] All.[] = z≤n
divisorPowerFilteredFoldBound
    exponent n (d ∷ ds) (All._∷_ d≤n rest)
  with d ∣? n
... | yes dividesProof =
  NatP.+-mono
    (powNatMonotone exponent d≤n)
    (divisorPowerFilteredFoldBound exponent n ds rest)
... | no notDivides =
  NatP.≤-trans
    (divisorPowerFilteredFoldBound exponent n ds rest)
    tailBelowNext
  where
  envelope : Nat
  envelope = Power.powNat n exponent

  tail : Nat
  tail = envelope * Reindex.listLength ds

  tailBelowNext : tail ≤ envelope + tail
  tailBelowNext =
    NatP.≤-trans
      (NatP.m≤m+n tail envelope)
      (NatP.≤-reflexive (NatP.+-comm tail envelope))

------------------------------------------------------------------------
-- General polynomial envelope and the two Eisenstein specializations.
------------------------------------------------------------------------

sigmaPowerPolynomialBound :
  (exponent n : Nat) ->
  Power.sigmaPower exponent n ≤ Power.powNat n exponent * n
sigmaPowerPolynomialBound exponent n =
  subst
    (λ length ->
      Power.sigmaPower exponent n
      ≤ Power.powNat n exponent * length)
    (Sigma1Bound.oneToLength n)
    (divisorPowerFilteredFoldBound
      exponent
      n
      (Hecke.oneTo n)
      (Sigma1Bound.upperBoundsOnly (OneTo.oneToAllBounds n)))

sigma3QuarticBound :
  (n : Nat) ->
  Power.sigma3 n ≤ Power.powNat n 3 * n
sigma3QuarticBound = sigmaPowerPolynomialBound 3

sigma5SexticBound :
  (n : Nat) ->
  Power.sigma5 n ≤ Power.powNat n 5 * n
sigma5SexticBound = sigmaPowerPolynomialBound 5
