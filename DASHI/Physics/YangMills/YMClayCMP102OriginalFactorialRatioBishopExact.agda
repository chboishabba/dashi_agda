module DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialRatioBishopExact where

------------------------------------------------------------------------
-- Original CMP102 factorial successor ratios, FULL source transport
-- Nat factorial growth -> unnormalised positive rational order
-- -> SAME Bishop real coefficient order.
--
-- The Nat inequalities are proven in
-- YMClayCMP102OriginalFactorialNatGrowthExact.
-- This file invokes the original cross-product order definition
-- (Q.*≤*) and P.p≤q⇒p⋆≤q⋆; it does NOT declare either ratio as an
-- input or postulate.
--
-- Source-written; Agda 2.9 with actual vendor/stdlib MUST elaborate
-- and verify this before the ratio leaves are marked accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Integer.Base as Z using (+_; +≤+)
import Data.Rational.Unnormalised as Q
  using (_/_; _*_; _≤_; *≤*)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialNatGrowthExact as Growth
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialMassBudgetExact as Mass

originalARatioBishop : Mass.OriginalARatio
originalARatioBishop n =
  let
    oldIndex = E.evenExponent (suc n)
    newIndex = E.evenExponent (suc (suc n))
    instance
      oldNonzero : N.NonZero (E.factorial oldIndex)
      oldNonzero = NP._!≢0 oldIndex
      newNonzero : N.NonZero (E.factorial newIndex)
      newNonzero = NP._!≢0 newIndex
    hNat = Growth.originalADenominatorGrowth n
    hRat :
      Q._≤_
        (E.inverseFactorialRational newIndex)
        ((+ 1 / 12) Q.* (E.inverseFactorialRational oldIndex))
    hRat = Q.*≤* (Z.+≤+ hNat)
  in
  P.≤-respʳ-≃
    (P.⋆-distrib-* (+ 1 / 12)
      (E.inverseFactorialRational oldIndex))
    (P.p≤q⇒p⋆≤q⋆
      (E.inverseFactorialRational newIndex)
      ((+ 1 / 12) Q.* (E.inverseFactorialRational oldIndex))
      hRat)

originalBRatioBishop : Mass.OriginalBRatio
originalBRatioBishop n =
  let
    oldIndex = E.oddExponent (suc n)
    newIndex = E.oddExponent (suc (suc n))
    instance
      oldNonzero : N.NonZero (E.factorial oldIndex)
      oldNonzero = NP._!≢0 oldIndex
      newNonzero : N.NonZero (E.factorial newIndex)
      newNonzero = NP._!≢0 newIndex
    hNat = Growth.originalBDenominatorGrowth n
    hRat :
      Q._≤_
        (E.inverseFactorialRational newIndex)
        ((+ 1 / 20) Q.* (E.inverseFactorialRational oldIndex))
    hRat = Q.*≤* (Z.+≤+ hNat)
  in
  P.≤-respʳ-≃
    (P.⋆-distrib-* (+ 1 / 20)
      (E.inverseFactorialRational oldIndex))
    (P.p≤q⇒p⋆≤q⋆
      (E.inverseFactorialRational newIndex)
      ((+ 1 / 20) Q.* (E.inverseFactorialRational oldIndex))
      hRat)

-- The previous conditional scalar A/B mass bounds are now SOURCE
-- WRITTEN without ANY synthetic ratio/initial/budget premise:
-- all data come from original factorial Nat proof and Bishop order.
originalAllAMassBelowSixElevenths :
  ∀ count →
  R._≤_ (Seq.SeriesOf
    (λ n → R._⋆
      (E.inverseFactorialRational (E.evenExponent (suc n))))
    count)
    (R._⋆ (+ 6 / 11))
originalAllAMassBelowSixElevenths =
  Mass.originalAAllFiniteMassFromFactorialRatio
    originalARatioBishop

originalAllBMassBelowTenFiftySevenths :
  ∀ count →
  R._≤_ (Seq.SeriesOf
    (λ n → R._⋆
      (E.inverseFactorialRational (E.oddExponent (suc n))))
    count)
    (R._⋆ (+ 10 / 57))
originalAllBMassBelowTenFiftySevenths =
  Mass.originalBAllFiniteMassFromFactorialRatio
    originalBRatioBishop
