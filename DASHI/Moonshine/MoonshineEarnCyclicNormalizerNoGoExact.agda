module DASHI.Moonshine.MoonshineEarnCyclicNormalizerNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Standard finite-group arithmetic used as calibration:
--
--   Aut(C_q) has order q-1 for prime q.
--
-- Hence if a prime-order complement C_p acts faithfully on C_q, then the
-- necessary arithmetic condition is
--
--   p divides q-1.
--
-- HISTORICAL INPUT
--
-- PR #1 / MoonshineEarn operationally replaces
--
--   23 -> 47,
--    7 -> 59,
--   11 -> 71.
--
-- DASHI CONTRIBUTION
--
-- Test the hypothesis that the source prime is uniformly the order of a
-- cyclic complement/automorphism acting on the target prime subgroup.
--
--   23 | 46    succeeds,
--    7 | 58    fails,
--   11 | 70    fails.
--
-- Thus the attractive 23->47 arithmetic cannot be promoted into a uniform
-- normalizer explanation of the complete PR #1 chain.  This file deliberately
-- does NOT assert any particular Monster maximal subgroup or normalizer; it
-- proves only the generic necessary arithmetic condition and its three finite
-- tests.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_%_; _∸_)
open import Data.Nat.Divisibility using (_∣_; _∤_; divides)
import Data.Nat.Divisibility as Div

------------------------------------------------------------------------
-- Necessary arithmetic shape for a prime complement acting faithfully on a
-- cyclic target of prime order.
------------------------------------------------------------------------

PrimeCyclicComplementCompatible : Nat → Nat → Set
PrimeCyclicComplementCompatible sourcePrime targetPrime =
  sourcePrime ∣ (targetPrime ∸ 1)

------------------------------------------------------------------------
-- The first edge passes the necessary condition.
------------------------------------------------------------------------

twentyThreeDividesFortySix : 23 ∣ 46
twentyThreeDividesFortySix = divides 2 refl

historical23To47ComplementCompatible :
  PrimeCyclicComplementCompatible 23 47
historical23To47ComplementCompatible = twentyThreeDividesFortySix

------------------------------------------------------------------------
-- The other two fail by exact modular arithmetic.
------------------------------------------------------------------------

sevenDoesNotDivideFiftyEight : 7 ∤ 58
sevenDoesNotDivideFiftyEight divisor
  with Div.n∣m⇒m%n≡0 58 6 divisor
... | ()

elevenDoesNotDivideSeventy : 11 ∤ 70
elevenDoesNotDivideSeventy divisor
  with Div.n∣m⇒m%n≡0 70 10 divisor
... | ()

historical7To59ComplementIncompatible :
  PrimeCyclicComplementCompatible 7 59 → ⊥
historical7To59ComplementIncompatible = sevenDoesNotDivideFiftyEight

historical11To71ComplementIncompatible :
  PrimeCyclicComplementCompatible 11 71 → ⊥
historical11To71ComplementIncompatible = elevenDoesNotDivideSeventy

------------------------------------------------------------------------
-- A single proposed mechanism covering the three operational edges is
-- impossible even though its first component is inhabited.
------------------------------------------------------------------------

record UniformEarnCyclicComplementMechanism : Set where
  field
    edge23To47 : PrimeCyclicComplementCompatible 23 47
    edge7To59 : PrimeCyclicComplementCompatible 7 59
    edge11To71 : PrimeCyclicComplementCompatible 11 71

uniformEarnCyclicComplementMechanismImpossible :
  UniformEarnCyclicComplementMechanism → ⊥
uniformEarnCyclicComplementMechanismImpossible M =
  historical7To59ComplementIncompatible
    (UniformEarnCyclicComplementMechanism.edge7To59 M)

record MoonshineEarnCyclicNormalizerBoundary : Set where
  field
    genericPrimeComplementConditionUsed : Bool
    edge23To47PassesNecessaryArithmetic : Bool
    edge7To59FailsNecessaryArithmetic : Bool
    edge11To71FailsNecessaryArithmetic : Bool
    uniformCyclicNormalizerExplanationPossible : Bool
    firstEdgePromotedToMonsterSubgroupTheorem : Bool

canonicalMoonshineEarnCyclicNormalizerBoundary :
  MoonshineEarnCyclicNormalizerBoundary
canonicalMoonshineEarnCyclicNormalizerBoundary = record
  { genericPrimeComplementConditionUsed = true
  ; edge23To47PassesNecessaryArithmetic = true
  ; edge7To59FailsNecessaryArithmetic = true
  ; edge11To71FailsNecessaryArithmetic = true
  ; uniformCyclicNormalizerExplanationPossible = false
  ; firstEdgePromotedToMonsterSubgroupTheorem = false
  }
