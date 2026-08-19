module DASHI.Moonshine.MoonshineEarnOggObserverNonfactorabilityExact where

------------------------------------------------------------------------
-- SOURCE / CONTEXT
--
-- Historical PR #1 / MoonshineEarn.agda supplies the arithmetic substitutions
--
--   23 -> 47,
--    7 -> 59,
--   11 -> 71.
--
-- MoonshineEarnHistoricalWeldExact independently proves that all six primes
-- divide the actual Monster order and all six lie on the finite Fricke
-- genus-zero control locus.
--
-- CROSS-POLLINATION
--
-- This is the exact observer/factorization pattern used elsewhere in DASHI:
-- if distinct fine states have the same coarse observation but require
-- different outputs, no function of the coarse observation alone can reproduce
-- the fine routing.
--
-- DASHI CONTRIBUTION
--
-- The common public observation
--
--   "Monster divisor + Fricke genus zero"
--
-- is constant across the historical source triple, while the required target
-- is 47,59,71 respectively.  Therefore the PR #1 substitution does NOT factor
-- through Ogg/Monster membership alone.
--
-- Consequently any source-native explanation of the historical arithmetic
-- must use finer Monster/Moonshine information (class, character, replicability,
-- modular-function, etc.) than the shared prime-set coincidence itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MoonshineEarnHistoricalWeldExact as Earn
import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke

------------------------------------------------------------------------
-- Operational source roles in the actual PR #1 chain.
------------------------------------------------------------------------

data EarnSource : Set where
  from23 from7 from11 : EarnSource

sourcePrime : EarnSource → Nat
sourcePrime from23 = 23
sourcePrime from7 = 7
sourcePrime from11 = 11

targetPrime : EarnSource → Nat
targetPrime from23 = 47
targetPrime from7 = 59
targetPrime from11 = 71

------------------------------------------------------------------------
-- The coarse Monster/Fricke observer deliberately records only the shared
-- public locus, not the prime label itself.
------------------------------------------------------------------------

data MonsterFrickeLocusObservation : Set where
  monsterFrickeGenusZero : MonsterFrickeLocusObservation

locusObserver : EarnSource → MonsterFrickeLocusObservation
locusObserver _ = monsterFrickeGenusZero

------------------------------------------------------------------------
-- Actual modern evidence that each source really does lie on that public
-- Monster/Fricke surface.  The observer is not a synthetic label detached from
-- the historical weld.
------------------------------------------------------------------------

sourceDividesActualMonsterOrder :
  (s : EarnSource) →
  Monster.PrimeDividesMonsterOrder (sourcePrime s)
sourceDividesActualMonsterOrder from23 = Earn.twentyThreeDividesMonsterOrder
sourceDividesActualMonsterOrder from7 = Earn.sevenDividesMonsterOrder
sourceDividesActualMonsterOrder from11 = Earn.elevenDividesMonsterOrder

sourceFiniteFrickeGenusZero : (s : EarnSource) → Set
sourceFiniteFrickeGenusZero from23 =
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime23) ≡ 0
sourceFiniteFrickeGenusZero from7 =
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime7) ≡ 0
sourceFiniteFrickeGenusZero from11 =
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime11) ≡ 0

sourceFiniteFrickeGenusZeroWitness :
  (s : EarnSource) → sourceFiniteFrickeGenusZero s
sourceFiniteFrickeGenusZeroWitness from23 = refl
sourceFiniteFrickeGenusZeroWitness from7 = refl
sourceFiniteFrickeGenusZeroWitness from11 = refl

------------------------------------------------------------------------
-- A second formulation uses direct collision / target-separation witnesses.
------------------------------------------------------------------------

coarseCollision23And7 : locusObserver from23 ≡ locusObserver from7
coarseCollision23And7 = refl

coarseCollision7And11 : locusObserver from7 ≡ locusObserver from11
coarseCollision7And11 = refl

targets23And7Differ : targetPrime from23 ≡ targetPrime from7 → ⊥
targets23And7Differ ()

targets7And11Differ : targetPrime from7 ≡ targetPrime from11 → ⊥
targets7And11Differ ()

------------------------------------------------------------------------
-- Exact non-factorability: one coarse value cannot route to three targets.
------------------------------------------------------------------------

record FactorsEarnTargetThroughLocus : Set where
  field
    route : MonsterFrickeLocusObservation → Nat
    factors :
      (s : EarnSource) →
      route (locusObserver s) ≡ targetPrime s

open FactorsEarnTargetThroughLocus public

monsterFrickeLocusCannotDetermineEarnTarget :
  FactorsEarnTargetThroughLocus → ⊥
monsterFrickeLocusCannotDetermineEarnTarget F =
  targets23And7Differ
    (trans
      (sym (factors F from23))
      (factors F from7))

record MoonshineEarnOggObserverBoundary : Set where
  field
    allHistoricalSourcesOnMonsterFrickeLocus : Bool
    coarseLocusCollisionsConstructed : Bool
    targetDifferencesConstructed : Bool
    substitutionFactorsThroughOggMembership : Bool
    finerMoonshineCoordinateRequiredForMechanism : Bool

canonicalMoonshineEarnOggObserverBoundary : MoonshineEarnOggObserverBoundary
canonicalMoonshineEarnOggObserverBoundary = record
  { allHistoricalSourcesOnMonsterFrickeLocus = true
  ; coarseLocusCollisionsConstructed = true
  ; targetDifferencesConstructed = true
  ; substitutionFactorsThroughOggMembership = false
  ; finerMoonshineCoordinateRequiredForMechanism = true
  }
