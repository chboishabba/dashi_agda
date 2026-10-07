module DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact where

------------------------------------------------------------------------
-- UNIVERSAL STOPPING COMPILER FROM A LITERAL STRICT-DESCENT PRODUCER
--
-- This isolates the genuine terminal Collatz wall.  If every literal positive
-- integer x > 1 has some finite shortcut-Syracuse prefix that lands at a
-- strictly smaller positive integer, then well-founded induction on Nat proves
-- that every x reaches 1.
--
-- The existing affine/parity theorem gives a sufficient producer interface:
-- choose m with 3^m <= x and prove the actual parity word satisfies
--
--   2 * 3^(ones word) <= 2^m.
--
-- Finite-density / Chernoff tails do not inhabit this producer because they do
-- not eliminate every exceptional start.  That distinction is the max-cut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_<_; z≤n; s≤s)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParityDescentEventExact as Event

------------------------------------------------------------------------
-- Iterate composition.
------------------------------------------------------------------------

syracuseIterateAdd :
  (m k : Nat) →
  (x : Syracuse.PositiveNat) →
  Syracuse.syracuseIterate (m + k) x
  ≡ Syracuse.syracuseIterate k (Syracuse.syracuseIterate m x)
syracuseIterateAdd zero k x = refl
syracuseIterateAdd (suc m) k x =
  syracuseIterateAdd m k (Syracuse.shortcutSyracuse x)

------------------------------------------------------------------------
-- Literal stopping proposition.
------------------------------------------------------------------------

ReachesOne : Syracuse.PositiveNat → Set
ReachesOne x =
  Σ Nat (λ k → Syracuse.syracuseIterate k x ≡ Syracuse.one)

record LiteralStrictDescentSource : Set₁ where
  field
    descend :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      Σ Nat (λ m →
        Syracuse.toNat (Syracuse.syracuseIterate m x)
        < Syracuse.toNat x)

open LiteralStrictDescentSource public

------------------------------------------------------------------------
-- Existing affine/parity machinery is a sufficient strict-descent producer.
------------------------------------------------------------------------

record GoodPrefixDescentSource : Set₁ where
  field
    chosenHorizon :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x → Nat

    startAboveCorrection :
      (x : Syracuse.PositiveNat) →
      (nontrivial : 1 < Syracuse.toNat x) →
      Affine.powNat 3 (chosenHorizon x nontrivial)
      ≤ Syracuse.toNat x

    chosenPrefixGood :
      (x : Syracuse.PositiveNat) →
      (nontrivial : 1 < Syracuse.toNat x) →
      Event.parityDriftGood
        (Itinerary.parityWord (chosenHorizon x nontrivial) x)

open GoodPrefixDescentSource public

asLiteralStrictDescentSource :
  GoodPrefixDescentSource → LiteralStrictDescentSource
asLiteralStrictDescentSource source = record
  { descend = λ x nontrivial →
      let
        m = chosenHorizon source x nontrivial
        descent = Event.goodParityWordImpliesDescent
          m
          x
          (startAboveCorrection source x nontrivial)
          (chosenPrefixGood source x nontrivial)
      in
      m , descent
  }

------------------------------------------------------------------------
-- Well-founded stopping compiler.
------------------------------------------------------------------------

reachesOneFromStrictDescentAcc :
  (source : LiteralStrictDescentSource) →
  (x : Syracuse.PositiveNat) →
  Acc _<_ (Syracuse.toNat x) →
  ReachesOne x
reachesOneFromStrictDescentAcc source (Syracuse.positiveNat zero) accessibility =
  zero , refl
reachesOneFromStrictDescentAcc source x@(Syracuse.positiveNat (suc n)) (acc wf) =
  let
    nontrivial : 1 < Syracuse.toNat x
    nontrivial = s≤s (s≤s z≤n)

    descentWitness = descend source x nontrivial
    m = Data.Product.proj₁ descentWitness
    smaller = Data.Product.proj₂ descentWitness
    y = Syracuse.syracuseIterate m x

    yStops : ReachesOne y
    yStops = reachesOneFromStrictDescentAcc source y (wf smaller)

    k = Data.Product.proj₁ yStops
    yStopsAtK = Data.Product.proj₂ yStops

    composed :
      Syracuse.syracuseIterate (m + k) x ≡ Syracuse.one
    composed = trans (syracuseIterateAdd m k x) yStopsAtK
  in
  (m + k) , composed

universalStoppingFromStrictDescent :
  (source : LiteralStrictDescentSource) →
  (x : Syracuse.PositiveNat) →
  ReachesOne x
universalStoppingFromStrictDescent source x =
  reachesOneFromStrictDescentAcc
    source
    x
    (<-wellFounded (Syracuse.toNat x))

universalStoppingFromGoodPrefixes :
  GoodPrefixDescentSource →
  (x : Syracuse.PositiveNat) →
  ReachesOne x
universalStoppingFromGoodPrefixes source =
  universalStoppingFromStrictDescent
    (asLiteralStrictDescentSource source)

record UniversalStoppingBoundary : Set where
  constructor universalStoppingBoundary
  field
    iterateCompositionOwned : Nat
    wellFoundedCompilerOwned : Nat
    affineGoodPrefixCompilerOwned : Nat
    finiteDensityTailEliminatesEveryException : Nat
    allStartsGoodPrefixProducerOwned : Nat

canonicalUniversalStoppingBoundary : UniversalStoppingBoundary
canonicalUniversalStoppingBoundary =
  universalStoppingBoundary 1 1 1 0 0
