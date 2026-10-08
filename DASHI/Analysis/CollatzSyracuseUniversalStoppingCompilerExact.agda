module DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact where

------------------------------------------------------------------------
-- UNIVERSAL STOPPING <-> LITERAL STRICT-DESCENT PRODUCER
--
-- The genuine terminal Collatz wall can be stated exactly:
--
--   every x > 1 has some finite shortcut-Syracuse iterate below x.
--
-- This is equivalent to universal stopping.  The forward implication is
-- well-founded induction on the literal positive integer.  The reverse
-- implication uses the eventual iterate 1, which is strictly below x > 1.
--
-- The existing affine/parity theorem provides a stronger sufficient sub-route:
-- choose m with 3^m <= x and prove the actual parity word satisfies
--
--   2 * 3^(ones word) <= 2^m.
--
-- That coarse sufficient interface is not asserted to exist for every start;
-- finite-density / Chernoff tails likewise do not eliminate every exceptional
-- start.  They therefore cannot inhabit the exact terminal source by themselves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_<_; z≤n; s≤s)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
import Data.Product as Product
open Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParityDescentEventExact as Event

syracuseIterateAdd :
  (m k : Nat) →
  (x : Syracuse.PositiveNat) →
  Syracuse.syracuseIterate (m + k) x
  ≡ Syracuse.syracuseIterate k (Syracuse.syracuseIterate m x)
syracuseIterateAdd zero k x = refl
syracuseIterateAdd (suc m) k x =
  syracuseIterateAdd m k (Syracuse.shortcutSyracuse x)

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

-- Strong sufficient sub-route.  This is intentionally not identified with the
-- terminal source: the affine correction estimate can be too coarse for a
-- particular start even when that start genuinely reaches a lower value.
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
    m = Product.proj₁ descentWitness
    smaller = Product.proj₂ descentWitness
    y = Syracuse.syracuseIterate m x

    yStops : ReachesOne y
    yStops = reachesOneFromStrictDescentAcc source y (wf smaller)

    k = Product.proj₁ yStops
    yStopsAtK = Product.proj₂ yStops

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

strictDescentFromUniversalStopping :
  ((x : Syracuse.PositiveNat) → ReachesOne x) →
  LiteralStrictDescentSource
strictDescentFromUniversalStopping stops = record
  { descend = λ x nontrivial →
      let
        stopped = stops x
        k = Product.proj₁ stopped
        atOne = Product.proj₂ stopped

        toNatAtOne :
          Syracuse.toNat (Syracuse.syracuseIterate k x) ≡ 1
        toNatAtOne = cong Syracuse.toNat atOne

        smaller :
          Syracuse.toNat (Syracuse.syracuseIterate k x)
          < Syracuse.toNat x
        smaller =
          subst
            (λ value → value < Syracuse.toNat x)
            (sym toNatAtOne)
            nontrivial
      in
      k , smaller
  }

record UniversalStoppingEquivalence : Set₁ where
  constructor universalStoppingEquivalence
  field
    strictDescentToStopping :
      LiteralStrictDescentSource →
      (x : Syracuse.PositiveNat) →
      ReachesOne x

    stoppingToStrictDescent :
      ((x : Syracuse.PositiveNat) → ReachesOne x) →
      LiteralStrictDescentSource

canonicalUniversalStoppingEquivalence : UniversalStoppingEquivalence
canonicalUniversalStoppingEquivalence =
  universalStoppingEquivalence
    universalStoppingFromStrictDescent
    strictDescentFromUniversalStopping

record UniversalStoppingBoundary : Set where
  constructor universalStoppingBoundary
  field
    iterateCompositionOwned : Nat
    wellFoundedCompilerOwned : Nat
    reverseStoppingToDescentOwned : Nat
    strictDescentEquivalenceOwned : Nat
    affineGoodPrefixSufficientCompilerOwned : Nat
    finiteDensityTailEliminatesEveryException : Nat
    allStartsLiteralStrictDescentProducerOwned : Nat

canonicalUniversalStoppingBoundary : UniversalStoppingBoundary
canonicalUniversalStoppingBoundary =
  universalStoppingBoundary 1 1 1 1 1 0 0
