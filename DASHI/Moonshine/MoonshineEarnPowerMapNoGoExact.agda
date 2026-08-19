module DASHI.Moonshine.MoonshineEarnPowerMapNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bull. London Math. Soc. 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds,
-- "Monstrous moonshine and monstrous Lie superalgebras",
-- Invent. Math. 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Standard finite-group fact used at the exact interface below:
--
--   ord(g^k) divides ord(g).
--
-- HISTORICAL INPUT
--
-- PR #1 / MoonshineEarn.agda performs, in operational order,
--
--   23 -> 47,
--    7 -> 59,
--   11 -> 71,
--
-- inside its FRACTRAN-style arithmetic chain.
--
-- DASHI CONTRIBUTION
--
-- Test the tempting interpretation that these substitutions are shadows of
-- the Monster conjugacy-class POWER MAP used by Conway--Norton replicability.
-- A genuine class power map is induced by g |-> g^k, hence its output order
-- must divide its input order.  All three historical substitutions violate
-- that necessary law, because the target prime is strictly larger than the
-- source prime.
--
-- Therefore the PR #1 substitution is NOT literally a Monster power map, and
-- Conway--Norton power-map compatibility cannot be used as its source-native
-- explanation.  This does not rule out every more indirect Moonshine relation;
-- it kills precisely the direct power-map / replicability interpretation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_<_)
open import Data.Nat.Divisibility using (_∣_; _∤_)
import Data.Nat.Divisibility as Div
import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- Minimal standard interface for an element-power operation with the exact
-- group-theoretic order law consumed by the falsifier.
------------------------------------------------------------------------

record PowerMapOrderLaw : Set₁ where
  field
    Element : Set
    power : Element → Nat → Element
    order : Element → Nat
    orderOfPowerDivides :
      (g : Element) → (k : Nat) →
      order (power g k) ∣ order g

open PowerMapOrderLaw public

record PowerMapSubstitution
    (law : PowerMapOrderLaw)
    (sourceOrder targetOrder : Nat) : Set where
  field
    sourceElement : Element law
    exponent : Nat
    sourceOrderExact : order law sourceElement ≡ sourceOrder
    poweredOrderExact :
      order law (power law sourceElement exponent) ≡ targetOrder

open PowerMapSubstitution public

------------------------------------------------------------------------
-- Any claimed power-map substitution forces target order to divide source.
------------------------------------------------------------------------

powerMapSubstitutionForcesOrderDivisibility :
  (law : PowerMapOrderLaw) →
  (sourceOrder targetOrder : Nat) →
  PowerMapSubstitution law sourceOrder targetOrder →
  targetOrder ∣ sourceOrder
powerMapSubstitutionForcesOrderDivisibility law sourceOrder targetOrder W =
  let
    raw :
      order law (power law (sourceElement W) (exponent W))
      ∣ order law (sourceElement W)
    raw = orderOfPowerDivides law (sourceElement W) (exponent W)

    sourceRewritten :
      order law (power law (sourceElement W) (exponent W))
      ∣ sourceOrder
    sourceRewritten =
      subst
        (λ n → order law (power law (sourceElement W) (exponent W)) ∣ n)
        (sourceOrderExact W)
        raw
  in
  subst
    (λ n → n ∣ sourceOrder)
    (poweredOrderExact W)
    sourceRewritten

------------------------------------------------------------------------
-- Exact arithmetic obstructions for the three PR #1 substitutions.
------------------------------------------------------------------------

fortySevenGreaterThanTwentyThree : 23 < 47
fortySevenGreaterThanTwentyThree = NatP.m≤m+n 24 23

fiftyNineGreaterThanSeven : 7 < 59
fiftyNineGreaterThanSeven = NatP.m≤m+n 8 51

seventyOneGreaterThanEleven : 11 < 71
seventyOneGreaterThanEleven = NatP.m≤m+n 12 59

fortySevenDoesNotDivideTwentyThree : 47 ∤ 23
fortySevenDoesNotDivideTwentyThree =
  Div.>⇒∤ fortySevenGreaterThanTwentyThree

fiftyNineDoesNotDivideSeven : 59 ∤ 7
fiftyNineDoesNotDivideSeven =
  Div.>⇒∤ fiftyNineGreaterThanSeven

seventyOneDoesNotDivideEleven : 71 ∤ 11
seventyOneDoesNotDivideEleven =
  Div.>⇒∤ seventyOneGreaterThanEleven

------------------------------------------------------------------------
-- Direct Monster-power-map interpretations are impossible.
------------------------------------------------------------------------

historical23To47CannotBePowerMap :
  (law : PowerMapOrderLaw) →
  PowerMapSubstitution law 23 47 → ⊥
historical23To47CannotBePowerMap law W =
  fortySevenDoesNotDivideTwentyThree
    (powerMapSubstitutionForcesOrderDivisibility law 23 47 W)

historical7To59CannotBePowerMap :
  (law : PowerMapOrderLaw) →
  PowerMapSubstitution law 7 59 → ⊥
historical7To59CannotBePowerMap law W =
  fiftyNineDoesNotDivideSeven
    (powerMapSubstitutionForcesOrderDivisibility law 7 59 W)

historical11To71CannotBePowerMap :
  (law : PowerMapOrderLaw) →
  PowerMapSubstitution law 11 71 → ⊥
historical11To71CannotBePowerMap law W =
  seventyOneDoesNotDivideEleven
    (powerMapSubstitutionForcesOrderDivisibility law 11 71 W)

------------------------------------------------------------------------
-- One record packages the exact mechanistic conclusion without overclaiming.
------------------------------------------------------------------------

record MoonshineEarnPowerMapNoGoBoundary : Set where
  field
    standardPowerOrderDivisibilityConsumed : Bool
    operationalSubstitution23To47Checked : Bool
    operationalSubstitution7To59Checked : Bool
    operationalSubstitution11To71Checked : Bool
    directMonsterPowerMapInterpretationPossible : Bool
    directReplicabilityPowerMapExplanationPossible : Bool
    everyIndirectMoonshineRelationRefuted : Bool

canonicalMoonshineEarnPowerMapNoGoBoundary : MoonshineEarnPowerMapNoGoBoundary
canonicalMoonshineEarnPowerMapNoGoBoundary = record
  { standardPowerOrderDivisibilityConsumed = true
  ; operationalSubstitution23To47Checked = true
  ; operationalSubstitution7To59Checked = true
  ; operationalSubstitution11To71Checked = true
  ; directMonsterPowerMapInterpretationPossible = false
  ; directReplicabilityPowerMapExplanationPossible = false
  ; everyIndirectMoonshineRelationRefuted = false
  }
