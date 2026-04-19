module DASHI.Arithmetic.ArithmeticPrimeProfileBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Nat using (_≤_)

open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; embed
  ; alphaAt
  ; betaAt
  ; gammaAt
  ; deltaAt
  ; embed-primeContribution
  )
open import DASHI.Arithmetic.NatBoolEquality using
  ( natEq
  )
import DASHI.Arithmetic.ValuationLemmas as VL
open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; normalizeAddCanonical
  )
open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-canonical
  )
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateCancellationPressure
  ; StateSupportPressure
  ; normalizeAddOneStepSupportBound
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( PrimeContributionVec
  ; primeContribution
  ; primeIndexedPressureAt
  ; sum15
  ; normalizeAdd⇒primeIndexedBounded
  )
open import DASHI.Statistics.PrimeProfileStats using
  ( PrimeProfileStats
  ; primeProfileWeights
  )

------------------------------------------------------------------------
-- Bridge profile
--
-- This is the first thin arithmetic-to-prime-profile surface.
-- It keeps the local valuation hooks, the tracked Vec15 carrier, and the
-- prime-profile stats object together without claiming more semantics than
-- the current repo can justify.

record ArithmeticPrimeProfileBridgeProfile : Set₁ where
  field
    lhs : Int
    rhs : Int
    embeddedState : NormalizeAddState
    primeProfile : PrimeProfileStats
    weights : PrimeContributionVec
    carrierProjection : PrimeContributionVec
    vpa : SSP → Int → Int → Nat
    vpb : SSP → Int → Int → Nat
    vpc : SSP → Int → Int → Nat
    wallBit : SSP → Int → Int → Bool
    localContribution : SSP → Int → Int → Nat
    weightsMatchProfile :
      primeProfileWeights primeProfile ≡ weights
    carrierProjectionMatches :
      carrierProjection ≡ weights

open ArithmeticPrimeProfileBridgeProfile public

------------------------------------------------------------------------
-- Minimal deterministic hooks.

vpaBridge : SSP → Int → Int → Nat
vpaBridge = alphaAt

vpbBridge : SSP → Int → Int → Nat
vpbBridge = betaAt

vpcBridge : SSP → Int → Int → Nat
vpcBridge = gammaAt

localContributionBridge : SSP → Int → Int → Nat
localContributionBridge = deltaAt

------------------------------------------------------------------------
-- Missing semantics are isolated here.

postulate
  bridgePrimeProfile : Int → Int → PrimeProfileStats
  bridgePrimeProfileWeights :
    ∀ x y →
    primeProfileWeights (bridgePrimeProfile x y) ≡
    primeIndexedPressureAt (embed x y)

wallBitBridge : SSP → Int → Int → Bool
wallBitBridge p x y = natEq (vpaBridge p x y) (vpbBridge p x y)

------------------------------------------------------------------------
-- A canonical bridge profile for a pair of embedded arithmetic states.

bridgeProfile : Int → Int → ArithmeticPrimeProfileBridgeProfile
bridgeProfile x y = record
  { lhs = x
  ; rhs = y
  ; embeddedState = embed x y
  ; primeProfile = bridgePrimeProfile x y
  ; weights = primeIndexedPressureAt (embed x y)
  ; carrierProjection = primeIndexedPressureAt (embed x y)
  ; vpa = vpaBridge
  ; vpb = vpbBridge
  ; vpc = vpcBridge
  ; wallBit = wallBitBridge
  ; localContribution = localContributionBridge
  ; weightsMatchProfile = bridgePrimeProfileWeights x y
  ; carrierProjectionMatches = refl
  }

------------------------------------------------------------------------
-- Deterministic bridge surfaces.

offWallZero :
  ∀ p x y →
  wallBitBridge p x y ≡ false →
  localContributionBridge p x y ≡ zero
offWallZero p x y wallFalse = VL.offWallZero p x y wallFalse

localContributionToProfileWeight :
  ∀ p x y →
  localContributionBridge p x y ≡ primeContribution p (embed x y)
localContributionToProfileWeight p x y =
  sym (embed-primeContribution p x y)

normalizeCompatibility :
  ∀ x y →
  normalizeAddCanonical (normalizeAdd (embed x y))
normalizeCompatibility x y =
  normalizeAdd-canonical (embed x y)

embeddedStateOneStepSupportBound :
  ∀ x y →
  StateCancellationPressure (normalizeAdd (embed x y)) ≤
  StateSupportPressure (normalizeAdd (embed x y))
embeddedStateOneStepSupportBound x y =
  normalizeAddOneStepSupportBound (embed x y)

embeddedProfileOneStepSupportBound :
  ∀ x y →
  sum15 (primeIndexedPressureAt (normalizeAdd (embed x y))) ≤
  StateSupportPressure (normalizeAdd (embed x y))
embeddedProfileOneStepSupportBound x y =
  normalizeAdd⇒primeIndexedBounded (embed x y)

embeddedProfileCarrier :
  Int → Int → PrimeContributionVec
embeddedProfileCarrier x y = primeIndexedPressureAt (embed x y)

embeddedProfileScore :
  Int → Int → Nat
embeddedProfileScore x y = sum15 (embeddedProfileCarrier x y)

------------------------------------------------------------------------
-- Minimal concrete package for the embedded prime-profile lane.
--
-- This is intentionally weaker than any quadratic/theorem-side bridge:
-- it records the embedded profile carrier, the induced scalar score, and
-- the one-step support bound, without identifying that score with a
-- theorem-side quadratic.

record EmbeddedPrimeProfileMeasurement : Set₁ where
  field
    lhs : Int
    rhs : Int
    embeddedState : NormalizeAddState
    carrier : PrimeContributionVec
    score : Nat
    scoreMatchesCarrier :
      score ≡ sum15 carrier
    normalizedSupportBound :
      sum15 (primeIndexedPressureAt (normalizeAdd embeddedState))
      ≤
      StateSupportPressure (normalizeAdd embeddedState)

open EmbeddedPrimeProfileMeasurement public

embeddedPrimeProfileMeasurement :
  Int → Int → EmbeddedPrimeProfileMeasurement
embeddedPrimeProfileMeasurement x y =
  record
    { lhs = x
    ; rhs = y
    ; embeddedState = embed x y
    ; carrier = embeddedProfileCarrier x y
    ; score = embeddedProfileScore x y
    ; scoreMatchesCarrier = refl
    ; normalizedSupportBound = embeddedProfileOneStepSupportBound x y
    }
