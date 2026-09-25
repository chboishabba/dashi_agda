module DASHI.Moonshine.JInvariant369SSP15PrimeInternalFibreExact where

------------------------------------------------------------------------
-- SSP15 PRIME x INTERNAL-LANE FIBRE
--
-- The repository already proves:
--
--   * there are fifteen Ogg/Monster prime lanes;
--   * there are fifteen internal SSP15 lanes = five modes x three phases;
--   * every prime accepts every internal lane.
--
-- Therefore the semantic carrier is not a canonical 15<->15 identification.
-- It is a 15 x 15 fibred/product carrier (before residual geometry), with any
-- chosen bijection selecting only one 15-state gauge section through 225
-- prime/internal combinations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.SSP15PrimeValuedStateExact as PrimeState
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch

PrimeInternalCarrier : Set
PrimeInternalCarrier =
  Lane.MonsterPrimeLane × Internal.SSP15InternalLane

primeInternalCountArithmetic :
  15 * 15 ≡ 225
primeInternalCountArithmetic = refl

attachPrimeInternal :
  (state : PrimeInternalCarrier) →
  PrimeState.ResidualGeometryKind →
  PrimeState.PrimeValuedSSP15State (proj₁ state)
attachPrimeInternal (prime , lane) residual =
  PrimeState.attachInternalLane prime lane residual

attachedInternalLaneExact :
  (state : PrimeInternalCarrier) →
  (residual : PrimeState.ResidualGeometryKind) →
  PrimeState.internalLane (attachPrimeInternal state residual)
  ≡ proj₂ state
attachedInternalLaneExact (prime , lane) residual = refl

------------------------------------------------------------------------
-- Chosen bijection = gauge section, not semantic collapse.
------------------------------------------------------------------------

chosenGaugeSection :
  Lane.MonsterPrimeLane →
  PrimeInternalCarrier
chosenGaugeSection prime =
  prime , Branch.primeToInternal prime

chosenGaugePreservesPrime :
  (prime : Lane.MonsterPrimeLane) →
  proj₁ (chosenGaugeSection prime) ≡ prime
chosenGaugePreservesPrime prime = refl

chosenGaugeUsesChosenLane :
  (prime : Lane.MonsterPrimeLane) →
  proj₂ (chosenGaugeSection prime) ≡ Branch.primeToInternal prime
chosenGaugeUsesChosenLane prime = refl

------------------------------------------------------------------------
-- Existing p71 examples prove the fibre is genuinely larger than the gauge.
------------------------------------------------------------------------

p71NeutralPair : PrimeInternalCarrier
p71NeutralPair =
  Lane.p71 , PrimeState.internalLane PrimeState.p71A1Neutral

p71CounterposedPair : PrimeInternalCarrier
p71CounterposedPair =
  Lane.p71 , PrimeState.internalLane PrimeState.p71A2Counterposed

p71NeutralAndCounterposedAreDistinct :
  p71NeutralPair ≡ p71CounterposedPair → ⊥
p71NeutralAndCounterposedAreDistinct ()

chosenGaugeAtP71IsNotNeutral :
  chosenGaugeSection Lane.p71 ≡ p71NeutralPair → ⊥
chosenGaugeAtP71IsNotNeutral ()

chosenGaugeAtP71IsNotCounterposed :
  chosenGaugeSection Lane.p71 ≡ p71CounterposedPair → ⊥
chosenGaugeAtP71IsNotCounterposed ()

------------------------------------------------------------------------
-- Every fibre still admits every internal lane.
------------------------------------------------------------------------

everyPrimeHasEveryInternalLane :
  (prime : Lane.MonsterPrimeLane) →
  (lane : Internal.SSP15InternalLane) →
  (residual : PrimeState.ResidualGeometryKind) →
  PrimeState.internalLane
    (PrimeState.attachInternalLane prime lane residual)
  ≡ lane
everyPrimeHasEveryInternalLane =
  PrimeState.primeValuationDoesNotRestrictInternalLane

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SSP15PrimeInternalFibreBoundary : Set where
  constructor ssp15-prime-internal-fibre-boundary
  field
    primeLaneCountFifteen : Bool
    internalLaneCountFifteen : Bool
    coarseProductCount225 : Bool
    everyPrimeAcceptsEveryInternalLane : Bool

    chosenBijectionInterpretedAsGaugeSection : Bool
    chosenGaugeExhaustsSemanticCarrier : Bool
    explicitOffGaugeP71StatesOwned : Bool
    primeEqualsInternalLaneSemantically : Bool

open SSP15PrimeInternalFibreBoundary public

canonicalSSP15PrimeInternalFibreBoundary :
  SSP15PrimeInternalFibreBoundary
canonicalSSP15PrimeInternalFibreBoundary =
  ssp15-prime-internal-fibre-boundary
    true true true true
    true false true false
