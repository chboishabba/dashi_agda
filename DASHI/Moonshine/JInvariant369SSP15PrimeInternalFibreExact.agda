module DASHI.Moonshine.JInvariant369SSP15PrimeInternalFibreExact where

------------------------------------------------------------------------
-- SSP15 LANE + ATTACHED INTERNAL OBSERVER STATE
--
-- SSP15 itself is the fifteen Ogg/Monster prime lanes.
--
-- Separately, the repo has a five-mode x three-phase internal presentation that
-- may be attached to a prime lane as additional state.  Therefore 15 x 15 = 225
-- counts enriched (prime, internal-state) combinations.  It is NOT the number
-- of SSP15 lanes and does not replace the canonical Ogg carrier.
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
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
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
-- Canonical signed lift from the FULL prime/internal pair.
--
-- Unlike the earlier gauge helper, this does not derive the selected prime
-- from the internal lane.  Prime and internal mode remain independent; only
-- the balanced phase is lifted to signed multiplicity.
------------------------------------------------------------------------

primeInternalToPointedSigned :
  PrimeInternalCarrier →
  Branch.PointedSignedSSPLane
primeInternalToPointedSigned (prime , lane) =
  Branch.pointed-signed-ssp-lane
    prime
    (Branch.phaseToUnitMultiplicity (proj₂ lane))

primeInternalPointedPrimeExact :
  (state : PrimeInternalCarrier) →
  Branch.selectedPrime (primeInternalToPointedSigned state)
  ≡ proj₁ state
primeInternalPointedPrimeExact (prime , lane) = refl

primeInternalPointedPhaseExact :
  (state : PrimeInternalCarrier) →
  Branch.unitMultiplicityToPhase
    (Branch.signedMultiplicity (primeInternalToPointedSigned state))
  ≡ proj₂ (proj₂ state)
primeInternalPointedPhaseExact (prime , (mode , phase)) =
  Branch.phaseCoarseRoundTrip phase

primeInternalValuation :
  PrimeInternalCarrier →
  Signed.SSPValuation
primeInternalValuation state =
  Branch.pointedSignedValuation (primeInternalToPointedSigned state)

primeInternalValuationOwnLane :
  (state : PrimeInternalCarrier) →
  primeInternalValuation state
    (Branch.lanePrimeToSignedPrime (proj₁ state))
  ≡
  Branch.phaseToUnitMultiplicity (proj₂ (proj₂ state))
primeInternalValuationOwnLane state =
  Branch.pointedValuationOwnLane (primeInternalToPointedSigned state)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SSP15PrimeInternalFibreBoundary : Set where
  constructor ssp15-prime-internal-fibre-boundary
  field
    primeLaneCountFifteen : Bool
    ssp15LaneCarrierIsOggPrimeCarrier : Bool
    internalLaneCountFifteen : Bool
    coarseProductCount225 : Bool
    product225IsSSP15LaneCount : Bool
    everyPrimeAcceptsEveryInternalLane : Bool

    chosenBijectionInterpretedAsGaugeSection : Bool
    chosenGaugeExhaustsSemanticCarrier : Bool
    explicitOffGaugeP71StatesOwned : Bool
    canonicalSignedLiftUsesPrimeInternalPair : Bool
    primeEqualsInternalLaneSemantically : Bool

open SSP15PrimeInternalFibreBoundary public

canonicalSSP15PrimeInternalFibreBoundary :
  SSP15PrimeInternalFibreBoundary
canonicalSSP15PrimeInternalFibreBoundary =
  ssp15-prime-internal-fibre-boundary
    true true true true false true
    true false true true false
