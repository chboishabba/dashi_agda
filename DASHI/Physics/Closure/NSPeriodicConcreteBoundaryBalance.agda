module DASHI.Physics.Closure.NSPeriodicConcreteBoundaryBalance where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.Closure.NSPeriodicConcreteCompactGamma using (monus)

------------------------------------------------------------------------
-- Exact eighth-unit bookkeeping for the four candidate boundary ledgers.
--
-- These are arithmetic feasibility checks only.  Equality with the actual PDE
-- Dini derivatives is deliberately not asserted.
------------------------------------------------------------------------

gammaSource gammaLoss gammaMargin : Nat
gammaSource = 20
gammaLoss = 18
gammaMargin = monus gammaSource gammaLoss

packetSource packetLoss packetMargin : Nat
packetSource = 18
packetLoss = 16
packetMargin = monus packetSource packetLoss

offPacketSource offPacketLoss offPacketMargin : Nat
offPacketSource = 16
offPacketLoss = 15
offPacketMargin = monus offPacketSource offPacketLoss

sizeSource sizeLoss sizeMargin : Nat
sizeSource = 14
sizeLoss = 14
sizeMargin = monus sizeSource sizeLoss

gammaMarginIsQuarter : gammaMargin ≡ 2
gammaMarginIsQuarter = refl

packetMarginIsQuarter : packetMargin ≡ 2
packetMarginIsQuarter = refl

offPacketMarginIsEighth : offPacketMargin ≡ 1
offPacketMarginIsEighth = refl

sizeMarginIsZero : sizeMargin ≡ 0
sizeMarginIsZero = refl

gammaCandidateStrict packetCandidateStrict offPacketCandidateStrict : Bool
gammaCandidateStrict = true
packetCandidateStrict = true
offPacketCandidateStrict = true

sizeCandidateStrict : Bool
sizeCandidateStrict = false

allFourCandidateLedgersStrict : Bool
allFourCandidateLedgersStrict = false

actualBoundaryDerivativeIdentitiesProved : Bool
actualBoundaryDerivativeIdentitiesProved = false

universalDiniInwardnessPromoted : Bool
universalDiniInwardnessPromoted = false
