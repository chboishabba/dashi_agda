module DASHI.Physics.Closure.NSTriadKNGammaSemanticSeparationRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / GAMMA SEMANTIC SEPARATION
--
-- Repository archaeology exposes two distinct quantities historically carrying
-- the surface name `Gamma`:
--
--   packet Gamma    = center-shell quantity / packet energy,
--
-- used by NSPeriodicGammaDerivative and the older Route-B reserve package;
--
--   transfer Gamma  = Q_+ / (2 nu D),
--
-- used by the compact-transfer potential B = Gamma/(1+Gamma).
--
-- These are not definitionally the same observable.  The countermodel below is
-- intentionally observer-level: it stores the already-evaluated packet-Gamma
-- and transfer-Gamma coordinates rather than rebuilding either quotient.  Two
-- states have identical packet Gamma while their transfer Gamma differs.
-- Therefore packet-Gamma coercivity cannot be promoted into transfer-Gamma
-- drift without an explicit same-object bridge theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

record TwoGammaObservation : Set where
  constructor two-gamma-observation
  field
    packetGamma transferGamma : ℚ

open TwoGammaObservation public

stateA stateB : TwoGammaObservation
stateA = two-gamma-observation 1ℚ 0ℚ
stateB = two-gamma-observation 1ℚ 1ℚ

samePacketGamma : packetGamma stateA ≡ packetGamma stateB
samePacketGamma = refl

stateATransferGammaZero : transferGamma stateA ≡ 0ℚ
stateATransferGammaZero = refl

stateBTransferGammaOne : transferGamma stateB ≡ 1ℚ
stateBTransferGammaOne = refl

zeroBelowOne : 0ℚ < 1ℚ
zeroBelowOne = toWitness {a? = 0ℚ <? 1ℚ} _

packetGammaReadoutCannotDetermineTransferGamma :
  (readout : ℚ → ℚ) →
  readout (packetGamma stateA) ≡ transferGamma stateA →
  readout (packetGamma stateB) ≡ transferGamma stateB →
  ⊥
packetGammaReadoutCannotDetermineTransferGamma readout readsA readsB =
  let
    readoutAtAZero : readout (packetGamma stateA) ≡ 0ℚ
    readoutAtAZero = trans readsA stateATransferGammaZero

    readoutAtBOne : readout (packetGamma stateB) ≡ 1ℚ
    readoutAtBOne = trans readsB stateBTransferGammaOne

    readoutSame :
      readout (packetGamma stateA) ≡ readout (packetGamma stateB)
    readoutSame = subst
      (λ gamma → readout (packetGamma stateA) ≡ readout gamma)
      samePacketGamma
      refl

    zeroEqualsOne : 0ℚ ≡ 1ℚ
    zeroEqualsOne =
      trans (sym readoutAtAZero)
        (trans readoutSame readoutAtBOne)

    zeroBelowZero : 0ℚ < 0ℚ
    zeroBelowZero = subst (0ℚ <_) (sym zeroEqualsOne) zeroBelowOne
  in
  ℚP.<-irrefl 0ℚ zeroBelowZero

round82PacketGammaEqualsTransferGammaBySurfaceName : Bool
round82PacketGammaEqualsTransferGammaBySurfaceName = false

round82PacketGammaCannotDetermineTransferGamma : Bool
round82PacketGammaCannotDetermineTransferGamma = true

round82TransferGammaNeedsExplicitSameObjectBridge : Bool
round82TransferGammaNeedsExplicitSameObjectBridge = true

round82PacketGammaCannotDetermineTransferGammaIsTrue :
  round82PacketGammaCannotDetermineTransferGamma ≡ true
round82PacketGammaCannotDetermineTransferGammaIsTrue = refl
