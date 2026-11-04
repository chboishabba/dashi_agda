module DASHI.Foundations.C3BraidEndpointMobiusExact where

-- Endpoints alone determine neither ribbon framing nor transverse twist.
-- This module models an explicit *additional* orientation-transport bit
-- and imports the existing order-two Base369 Mobius gate.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

import Base369 as Base
import DASHI.Foundations.Base369MobiusTransport as Mobius

data EndpointOrientation : Set where
  forward reversed : EndpointOrientation

flip : EndpointOrientation → EndpointOrientation
flip forward = reversed
flip reversed = forward

doubleFlip : ∀ o → flip (flip o) ≡ o
doubleFlip forward = refl
doubleFlip reversed = refl

toPolarity : EndpointOrientation → Mobius.OrientationPolarity
toPolarity forward = Mobius.positive
toPolarity reversed = Mobius.negative

fromPolarity : Mobius.OrientationPolarity → EndpointOrientation
fromPolarity Mobius.positive = forward
fromPolarity Mobius.negative = reversed

orientationRoundTrip : ∀ o → fromPolarity (toPolarity o) ≡ o
orientationRoundTrip forward = refl
orientationRoundTrip reversed = refl

mobiusFlipCompatible : ∀ o →
  fromPolarity (Mobius.flipOrientationPolarity (toPolarity o))
    ≡ flip o
mobiusFlipCompatible forward = refl
mobiusFlipCompatible reversed = refl

record EndpointObservation : Set where
  constructor observe
  field
    leftOrientation : EndpointOrientation
    rightOrientation : EndpointOrientation
open EndpointObservation public

-- One-end and two-end flips are DIFFERENT observable operations.
flipLeft : EndpointObservation → EndpointObservation
flipLeft (observe a b) = observe (flip a) b

flipRight : EndpointObservation → EndpointObservation
flipRight (observe a b) = observe a (flip b)

flipBoth : EndpointObservation → EndpointObservation
flipBoth (observe a b) = observe (flip a) (flip b)

flipLeftTwice : ∀ e → flipLeft (flipLeft e) ≡ e
flipLeftTwice (observe forward forward) = refl
flipLeftTwice (observe forward reversed) = refl
flipLeftTwice (observe reversed forward) = refl
flipLeftTwice (observe reversed reversed) = refl

flipRightTwice : ∀ e → flipRight (flipRight e) ≡ e
flipRightTwice (observe forward forward) = refl
flipRightTwice (observe forward reversed) = refl
flipRightTwice (observe reversed forward) = refl
flipRightTwice (observe reversed reversed) = refl

flipBothIsLeftThenRight : ∀ e →
  flipBoth e ≡ flipLeft (flipRight e)
flipBothIsLeftThenRight (observe forward forward) = refl
flipBothIsLeftThenRight (observe forward reversed) = refl
flipBothIsLeftThenRight (observe reversed forward) = refl
flipBothIsLeftThenRight (observe reversed reversed) = refl

-- Concrete Base369 phase is invariant under its model Mobius transport.
base369PhaseInvariant : ∀ h →
  Mobius.hexTriadicPhase (Mobius.mobiusTransport h)
    ≡ Mobius.hexTriadicPhase h
base369PhaseInvariant = Mobius.mobiusTransport-preservesTriadicPhase

base369DoubleTraversal : ∀ h →
  Mobius.mobiusTransport (Mobius.mobiusTransport h) ≡ h
base369DoubleTraversal = Mobius.mobiusTransport-squares-to-identity

-- No theorem here identifies a physical end rotation with this finite
-- transport, nor infers Z-valued ribbon framing from an orientation bit.
