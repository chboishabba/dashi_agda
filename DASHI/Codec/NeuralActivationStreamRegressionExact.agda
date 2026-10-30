{-# OPTIONS --safe #-}
module DASHI.Codec.NeuralActivationStreamRegressionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Codec.NeuralActivationStateTransportExact as Transport

-- A concrete state-aware predictor: the last acknowledged activation.
-- Sender and receiver both update only after the receiver has decoded.
width : Nat
width = suc (suc zero)

record Session : Set where
  constructor session
  field
    acknowledged : Vec Bool width

open Session

stream : Transport.ActivationStream width
stream = record
  { Context = Session
  ; predict = acknowledged
  }

advance : Session → Vec Bool width → Session
advance previous decoded = session decoded

-- A correct payload reconstructs exactly, and therefore advances the
-- same canonical state on both sides.
one-step-state-agreement : (s : Session) (x : Vec Bool width) →
  advance s (Transport.decode stream s (Transport.encode stream s x))
  ≡ advance s x
one-step-state-agreement s x =
  cong (advance s) (Transport.decode-encode stream s x)

-- Two consecutive packets can predict from the immediately preceding
-- decoded activation, assuming reliable ordered delivery/ACK.
two-step-roundtrip :
  (s : Session) (x y : Vec Bool width) →
  Transport.decode stream
    (advance s (Transport.decode stream s (Transport.encode stream s x)))
    (Transport.encode stream (advance s x) y)
    ≡ y
two-step-roundtrip s x y
  rewrite Transport.decode-encode stream s x =
  Transport.decode-encode stream (advance s x) y

-- The raw fallback predictor never depends on prior session history.
rawPredictor : Transport.ActivationStream width
rawPredictor = record
  { Context = Session
  ; predict = λ _ → false ∷ false ∷ []
  }

rawFallbackRoundtrip : (s : Session) (x : Vec Bool width) →
  Transport.decode rawPredictor s (Transport.encode rawPredictor s x) ≡ x
rawFallbackRoundtrip = Transport.decode-encode rawPredictor

-- Transport substitution is semantics preserving for ANY downstream
-- consumer f, because the same canonical activation is reconstructed.
downstream-congruence : ∀ {B : Set}
  (f : Vec Bool width → B) (s : Session) (x : Vec Bool width) →
  f (Transport.decode stream s (Transport.encode stream s x)) ≡ f x
downstream-congruence f s x =
  cong f (Transport.decode-encode stream s x)
