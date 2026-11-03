{-# OPTIONS --safe #-}
module DASHI.Reasoning.IEEEOrbitSignWitnessBidiExact where

-- Finite symbolic sign-bit carrier for IEEE block codecs.
-- This models sign XOR and a transported witness, not byte order,
-- zlib framing, payload bounds, NaN arithmetic or PyTorch execution.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

flip : Bool → Bool
flip false = true
flip true = false

flipTwice : (s : Bool) → flip (flip s) ≡ s
flipTwice false = refl
flipTwice true = refl

record EncodedWord : Set where
  constructor word
  field
    magnitudeBits : List Bool
    signBit : Bool
open EncodedWord public

flipSign : EncodedWord → EncodedWord
flipSign (word bits s) = word bits (flip s)

flipSignTwice : (w : EncodedWord) → flipSign (flipSign w) ≡ w
flipSignTwice (word bits false) = refl
flipSignTwice (word bits true) = refl

-- Canonical sign + transport witness: enough to reproduce signed zero
-- and any arbitrary magnitude/payload bits, including symbolic NaNs.
record Packet : Set where
  constructor packet
  field
    canonical : EncodedWord
    orientation : Bool
open Packet public

encode : EncodedWord → Packet
encode (word bits false) = packet (word bits false) false
encode (word bits true)  = packet (word bits false) true

decode : Packet → EncodedWord
decode (packet w false) = w
decode (packet w true) = flipSign w

decoderEncoderRoundtrip :
  (w : EncodedWord) → decode (encode w) ≡ w
decoderEncoderRoundtrip (word bits false) = refl
decoderEncoderRoundtrip (word bits true) = refl

-- Upstream source representation uses a lexical comparison of a whole
-- floating block with its globally inverted block; this canonical
-- sign convention alone is NOT proven equivalent to that comparison.
-- Remaining real-byte proof needs layout, packed mask, stream framing.
