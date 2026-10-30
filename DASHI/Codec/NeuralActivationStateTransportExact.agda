{-# OPTIONS --safe #-}

module DASHI.Codec.NeuralActivationStateTransportExact where

-- DASHI-owned concrete lossless transport refinement. Reuses the original
-- triadic video-codec owner by import; does not alter its claims or imply a
-- measured compression ratio. Discussion-origin architecture: Johl Brown.
-- A state-aware predictor must be identical on both ends. Tensor width is
-- type-level side information; it need not be transmitted per activation.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Combinatorics.TriadicVideoCodecObservationQuotient as Video

xor : Bool → Bool → Bool
xor false x = x
xor true false = true
xor true true = false

xor-involutive : (p x : Bool) → xor p (xor p x) ≡ x
xor-involutive false false = refl
xor-involutive false true = refl
xor-involutive true false = refl
xor-involutive true true = refl

xorVec : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
xorVec [] [] = []
xorVec (p ∷ ps) (x ∷ xs) = xor p x ∷ xorVec ps xs

xorVec-involutive : ∀ {n} (p x : Vec Bool n) →
  xorVec p (xorVec p x) ≡ x
xorVec-involutive [] [] = refl
xorVec-involutive (p ∷ ps) (x ∷ xs)
  rewrite xor-involutive p x | xorVec-involutive ps xs = refl

-- Context can include model identity, layer, expert, previous accepted
-- activations and deterministic predictor state. No distributional or
-- repeated-activation assumption is made.
record ActivationStream (n : Nat) : Set₁ where
  field
    Context : Set
    predict : Context → Vec Bool n

open ActivationStream

encode : ∀ {n} (S : ActivationStream n) →
  Context S → Vec Bool n → Vec Bool n
encode S state actual = xorVec (predict S state) actual

decode : ∀ {n} (S : ActivationStream n) →
  Context S → Vec Bool n → Vec Bool n
decode S state residual = xorVec (predict S state) residual

decode-encode : ∀ {n} (S : ActivationStream n)
  (state : Context S) (actual : Vec Bool n) →
  decode S state (encode S state actual) ≡ actual
decode-encode S state actual =
  xorVec-involutive (predict S state) actual

-- The same observation is recovered if sender and receiver contexts agree.
-- State agreement is an explicit requirement, not inferred from hashes.
transport-sound : ∀ {n} (S : ActivationStream n)
  (sender receiver : Context S) (actual : Vec Bool n) →
  sender ≡ receiver →
  decode S receiver (encode S sender actual) ≡ actual
transport-sound S sender .sender actual refl =
  decode-encode S sender actual

-- Byte/bit layout and entropy packing remain separate refinements.
-- This theorem establishes exact bit-vector reconstruction, NOT a reduced
-- wire size, lower latency, synchronization under packet loss, or ZK soundness.
