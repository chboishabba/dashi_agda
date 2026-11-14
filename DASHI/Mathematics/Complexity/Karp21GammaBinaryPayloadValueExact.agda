{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryPayloadValueExact where

------------------------------------------------------------------------
-- P1: NUMERIC BRIDGE BETWEEN BINARY GAMMA NUMERAL AND PAYLOAD VALUE.
--
-- Source reuse: existing structural successorBits on the binary ℕᵇ
-- carrier, exact literal payloadValue/readLowBits, and stdlib toℕ.
-- The main theorem here is:
--
--     payloadValue (successorBits b) = suc (Bin.toℕ b).
--
-- It handles BOTH even and odd binary constructors and makes the
-- pending gammaReadEncodeRoundTrip a short decoder/encoder transport
-- rather than a new numeral algorithm. Actual machine time is open.
--
-- Source attribution: Elias gamma; Agda Data.Nat.Binary.Base;
-- original DASHI E20/N21 gamma/zigzag codec owner (Karp 1972).
-- This is source-written, not an Agda kernel acceptance receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
import Data.Nat.Binary.Base as Bin
open import Data.Nat.Tactic.RingSolver using (solve-∀)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Enc
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Dec

-- This is only semiring algebra, independent of binary word syntax.
twiceDistributesOverPayload :
  (a b c d : Nat) →
  a * (2 * b) + (2 * c + d)
    ≡ 2 * (a * b + c) + d
twiceDistributesOverPayload = solve-∀

-- Appending ONE bit (not a whole gamma header) doubles the numeric
-- value of the previous bitstring, then adds the new bit.
payloadValueAppendBit :
  (bits : Word.BitWord) (bit : Bool) →
  Dec.payloadValue (bits ++ (bit ∷ []))
    ≡ 2 * Dec.payloadValue bits + Dec.bitNat bit
payloadValueAppendBit [] false = refl
payloadValueAppendBit [] true = refl
payloadValueAppendBit (first ∷ rest) bit
  rewrite ListP.length-++-sucʳ rest bit []
        | ListP.++-identityʳ rest
        | payloadValueAppendBit rest bit =
  twiceDistributesOverPayload
    (Dec.bitNat first)
    (Dec.pow2 (length rest))
    (Dec.payloadValue rest)
    (Dec.bitNat bit)

twiceSuccExact :
  (n : Nat) → 2 * suc n ≡ suc (suc (2 * n))
twiceSuccExact n rewrite NatP.*-suc 2 n = refl

successorBitsNumericValue :
  (n : Bin.ℕᵇ) →
  Dec.payloadValue (Enc.successorBits n) ≡ suc (Bin.toℕ n)
successorBitsNumericValue Bin.zero = refl
successorBitsNumericValue (Bin.2[1+ n ])
  rewrite payloadValueAppendBit (Enc.successorBits n) true
        | successorBitsNumericValue n
        | NatP.+-comm (2 * suc (Bin.toℕ n)) 1 =
  refl
successorBitsNumericValue (Bin.1+[2 n ])
  rewrite payloadValueAppendBit (Enc.successorBits n) false
        | successorBitsNumericValue n
        | NatP.+-identityʳ (2 * suc (Bin.toℕ n))
        | twiceSuccExact (Bin.toℕ n) =
  refl
