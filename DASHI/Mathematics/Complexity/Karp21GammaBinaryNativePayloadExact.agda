{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact where

------------------------------------------------------------------------
-- K05 N21: BINARY-NATIVE, SUFFIX-PRESERVING ELIAS-GAMMA PAYLOAD READER.
--
-- The old readGamma computes (pow2 zeros + payloadValue payload) - 1
-- as a unary Nat. This parser instead returns the canonical bitword
-- of n+1: [true] ++ payload. No exponentially large Nat is allocated.
-- It uses the SAME original Elias gamma codewords and strict suffix
-- grammar, and proves left inverse of the ORIGINAL binary encoder.
--
-- Executable recursion: readPayload structurally decreases k;
-- scanZeros structurally decreases the remaining input.
-- No axiom, arbitrary fuel, self-referential machine cost or oracle.
-- An all-input tape-clock theorem is a further separate goal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (_++_; length)
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import Data.Nat.Binary.Base as Bin

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Numeric

readPayload :
  Nat → Word.BitWord → Maybe (Word.BitWord × Word.BitWord)
readPayload zero suffix = just ([] , suffix)
readPayload (suc k) [] = nothing
readPayload (suc k) (b ∷ rest) with readPayload k rest
... | nothing = nothing
... | just (payload , suffix) = just (b ∷ payload , suffix)

readPayloadAppendExact :
  (payload suffix : Word.BitWord) →
  readPayload (length payload) (payload ++ suffix)
    ≡ just (payload , suffix)
readPayloadAppendExact [] suffix = refl
readPayloadAppendExact (b ∷ payload) suffix
  rewrite readPayloadAppendExact payload suffix = refl

scanZeros :
  Nat → Word.BitWord → Maybe (Word.BitWord × Word.BitWord)
scanZeros count [] = nothing
scanZeros count (false ∷ rest) =
  scanZeros (suc count) rest
scanZeros count (true ∷ rest) with readPayload count rest
... | nothing = nothing
... | just (payload , suffix) =
  just (true ∷ payload , suffix)

readGammaBinary :
  Word.BitWord → Maybe (Word.BitWord × Word.BitWord)
readGammaBinary = scanZeros zero

scanZerosPrefixExact :
  (seen zeros : Nat) (suffix : Word.BitWord) →
  scanZeros seen (Gamma.zeroPrefix zeros ++ (true ∷ suffix))
    ≡ scanZeros (seen + zeros) (true ∷ suffix)
scanZerosPrefixExact seen zero suffix
  rewrite NatP.+-identityʳ seen = refl
scanZerosPrefixExact seen (suc zeros) suffix
  rewrite NatP.+-suc seen zeros =
  scanZerosPrefixExact (suc seen) zeros suffix

readGammaBinaryPayloadExact :
  (payload suffix : Word.BitWord) →
  readGammaBinary
    (Gamma.zeroPrefix (length payload)
      ++ (true ∷ (payload ++ suffix)))
    ≡ just (true ∷ payload , suffix)
readGammaBinaryPayloadExact payload suffix
  rewrite scanZerosPrefixExact zero (length payload)
    (payload ++ suffix)
        | readPayloadAppendExact payload suffix =
  refl

binaryOriginalNumeralSuffix :
  (b : Bin.ℕᵇ) (suffix : Word.BitWord) →
  readGammaBinary
    (Gamma.zeroPrefix (Bin.size b) ++
      (Gamma.successorBits b ++ suffix))
      ≡ just (Gamma.successorBits b , suffix)
binaryOriginalNumeralSuffix b suffix
  with Gamma.successorBitsLeadingOne b
... | payload , starts
  rewrite sym (Numeric.successorPayloadLength b payload starts)
        | starts
        | readGammaBinaryPayloadExact payload suffix = refl

-- The genuine original Karp encoder is now read by the bit-native
-- source without ever reconstructing the numerical magnitude.
gammaOriginalEncodeNativeSuffix :
  (n : Nat) (suffix : Word.BitWord) →
  readGammaBinary (Gamma.encodeGammaNat n ++ suffix)
    ≡ just (Gamma.successorBits (Bin.fromℕ n) , suffix)
gammaOriginalEncodeNativeSuffix n suffix
  rewrite Gamma.gammaPrefixExactlyBinarySize n
        | ListP.++-assoc
            (Gamma.zeroPrefix (Bin.size (Bin.fromℕ n)))
            (Gamma.successorBits (Bin.fromℕ n))
            suffix =
  binaryOriginalNumeralSuffix (Bin.fromℕ n) suffix

-- Exact wire-level encoding shapes; numerical reconstruction is
-- intentionally a separate observation from reading a binary codeword.

------------------------------------------------------------------------
-- The parser's own bit-inspection clock. Both cost functions mirror
-- the exact recursive calls of readPayload and scanZeros.
------------------------------------------------------------------------

payloadInspectionWork : Nat → Word.BitWord → Nat
payloadInspectionWork zero rest = 1
payloadInspectionWork (suc k) [] = 1
payloadInspectionWork (suc k) (_ ∷ rest) =
  suc (payloadInspectionWork k rest)

payloadInspectionLinear :
  (k : Nat) (bits : Word.BitWord) →
  payloadInspectionWork k bits ≤ suc (length bits)
payloadInspectionLinear zero bits = s≤s z≤n
payloadInspectionLinear (suc k) [] = s≤s z≤n
payloadInspectionLinear (suc k) (_ ∷ rest) =
  s≤s (payloadInspectionLinear k rest)

scanInspectionWork : Nat → Word.BitWord → Nat
scanInspectionWork seen [] = 1
scanInspectionWork seen (false ∷ rest) =
  suc (scanInspectionWork (suc seen) rest)
scanInspectionWork seen (true ∷ rest) =
  suc (payloadInspectionWork seen rest)

scanInspectionLinear :
  (seen : Nat) (bits : Word.BitWord) →
  scanInspectionWork seen bits ≤ suc (length bits)
scanInspectionLinear seen [] = s≤s z≤n
scanInspectionLinear seen (false ∷ rest) =
  s≤s (scanInspectionLinear (suc seen) rest)
scanInspectionLinear seen (true ∷ rest) =
  s≤s (payloadInspectionLinear seen rest)

gammaNativeInspectionWork : Word.BitWord → Nat
gammaNativeInspectionWork = scanInspectionWork zero

gammaNativeInspectionLinear :
  (bits : Word.BitWord) →
  gammaNativeInspectionWork bits ≤ suc (length bits)
gammaNativeInspectionLinear bits = scanInspectionLinear zero bits

-- This pays the number of input-symbol inspections for ONE literal
-- gamma token. It does not count machine-head movement for a tape
-- representation, allocation, or full graph-level many-token scan.
