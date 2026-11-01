module DASHI.ComputerScience.TernarySignedDigitBinaryCodeBridgeExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just; nothing)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.VerifiedFiniteTritCoder as Code

------------------------------------------------------------------------
-- The repository already owns the exact binary-coded ternary boundary used by
-- FPGA implementations: neg=00, zero=01, pos=10, 11 reserved.

binaryCodeRoundTrip :
  (t : Trit.Trit) → Code.decodeWord (Code.encodeTrit t) ≡ just t
binaryCodeRoundTrip = Code.decode-encode

reservedBinaryPairRejected :
  Code.decodeWord Code.word11 ≡ nothing
reservedBinaryPairRejected = Code.reserved-word-rejected

record BinaryCodedSignedDigitBoundary : Set where
  constructor binaryCodedSignedDigitBoundary
  field
    twoBitsPerTritBaselineLossless : Bool
    fourthCodewordReserved : Bool

canonicalBinaryCodedSignedDigitBoundary : BinaryCodedSignedDigitBoundary
canonicalBinaryCodedSignedDigitBoundary =
  binaryCodedSignedDigitBoundary true true
