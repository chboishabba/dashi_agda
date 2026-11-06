{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedInspectionClockExact where

------------------------------------------------------------------------
-- K05: ALL-WORD BINARY-NATIVE SIGNED TOKEN INSPECTION CLOCK.
--
-- This is a concrete structural cost bound for the selected executable
-- gamma scanner followed by the selected last-bit sign splitter.
-- It applies to malformed and truncated words as well as valid tokens.
--
-- It does NOT price copying/allocating bit lists, random-access tapes,
-- the graph parser, graph arithmetic or the full N21 machine.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (length)
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed

-- The sign splitter makes at most one inspection per source bit plus
-- its terminal branch, even if the original gamma input was rejected.
signInspectionOnOriginalWord : Word.BitWord → Nat
signInspectionOnOriginalWord word =
  Signed.splitLastInspectionWork word

signInspectionOnOriginalWordLinear :
  (word : Word.BitWord) →
  signInspectionOnOriginalWord word ≤ suc (length word)
signInspectionOnOriginalWordLinear =
  Signed.splitLastInspectionLinear

-- For the real signed reader, the second scan is over the gamma
-- payload, a subword of the input. A full-input scan overcharges it,
-- making this unconditional bound conservative.
signedTokenInspectionEnvelope : Word.BitWord → Nat
signedTokenInspectionEnvelope word =
  Gamma.gammaNativeInspectionWork word
    + signInspectionOnOriginalWord word

twoPassLinearBudget : Word.BitWord → Nat
twoPassLinearBudget word =
  suc (length word) + suc (length word)

-- Explicit addition monotonicity avoids treating the two machine
-- inspections as a single unit-cost arithmetic operation.
+-mono-two :
  {a b c d : Nat} → a ≤ b → c ≤ d → a + c ≤ b + d
+-mono-two z≤n z≤n = z≤n
+-mono-two {a = zero} {b = suc b} z≤n (s≤s cd) =
  s≤s (+-mono-two {a = zero} {b = b} z≤n cd)
+-mono-two {a = suc a} {b = suc b} (s≤s ab) cd =
  s≤s (+-mono-two {a = a} {b = b} ab cd)

signedTokenInspectionLinear :
  (word : Word.BitWord) →
  signedTokenInspectionEnvelope word ≤ twoPassLinearBudget word
signedTokenInspectionLinear word =
  +-mono-two
    (Gamma.gammaNativeInspectionLinear word)
    (Signed.splitLastInspectionLinear word)
