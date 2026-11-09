{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact where

------------------------------------------------------------------------
-- P0-B/F original N21 chronological endpoint consistency, executable
-- WITHOUT unary Nat endpoint/equality. Each source edge contributes
-- its two original sparse witness label bits in order.
-- compareLE decides vertex identity independent of binary padding.
-- A typed original source Nat observational theorem remains B5.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Compare

BinaryEndpointHistory : Set
BinaryEndpointHistory = List (Word.BitWord × Bool)

-- The actual original endpointConsistent scans ALL historical
-- occurrences. The native source does likewise, but all vertex
-- equality is binary, without decoding address magnitudes.
endpointConsistentBinary :
  Word.BitWord → Bool → BinaryEndpointHistory → Bool
endpointConsistentBinary vertex selected [] = true
endpointConsistentBinary vertex selected ((other , observed) ∷ rest)
  with Compare.equalNativeLE vertex other
... | true =
  Boolean.andBool
    (Boolean.boolEqual selected observed)
    (endpointConsistentBinary vertex selected rest)
... | false = endpointConsistentBinary vertex selected rest

-- Chronological source raw-list state adds u then v to the *front*
-- of the previously accumulated history; deliberately no sorting or
-- deduplication that could change the original consistency semantics.
recordBinaryEndpointPair :
  Word.BitWord → Word.BitWord → Bool → Bool →
  BinaryEndpointHistory → BinaryEndpointHistory
recordBinaryEndpointPair u v a b history =
  (u , a) ∷ (v , b) ∷ history

-- Actual original first-enabled edge advancement requires BOTH
-- original vertex-label consistency tests, before history mutation.
endpointPairConsistentBinary :
  Word.BitWord → Word.BitWord → Bool → Bool →
  BinaryEndpointHistory → Bool
endpointPairConsistentBinary u v a b history =
  Boolean.andBool
    (endpointConsistentBinary u a history)
    (endpointConsistentBinary v b history)

-- Directly executed source sanity cases; no alternate Nat meaning.
emptyHistoryConsistent :
  (vertex : Word.BitWord) (label : Bool) →
  endpointConsistentBinary vertex label [] ≡ true
emptyHistoryConsistent vertex label = refl
