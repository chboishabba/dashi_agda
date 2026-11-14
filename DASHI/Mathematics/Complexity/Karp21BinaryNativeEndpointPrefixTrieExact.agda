{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeEndpointPrefixTrieExact where

------------------------------------------------------------------------
-- N21 actual bit-native endpoint-identity sharing.
--
-- Canonical gamma successor binary addresses form trie keys. Every
-- occurrence follows one root-to-leaf path, so repeated occurrences
-- reuse the prior identity/label instead of scanning all prior pairs.
-- The graph parser owns the validity/canonicality of these keys.
--
-- No prime-power magnitude expansion, hash oracle or unary Fin n.
-- The comparison to original endpointConsistent for ALL graph words,
-- and machine-tape pointer/allocation costs, remain separate gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Base using (List; length)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact as Eq

data AddressTrie : Set where
  empty : AddressTrie
  node : Maybe Bool → AddressTrie → AddressTrie → AddressTrie

-- Returns nothing ONLY on a conflicting assignment to the same
-- full binary address. No comparison to unary decoded addresses.
insertAddress :
  Word.BitWord → Bool → AddressTrie → Maybe AddressTrie
insertAddress [] value empty =
  just (node (just value) empty empty)
insertAddress [] value (node nothing left right) =
  just (node (just value) left right)
insertAddress [] value (node (just old) left right)
  with Eq.bitEqual value old
... | false = nothing
... | true = just (node (just old) left right)

insertAddress (false ∷ key) value empty
  with insertAddress key value empty
... | nothing = nothing
... | just left = just (node nothing left empty)
insertAddress (true ∷ key) value empty
  with insertAddress key value empty
... | nothing = nothing
... | just right = just (node nothing empty right)

insertAddress (false ∷ key) value (node stored left right)
  with insertAddress key value left
... | nothing = nothing
... | just next = just (node stored next right)
insertAddress (true ∷ key) value (node stored left right)
  with insertAddress key value right
... | nothing = nothing
... | just next = just (node stored left next)

-- One recursive descent per input bit and one terminal label check.
addressInsertionVisits : Word.BitWord → Nat
addressInsertionVisits key = suc (length key)

addressInsertEmpty :
  (value : Bool) →
  insertAddress [] value empty ≡
    just (node (just value) empty empty)
addressInsertEmpty value = refl

addressInsertSameEmpty :
  (value : Bool) →
  insertAddress [] value (node (just value) empty empty)
    ≡ just (node (just value) empty empty)
addressInsertSameEmpty false = refl
addressInsertSameEmpty true = refl

addressInsertOppositeRejected :
  insertAddress [] true (node (just false) empty empty) ≡ nothing
addressInsertOppositeRejected = refl

admitAll :
  List (Word.BitWord × Bool) → AddressTrie → Bool
admitAll [] trie = true
admitAll ((key , value) ∷ occurrences) trie
  with insertAddress key value trie
... | nothing = false
... | just next = admitAll occurrences next

endpointOccurrenceTrieAccepts :
  List (Word.BitWord × Bool) → Bool
endpointOccurrenceTrieAccepts occurrences =
  admitAll occurrences empty

emptyOccurrencesAccepted :
  endpointOccurrenceTrieAccepts [] ≡ true
emptyOccurrencesAccepted = refl
