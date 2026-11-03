{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact where

------------------------------------------------------------------------
-- N21: LITERAL SIGNED WEIGHTED MAX CUT GRAPH WORD PARSER.
--
-- Wire format matches scripts/karp21_signed_cut_binary_codec.py:
--   gamma(n), gamma(m),
--   m * [gamma(u),gamma(v),gamma(zigzag(weight))], gamma(W).
--
-- Reject malformed gamma words; nonpositive W; u >= v or v >= n;
-- duplicate, reversed, non-ascending edge pairs; extra trailing bits.
-- Each typed output is the ORIGINAL
--   Cut.WeightedCutGraph n, with positive threshold, signed weights,
--   Fin n endpoints, and actual off-diagonal impossibility proofs.
--
-- Unlike a reflected Bool status marker this decoder constructs the
-- graph itself. It preserves binary-encoded n without allocating an
-- n-sized Boolean witness. Its bit-clock, byte-count proof and exact
-- serializer/roundtrip remain independent Karp N21 obligations.
--
-- Sources: Richard Karp (1972); DASHI original Python E20/N21 codec.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (z≤n)
import Data.Nat.Properties as NatP
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as N21
import Data.Integer.Base as Int

record RawEdge : Set where
  constructor raw-edge
  field
    source target : Nat
    signedWeight : ℤ
open RawEdge public

readOneRawEdge :
  Word.BitWord → Maybe (RawEdge × Word.BitWord)
readOneRawEdge word with Gamma.readGamma word
... | nothing = nothing
... | just (u , afterU) with Gamma.readGamma afterU
...   | nothing = nothing
...   | just (v , afterV) with Gamma.readSignedGamma afterV
...     | nothing = nothing
...     | just (w , rest) =
  just (raw-edge u v w , rest)

readRawEdges :
  Nat → Word.BitWord → Maybe (List RawEdge × Word.BitWord)
readRawEdges zero word = just ([] , word)
readRawEdges (suc count) word
  with readOneRawEdge word
... | nothing = nothing
... | just (e , afterHead) with readRawEdges count afterHead
...   | nothing = nothing
...   | just (es , suffix) = just (e ∷ es , suffix)

data PreviousPair : Set where
  noPrevious : PreviousPair
  previous : Nat → Nat → PreviousPair

-- This is the same strict lexicographic pair order as Python's
-- (u,v) > previous. First edge requires only 0 <= u < v < n.
strictAfter : PreviousPair → Nat → Nat → Bool
strictAfter noPrevious u v = true
strictAfter (previous a b) u v with NatP._<?_ a u
... | yes _ = true
... | no _ with NatP._≟_ a u
...   | no _ = false
...   | yes _ with NatP._<?_ b v
...     | yes _ = true
...     | no _ = false

-- A successful edge validation constructs BOTH Fin n endpoints and
-- an actual proof they differ, extracted from Fin decidable equality.
-- No unchecked conversion from Nat to a finite vertex is used.
validateRawEdges :
  (n : Nat) (prev : PreviousPair) →
  List RawEdge → Maybe (List (Cut.SignedUndirectedEdge n))
validateRawEdges n prev [] = just []
validateRawEdges n prev (raw-edge u v w ∷ tail)
  with NatP._<?_ u v | NatP._<?_ v n | strictAfter prev u v
... | yes u<v | yes v<n | true
  with FinP._≟_
    (Fin.fromℕ< (NatP.<-trans u<v v<n))
    (Fin.fromℕ< v<n)
...   | yes _ = nothing
...   | no apart
  with validateRawEdges n (previous u v) tail
...     | nothing = nothing
...     | just rest =
  just
    (Cut.edge
      (Fin.fromℕ< (NatP.<-trans u<v v<n))
      (Fin.fromℕ< v<n)
      apart w ∷ rest)
... | _ | _ | _ = nothing

------------------------------------------------------------------------
-- Exact nested decode:
-- * n,m gamma headers
-- * at least 3 input bits per edge triple, before allocating edges
-- * exactly m triples
-- * gamma(W) with W >= 1
-- * NO remaining suffix.
------------------------------------------------------------------------

decodeGraphWord :
  Word.BitWord → Maybe N21.GraphInstance
decodeGraphWord word with Gamma.readGamma word
... | nothing = nothing
... | just (n , afterN) with Gamma.readGamma afterN
...   | nothing = nothing
...   | just (m , afterM)
  with NatP._≤?_ (m * (suc (suc (suc zero)))) (length afterM)
...     | no _ = nothing
...     | yes _ with readRawEdges m afterM
...       | nothing = nothing
...       | just (raw , afterEdges) with Gamma.readGamma afterEdges
...         | nothing = nothing
...         | just (zero , suffix) = nothing
...         | just (suc threshold , []) with
            validateRawEdges n noPrevious raw
...           | nothing = nothing
...           | just edges =
  just
    (n , Cut.graph edges (+ (suc threshold))
      (Int.+≤+ z≤n , (λ ())))
...         | just (suc threshold , _ ∷ _) = nothing

------------------------------------------------------------------------
-- Literal small examples, including empty and malformed target words.
------------------------------------------------------------------------

decodeEmptyGraphWithPositiveThreshold :
  decodeGraphWord
    (true ∷ true ∷ false ∷ true ∷ false ∷ [])
  ≡ just
    ( zero
    , Cut.graph []
        (+ (suc zero))
        (Int.+≤+ z≤n , (λ ())) )
decodeEmptyGraphWithPositiveThreshold = refl

rejectEmptyGraphWord :
  decodeGraphWord [] ≡ nothing
rejectEmptyGraphWord = refl

rejectIncompleteGraphHeader :
  decodeGraphWord (false ∷ true ∷ []) ≡ nothing
rejectIncompleteGraphHeader = refl

rejectZeroThreshold :
  decodeGraphWord (true ∷ true ∷ true ∷ []) ≡ nothing
rejectZeroThreshold = refl
