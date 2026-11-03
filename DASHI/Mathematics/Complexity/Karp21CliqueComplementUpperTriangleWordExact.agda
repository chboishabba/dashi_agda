{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CliqueComplementUpperTriangleWordExact where

------------------------------------------------------------------------
-- E05: EXACT BINARY OFF-DIAGONAL COMPLEMENT OPERATOR.
--
-- Karp's CLIQUE -> VERTEX COVER uses the complement of a SIMPLE graph.
-- A canonical upper-triangular edge-incidence encoding includes only
-- off-diagonal addresses (i,j), i<j, in known sorted order.
--
-- On THAT EDGE BIT BLOCK the original simple graph complement is
-- bit-by-bit Bool negation. There are no diagonal bits to accidentally
-- turn into self-loops. Source-written results here:
--  * involution of literal bit-word complement;
--  * preservation of the EXACT original binary Word length;
--  * exact one-pass emitted bit count.
--
-- This is NOT yet a complete E05 encoded polynomial reduction: it
-- must be welded to a strict canonical simple-graph parser, its
-- upper-pair ordering, the k->n-k cover cardinality and a true machine
-- time certificate. No false all-graphs complement language is claimed.
--
-- Original: R. M. Karp (1972); DASHI SimpleGraphComplementExact,
-- CliqueVertexCoverExact; pure Boolean/list Agda stdlib.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden

-- The same truth table as Karp21CliqueVertexCoverExact.negBool,
-- implemented in the small transitive-safe binary owner.
negBool : Bool → Bool
negBool true = false
negBool false = true

negBoolInvolution : (bit : Bool) → negBool (negBool bit) ≡ bit
negBoolInvolution true = refl
negBoolInvolution false = refl

complementUpperTriangleWord : Word.BitWord → Word.BitWord
complementUpperTriangleWord [] = []
complementUpperTriangleWord (bit ∷ rest) =
  negBool bit ∷ complementUpperTriangleWord rest

complementUpperTriangleInvolution :
  (bits : Word.BitWord) →
  complementUpperTriangleWord (complementUpperTriangleWord bits)
    ≡ bits
complementUpperTriangleInvolution [] = refl
complementUpperTriangleInvolution (bit ∷ rest)
  rewrite negBoolInvolution bit
        | complementUpperTriangleInvolution rest = refl

complementUpperTrianglePreservesLength :
  (bits : Word.BitWord) →
  Word.encodingSize (complementUpperTriangleWord bits)
    ≡ Word.encodingSize bits
complementUpperTrianglePreservesLength [] = refl
complementUpperTrianglePreservesLength (bit ∷ rest) =
  cong suc (complementUpperTrianglePreservesLength rest)

-- The one-pass emitter writes exactly one output bit per input bit.
-- This counts write operations, NOT arbitrary input parsing, numeric
-- threshold conversion, or a Turing machine's complete execution.
emittedComplementBits : Word.BitWord → Nat
emittedComplementBits [] = zero
emittedComplementBits (_ ∷ rest) = suc (emittedComplementBits rest)

emittedComplementBitCountExact :
  (bits : Word.BitWord) →
  emittedComplementBits bits ≡ Word.encodingSize bits
emittedComplementBitCountExact [] = refl
emittedComplementBitCountExact (_ ∷ rest) =
  cong suc (emittedComplementBitCountExact rest)
