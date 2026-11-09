{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact where

------------------------------------------------------------------------
-- P0-B/F: ACTUAL binary endpoint-order validator for original N21.
--
-- This is a bit-only runtime over native gamma-decoded LE endpoints.
-- The original structural graph conditions are 0 <= u < v < n,
-- strictly increasing lexicographic (u,v) across edges, and exact
-- canonical edge order. No unary Nat or Fin is constructed here.
-- The comparator is the ACTUAL Karp21BinaryNativeThresholdExact.
--
-- STILL OPEN: numeric reflection to original validRawEdges on every
-- word, source gamma n/m bit-header/count scanner, certificate-history
-- bit equality and full TM tape/alloc/head-motion polynomial clock.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdStructuralExact as Structural
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge

-- Compare encoded natural addresses WITHOUT interpreting them as Nat.
lessNativeLE : Word.BitWord → Word.BitWord → Bool
lessNativeLE xs ys with Compare.compareLE xs ys
... | Compare.less = true
... | Compare.equal = false
... | Compare.greater = false

equalNativeLE : Word.BitWord → Word.BitWord → Bool
equalNativeLE xs ys with Compare.compareLE xs ys
... | Compare.less = false
... | Compare.equal = true
... | Compare.greater = false

greaterNativeLE : Word.BitWord → Word.BitWord → Bool
greaterNativeLE xs ys with Compare.compareLE xs ys
... | Compare.less = false
... | Compare.equal = false
... | Compare.greater = true

data BinaryPreviousPair : Set where
  noPrevious : BinaryPreviousPair
  previous : Word.BitWord → Word.BitWord → BinaryPreviousPair

-- Literal original (u,v) > previous in lexicographic order.
strictAfterBinary :
  BinaryPreviousPair → Word.BitWord → Word.BitWord → Bool
strictAfterBinary noPrevious u v = true
strictAfterBinary (previous a b) u v
  with Compare.compareLE a u
... | Compare.less = true
... | Compare.greater = false
... | Compare.equal = lessNativeLE b v

-- Source original strict graph validation, now with ONLY bit-level
-- endpoint comparisons and bounded-length native binary registers.
validNativeBinaryEdges :
  Word.BitWord →
  BinaryPreviousPair →
  List Edge.BinaryRawEdge →
  Bool
validNativeBinaryEdges n prev [] = true
validNativeBinaryEdges n prev (Edge.binary-edge u v w ∷ rest)
  with lessNativeLE u v
     | lessNativeLE v n
     | strictAfterBinary prev u v
... | true | true | true =
  validNativeBinaryEdges n (previous u v) rest
... | _ | _ | _ = false

-- Reflexive comparator facts guarantee a vertex cannot be its own
-- strictly ordered edge endpoint, with arbitrary high zero padding.
strictSelfEdgeRejected :
  (vertex : Word.BitWord) →
  lessNativeLE vertex vertex ≡ false
strictSelfEdgeRejected vertex
  rewrite Structural.compareLEReflexive vertex = refl
