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
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (sym)
import Data.Nat.Base as Nat

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdStructuralExact as Structural
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdNumericalExact as Numeric
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
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


------------------------------------------------------------------------
-- NUMERICAL REFLECTION of strict binary endpoint inequality.
-- The original compareLE trichotomy already supplies explicit Nat
-- distance witnesses; unlike the executable path, this uses unary
-- Nat booleans ONLY as a proof-side observer.
------------------------------------------------------------------------

natStrictLessGap :
  (x gap : Nat) →
  Nat._≤ᵇ_ (suc x) (suc (x + gap)) ≡ true
natStrictLessGap zero gap = refl
natStrictLessGap (suc x) gap = natStrictLessGap x gap

natStrictSelfFalse :
  (x : Nat) → Nat._≤ᵇ_ (suc x) x ≡ false
natStrictSelfFalse zero = refl
natStrictSelfFalse (suc x) = natStrictSelfFalse x

natStrictReverseFalse :
  (y gap : Nat) →
  Nat._≤ᵇ_ (suc (suc (y + gap))) y ≡ false
natStrictReverseFalse zero gap = refl
natStrictReverseFalse (suc y) gap = natStrictReverseFalse y gap

-- This closes the actual comparison NUMERIC seam for all binary
-- endpoint widths including redundant most-significant zero bits.
nativeStrictLessNumerical :
  (xs ys : Word.BitWord) →
  lessNativeLE xs ys ≡
    Nat._≤ᵇ_ (suc (Value.valueLE xs)) (Value.valueLE ys)
nativeStrictLessNumerical xs ys
  with Compare.compareLE xs ys
     | Numeric.compareLENumericalCorrect xs ys
... | Compare.less | (gap , equal)
  rewrite equal =
  sym (natStrictLessGap (Value.valueLE xs) gap)
... | Compare.equal | equal
  rewrite equal =
  sym (natStrictSelfFalse (Value.valueLE xs))
... | Compare.greater | (gap , equal)
  rewrite equal =
  sym (natStrictReverseFalse (Value.valueLE ys) gap)


------------------------------------------------------------------------
-- B5: actual binary vertex identity agrees with NUMERICAL equality.
-- This is the exact key for reusing original chronological endpoint
-- consistency without constructing unary Nat at executable runtime.
------------------------------------------------------------------------

natEqualReflexive :
  (n : Nat) → Nat._≡ᵇ_ n n ≡ true
natEqualReflexive zero = refl
natEqualReflexive (suc n) = natEqualReflexive n

natGapDifferentLeft :
  (n gap : Nat) →
  Nat._≡ᵇ_ (suc (n + gap)) n ≡ false
natGapDifferentLeft zero gap = refl
natGapDifferentLeft (suc n) gap =
  natGapDifferentLeft n gap

natGapDifferentRight :
  (n gap : Nat) →
  Nat._≡ᵇ_ n (suc (n + gap)) ≡ false
natGapDifferentRight zero gap = refl
natGapDifferentRight (suc n) gap =
  natGapDifferentRight n gap

nativeEqualNumerical :
  (xs ys : Word.BitWord) →
  equalNativeLE xs ys ≡
    Nat._≡ᵇ_ (Value.valueLE xs) (Value.valueLE ys)
nativeEqualNumerical xs ys
  with Compare.compareLE xs ys
     | Numeric.compareLENumericalCorrect xs ys
... | Compare.less | (gap , equality)
  rewrite equality =
  sym (natGapDifferentRight (Value.valueLE xs) gap)
... | Compare.equal | equality
  rewrite equality =
  sym (natEqualReflexive (Value.valueLE xs))
... | Compare.greater | (gap , equality)
  rewrite equality =
  sym (natGapDifferentLeft (Value.valueLE ys) gap)
