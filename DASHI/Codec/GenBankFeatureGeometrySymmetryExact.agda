{-# OPTIONS --safe #-}
module DASHI.Codec.GenBankFeatureGeometrySymmetryExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Codec.GenBankLocationFiniteCore as GB

-- Pure geometric model of an EXACT location, with an explicit source
-- length n. We do not identify this model with a parser for arbitrary
-- raw GenBank text, nor with molecular function.
--
-- The invariant (left + width) + right = n means that mirroring an interval
-- merely swaps its prefix and suffix. This avoids a partially defined
-- natural subtraction and keeps the reversed interval within bounds.

cong : {A B : Set} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} →
        x ≡ y → y ≡ z → x ≡ z
trans refl q = q

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

+-zero-right : (a : Nat) → a + zero ≡ a
+-zero-right zero = refl
+-zero-right (suc a) rewrite +-zero-right a = refl

+-suc-right : (a b : Nat) → a + suc b ≡ suc (a + b)
+-suc-right zero b = refl
+-suc-right (suc a) b rewrite +-suc-right a b = refl

+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero b rewrite +-zero-right b = refl
+-comm (suc a) b rewrite +-comm a b | +-suc-right b a = refl

swapEnds : (left width right : Nat) →
  (right + width) + left ≡ (left + width) + right
swapEnds left width right =
  trans (+-assoc right width left)
    (trans
      (cong (λ t → right + t) (+-comm width left))
      (+-comm right (left + width)))

record BoundedSpan (n : Nat) : Set where
  constructor boundedSpan
  field
    left : Nat
    width : Nat
    right : Nat
    covers : (left + width) + right ≡ n
    strand : GB.Strand
open BoundedSpan public

mirrorSpan : {n : Nat} → BoundedSpan n → BoundedSpan n
mirrorSpan (boundedSpan l w r within direction) =
  boundedSpan r w l
    (trans (swapEnds l w r) within)
    (GB.reverseStrandOf direction)

-- Original 1-based inclusive start and end, derived from a validated
-- source interval; internal coordinates remain 0-based half-open.
sourceStart1 : {n : Nat} → BoundedSpan n → Nat
sourceStart1 span = suc (left span)

sourceEnd1 : {n : Nat} → BoundedSpan n → Nat
sourceEnd1 span = left span + width span

internalStart0 : {n : Nat} → BoundedSpan n → Nat
internalStart0 = left

internalEnd0 : {n : Nat} → BoundedSpan n → Nat
internalEnd0 span = left span + width span

endConvention : {n : Nat} (span : BoundedSpan n) →
  sourceEnd1 span ≡ internalEnd0 span
endConvention span = refl

mirrorStartTwice : {n : Nat} (span : BoundedSpan n) →
  internalStart0 (mirrorSpan (mirrorSpan span)) ≡ internalStart0 span
mirrorStartTwice (boundedSpan l w r within direction) = refl

mirrorWidthTwice : {n : Nat} (span : BoundedSpan n) →
  width (mirrorSpan (mirrorSpan span)) ≡ width span
mirrorWidthTwice (boundedSpan l w r within direction) = refl

mirrorStrandTwice : {n : Nat} (span : BoundedSpan n) →
  strand (mirrorSpan (mirrorSpan span)) ≡ strand span
mirrorStrandTwice (boundedSpan l w r within direction) =
  GB.reverseStrandInvolutive direction

-- Source-coordinate AST: binary join/order are the structural presentation
-- of finite compound locations; parser adapters must prove their flattening
-- and original part-order correspondence. Reverse complement reverses
-- compound part order, as for GenBank source-coordinate reorientation.
data FeatureLocation (n : Nat) : Set where
  interval : BoundedSpan n → FeatureLocation n
  join : FeatureLocation n → FeatureLocation n → FeatureLocation n
  order : FeatureLocation n → FeatureLocation n → FeatureLocation n
  complement : FeatureLocation n → FeatureLocation n

reverseFeature : {n : Nat} → FeatureLocation n → FeatureLocation n
reverseFeature (interval span) = interval (mirrorSpan span)
reverseFeature (join a b) = join (reverseFeature b) (reverseFeature a)
reverseFeature (order a b) = order (reverseFeature b) (reverseFeature a)
reverseFeature (complement a) = complement (reverseFeature a)

-- Erases only the covers proof, not coordinates, strand, compound order or
-- location constructor. This is an observable semantic AST, NOT raw text.
data Geometry : Set where
  intervalG : Nat → Nat → Nat → GB.Strand → Geometry
  joinG : Geometry → Geometry → Geometry
  orderG : Geometry → Geometry → Geometry
  complementG : Geometry → Geometry

geometry : {n : Nat} → FeatureLocation n → Geometry
geometry (interval span) =
  intervalG (left span) (width span) (right span) (strand span)
geometry (join a b) = joinG (geometry a) (geometry b)
geometry (order a b) = orderG (geometry a) (geometry b)
geometry (complement a) = complementG (geometry a)

mirrorGeometry : Geometry → Geometry
mirrorGeometry (intervalG l w r direction) =
  intervalG r w l (GB.reverseStrandOf direction)
mirrorGeometry (joinG a b) =
  joinG (mirrorGeometry b) (mirrorGeometry a)
mirrorGeometry (orderG a b) =
  orderG (mirrorGeometry b) (mirrorGeometry a)
mirrorGeometry (complementG a) =
  complementG (mirrorGeometry a)

geometryOfReverse : {n : Nat} (location : FeatureLocation n) →
  geometry (reverseFeature location) ≡ mirrorGeometry (geometry location)
geometryOfReverse (interval (boundedSpan l w r within direction)) = refl
geometryOfReverse (join a b)
  rewrite geometryOfReverse a | geometryOfReverse b = refl
geometryOfReverse (order a b)
  rewrite geometryOfReverse a | geometryOfReverse b = refl
geometryOfReverse (complement a)
  rewrite geometryOfReverse a = refl

mirrorGeometryTwice : (g : Geometry) →
  mirrorGeometry (mirrorGeometry g) ≡ g
mirrorGeometryTwice (intervalG l w r direction)
  rewrite GB.reverseStrandInvolutive direction = refl
mirrorGeometryTwice (joinG a b)
  rewrite mirrorGeometryTwice a | mirrorGeometryTwice b = refl
mirrorGeometryTwice (orderG a b)
  rewrite mirrorGeometryTwice a | mirrorGeometryTwice b = refl
mirrorGeometryTwice (complementG a)
  rewrite mirrorGeometryTwice a = refl

reverseFeatureTwiceObservable : {n : Nat} (location : FeatureLocation n) →
  geometry (reverseFeature (reverseFeature location)) ≡ geometry location
reverseFeatureTwiceObservable location =
  trans
    (geometryOfReverse (reverseFeature location))
    (trans
      (cong mirrorGeometry (geometryOfReverse location))
      (mirrorGeometryTwice (geometry location)))

-- A genuinely source-coordinate-shaped carrier, separate from the
-- canonical bounded AST. Normalization must preserve its prefix/extent/
-- suffix witnesses; it cannot silently discard reverse strand.
record SourceInterval (n : Nat) : Set where
  constructor sourceInterval
  field
    start0 : Nat
    extent : Nat
    trailing : Nat
    bounds : (start0 + extent) + trailing ≡ n
    direction : GB.Strand
open SourceInterval public

normalize : {n : Nat} → SourceInterval n → BoundedSpan n
normalize (sourceInterval l w r within direction) =
  boundedSpan l w r within direction

mirrorSource : {n : Nat} → SourceInterval n → SourceInterval n
mirrorSource (sourceInterval l w r within direction) =
  sourceInterval r w l (trans (swapEnds l w r) within)
    (GB.reverseStrandOf direction)

spanGeometry : {n : Nat} → BoundedSpan n → Geometry
spanGeometry span =
  intervalG (left span) (width span) (right span) (strand span)

-- The bounded exact interval *normalization* commutes with source RC.
-- It is not a theorem about Biopython syntax, arbitrary fuzzy GenBank
-- positions, or the whole source-file byte representation.
normalizeMirrorCommutes : {n : Nat} (s : SourceInterval n) →
  spanGeometry (normalize (mirrorSource s)) ≡
  mirrorGeometry (spanGeometry (normalize s))
normalizeMirrorCommutes (sourceInterval l w r within direction) = refl
