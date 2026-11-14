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

-- Source-coordinate AST: binary joins/order preserve an explicit
-- compound order policy. Biopython CompoundLocation._flip (v1.86) reverses
-- parts only if ALL the child part strands are absent/None. Otherwise it
-- preserves the original biological part order (even with mixed strands).
-- This policy is an input classification; the parser adapter must
-- provide the witness that it correctly classified child strands.
data CompoundOrderPolicy : Set where
  allPartsWithoutStrand : CompoundOrderPolicy
  atLeastOneStrandedPart : CompoundOrderPolicy

data FeatureLocation (n : Nat) : Set where
  interval : BoundedSpan n → FeatureLocation n
  join : CompoundOrderPolicy →
         FeatureLocation n → FeatureLocation n → FeatureLocation n
  order : CompoundOrderPolicy →
          FeatureLocation n → FeatureLocation n → FeatureLocation n
  complement : FeatureLocation n → FeatureLocation n

reverseFeature : {n : Nat} → FeatureLocation n → FeatureLocation n
reverseFeature (interval span) = interval (mirrorSpan span)
reverseFeature (join allPartsWithoutStrand a b) =
  join allPartsWithoutStrand (reverseFeature b) (reverseFeature a)
reverseFeature (join atLeastOneStrandedPart a b) =
  join atLeastOneStrandedPart (reverseFeature a) (reverseFeature b)
reverseFeature (order allPartsWithoutStrand a b) =
  order allPartsWithoutStrand (reverseFeature b) (reverseFeature a)
reverseFeature (order atLeastOneStrandedPart a b) =
  order atLeastOneStrandedPart (reverseFeature a) (reverseFeature b)
reverseFeature (complement a) = complement (reverseFeature a)

-- This erases only the covers equality proof, not coordinates, strand,
-- compound order, or the explicit order policy.
data Geometry : Set where
  intervalG : Nat → Nat → Nat → GB.Strand → Geometry
  joinG : CompoundOrderPolicy → Geometry → Geometry → Geometry
  orderG : CompoundOrderPolicy → Geometry → Geometry → Geometry
  complementG : Geometry → Geometry

geometry : {n : Nat} → FeatureLocation n → Geometry
geometry (interval span) =
  intervalG (left span) (width span) (right span) (strand span)
geometry (join policy a b) = joinG policy (geometry a) (geometry b)
geometry (order policy a b) = orderG policy (geometry a) (geometry b)
geometry (complement a) = complementG (geometry a)

mirrorGeometry : Geometry → Geometry
mirrorGeometry (intervalG l w r direction) =
  intervalG r w l (GB.reverseStrandOf direction)
mirrorGeometry (joinG allPartsWithoutStrand a b) =
  joinG allPartsWithoutStrand (mirrorGeometry b) (mirrorGeometry a)
mirrorGeometry (joinG atLeastOneStrandedPart a b) =
  joinG atLeastOneStrandedPart (mirrorGeometry a) (mirrorGeometry b)
mirrorGeometry (orderG allPartsWithoutStrand a b) =
  orderG allPartsWithoutStrand (mirrorGeometry b) (mirrorGeometry a)
mirrorGeometry (orderG atLeastOneStrandedPart a b) =
  orderG atLeastOneStrandedPart (mirrorGeometry a) (mirrorGeometry b)
mirrorGeometry (complementG a) = complementG (mirrorGeometry a)

geometryOfReverse : {n : Nat} (location : FeatureLocation n) →
  geometry (reverseFeature location) ≡ mirrorGeometry (geometry location)
geometryOfReverse (interval (boundedSpan l w r within direction)) = refl
geometryOfReverse (join allPartsWithoutStrand a b)
  rewrite geometryOfReverse a | geometryOfReverse b = refl
geometryOfReverse (join atLeastOneStrandedPart a b)
  rewrite geometryOfReverse a | geometryOfReverse b = refl
geometryOfReverse (order allPartsWithoutStrand a b)
  rewrite geometryOfReverse a | geometryOfReverse b = refl
geometryOfReverse (order atLeastOneStrandedPart a b)
  rewrite geometryOfReverse a | geometryOfReverse b = refl
geometryOfReverse (complement a)
  rewrite geometryOfReverse a = refl

mirrorGeometryTwice : (g : Geometry) →
  mirrorGeometry (mirrorGeometry g) ≡ g
mirrorGeometryTwice (intervalG l w r direction)
  rewrite GB.reverseStrandInvolutive direction = refl
mirrorGeometryTwice (joinG allPartsWithoutStrand a b)
  rewrite mirrorGeometryTwice a | mirrorGeometryTwice b = refl
mirrorGeometryTwice (joinG atLeastOneStrandedPart a b)
  rewrite mirrorGeometryTwice a | mirrorGeometryTwice b = refl
mirrorGeometryTwice (orderG allPartsWithoutStrand a b)
  rewrite mirrorGeometryTwice a | mirrorGeometryTwice b = refl
mirrorGeometryTwice (orderG atLeastOneStrandedPart a b)
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
