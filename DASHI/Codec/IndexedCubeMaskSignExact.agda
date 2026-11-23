module DASHI.Codec.IndexedCubeMaskSignExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.TriadicMaskSignFactorization as M

-- The original codec is applied to each of three triples.
-- Prefix reduction retains the final triple, never erases it.
record Blocks (A : Set) : Set where
  constructor blocks
  field
    firstBlock secondBlock residualBlock : M.Triple A
open Blocks public

mapBlocks : ∀ {A B : Set} → (A → B) → Blocks A → Blocks B
mapBlocks f (blocks a b c) =
  blocks (M.mapTriple f a) (M.mapTriple f b) (M.mapTriple f c)

rotateTriple : ∀ {A : Set} → M.Triple A → M.Triple A
rotateTriple (M.triple a b c) = M.triple b c a

rotate : ∀ {A : Set} → Blocks A → Blocks A
rotate (blocks a b c) =
  blocks (rotateTriple a) (rotateTriple b) (rotateTriple c)

encode : Blocks Trit → Blocks M.FactorizedTrit
encode = mapBlocks M.encodeTrit

decode : Blocks M.FactorizedTrit → Blocks Trit
decode = mapBlocks M.decodeTrit

codecRotation : (x : Blocks Trit) →
  encode (rotate x) ≡ rotate (encode x)
codecRotation (blocks (M.triple a b c) (M.triple d e f)
  (M.triple g h i)) = refl

rotationOrderThree : ∀ {A : Set} (x : Blocks A) →
  rotate (rotate (rotate x)) ≡ x
rotationOrderThree (blocks (M.triple a b c) (M.triple d e f)
  (M.triple g h i)) = refl

roundtrip : (x : Blocks Trit) → decode (encode x) ≡ x
roundtrip (blocks a b c)
  rewrite M.decodeTriple-encodeTriple a
        | M.decodeTriple-encodeTriple b
        | M.decodeTriple-encodeTriple c = refl

record PrefixResidual (A : Set) : Set where
  constructor split
  field
    prefixOne prefixTwo suffix : M.Triple A
open PrefixResidual public

partition : ∀ {A : Set} → Blocks A → PrefixResidual A
partition (blocks a b c) = split a b c

join : ∀ {A : Set} → PrefixResidual A → Blocks A
join (split a b c) = blocks a b c

joinPartition : ∀ {A : Set} (x : Blocks A) → join (partition x) ≡ x
joinPartition (blocks a b c) = refl

partitionJoin : ∀ {A : Set} (x : PrefixResidual A) → partition (join x) ≡ x
partitionJoin (split a b c) = refl

encodeSplit : PrefixResidual Trit → PrefixResidual M.FactorizedTrit
encodeSplit (split a b c) =
  split (M.encodeTriple a) (M.encodeTriple b) (M.encodeTriple c)

rotateSplit : ∀ {A : Set} → PrefixResidual A → PrefixResidual A
rotateSplit (split a b c) =
  split (rotateTriple a) (rotateTriple b) (rotateTriple c)

partitionCodec : (x : Blocks Trit) →
  partition (encode x) ≡ encodeSplit (partition x)
partitionCodec (blocks a b c) = refl

partitionRotation : ∀ {A : Set} (x : Blocks A) →
  partition (rotate x) ≡ rotateSplit (partition x)
partitionRotation (blocks a b c) = refl

splitCodecRotation : (x : PrefixResidual Trit) →
  encodeSplit (rotateSplit x) ≡ rotateSplit (encodeSplit x)
splitCodecRotation (split (M.triple a b c) (M.triple d e f)
  (M.triple g h i)) = refl
