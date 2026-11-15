{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFiniteNativeBondReindexingSafeExact where

------------------------------------------------------------------------
-- R443-C3 FINITE BOND REINDEXING: REAL ORIGINAL ENUMERATION, NO NEW GEOMETRY.
--
-- A function on the ORIGINAL periodic positive-bond labels induces an
-- explicit action on its canonical Vec representation. We establish
-- pointwise naturality, composition, identity, and inverses by reusing
-- the source-written two-way finite bond codec.
--
-- No full function extensionality, real analysis, Haar, RG or OS inputs.
-- A label bijection is a finite permutation of positions, but the distinct
-- syntactic LinkPermutation (adjacent-swap) witness must still be built
-- separately before invoking productHaarPermutationInvariant.
--
-- Provenance: original Balaban periodic torus; DASHI native bond codec.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec

module _ {Value : Set} (L : Nat) where

  Bond : Set
  Bond = Torus.PositiveBond L

  Vector : Set
  Vector = Vec.Vec Value (Codec.originalPositiveBondCount L)

  reindexBonds : (Bond → Bond) → Vector → Vector
  reindexBonds permutation vector =
    Codec.encodeOriginalBonds L
      (λ bond → Codec.decodeOriginalBonds L vector (permutation bond))

  reindexAt :
    (permutation : Bond → Bond) (vector : Vector) (bond : Bond) →
    Codec.decodeOriginalBonds L
      (reindexBonds permutation vector) bond
    ≡
    Codec.decodeOriginalBonds L vector (permutation bond)
  reindexAt permutation vector bond =
    Codec.originalBondsDecodeEncodeAt L
      (λ label →
        Codec.decodeOriginalBonds L vector (permutation label))
      bond

  reindexIdentity : (vector : Vector) →
    reindexBonds (λ bond → bond) vector ≡ vector
  reindexIdentity vector =
    Codec.originalBondsEncodeDecodeExactly L vector

  reindexCompose :
    (first second : Bond → Bond) (vector : Vector) →
    reindexBonds first (reindexBonds second vector)
    ≡
    reindexBonds (λ bond → second (first bond)) vector
  reindexCompose first second vector =
    Codec.originalBondsEncodePointwise L
      (λ bond →
        Codec.decodeOriginalBonds L
          (reindexBonds second vector) (first bond))
      (λ bond →
        Codec.decodeOriginalBonds L vector (second (first bond)))
      (λ bond → reindexAt second vector (first bond))

  reindexAsIdentity :
    (permutation : Bond → Bond) (vector : Vector) →
    (∀ bond → permutation bond ≡ bond) →
    reindexBonds permutation vector ≡ vector
  reindexAsIdentity permutation vector identityAt =
    trans
      (Codec.originalBondsEncodePointwise L
        (λ bond → Codec.decodeOriginalBonds L vector (permutation bond))
        (Codec.decodeOriginalBonds L vector)
        (λ bond →
          cong (Codec.decodeOriginalBonds L vector) (identityAt bond)))
      (reindexIdentity vector)

  reindexInverseLeft :
    (forward backward : Bond → Bond) (vector : Vector) →
    (∀ bond → backward (forward bond) ≡ bond) →
    reindexBonds forward (reindexBonds backward vector) ≡ vector
  reindexInverseLeft forward backward vector inverseAt =
    trans
      (reindexCompose forward backward vector)
      (reindexAsIdentity
        (λ bond → backward (forward bond)) vector inverseAt)

  reindexInverseRight :
    (forward backward : Bond → Bond) (vector : Vector) →
    (∀ bond → forward (backward bond) ≡ bond) →
    reindexBonds backward (reindexBonds forward vector) ≡ vector
  reindexInverseRight forward backward vector inverseAt =
    trans
      (reindexCompose backward forward vector)
      (reindexAsIdentity
        (λ bond → forward (backward bond)) vector inverseAt)

  reindexOrderThree :
    (permutation : Bond → Bond) (vector : Vector) →
    (∀ bond → permutation (permutation (permutation bond)) ≡ bond) →
    reindexBonds permutation
      (reindexBonds permutation (reindexBonds permutation vector))
    ≡ vector
  reindexOrderThree permutation vector orderThreeAt =
    trans
      (reindexCompose permutation permutation
        (reindexBonds permutation vector))
      (trans
        (reindexCompose
          (λ bond → permutation (permutation bond))
          permutation vector)
        (reindexAsIdentity
          (λ bond → permutation (permutation (permutation bond)))
          vector orderThreeAt))
