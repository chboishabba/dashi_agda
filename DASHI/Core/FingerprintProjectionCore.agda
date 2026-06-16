module DASHI.Core.FingerprintProjectionCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.FormalLensVocabularyCore as Vocabulary

------------------------------------------------------------------------
-- Generic fingerprint projection core.
--
-- This module keeps the projection story explicit:
-- object -> canonical bytes -> digest.
-- The fiber, collision, preimage, and second-preimage records are candidate
-- surfaces only.  They describe the shape of the projection, but they do not
-- claim any cryptographic proof or object-equality authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

parity : Nat → Nat
parity zero =
  zero
parity (suc zero) =
  suc zero
parity (suc (suc n)) =
  parity n

replicateZeros : Nat → List Nat
replicateZeros zero =
  []
replicateZeros (suc n) =
  zero ∷ replicateZeros n

record FingerprintProjectionCore : Set₁ where
  constructor mkFingerprintProjectionCore
  field
    coreLabel :
      String

    coreOwner :
      String

    coreSurfaceName :
      String

    objectType :
      Set

    canonicalBytesType :
      Set

    digestType :
      Set

    objectToCanonicalBytes :
      objectType →
      canonicalBytesType

    canonicalBytesToDigest :
      canonicalBytesType →
      digestType

    objectToDigest :
      objectType →
      digestType

    objectToDigestIsCanonicalComposition :
      ∀ object →
      objectToDigest object ≡
      canonicalBytesToDigest (objectToCanonicalBytes object)

open FingerprintProjectionCore public

------------------------------------------------------------------------
-- Vocabulary layer.

canonicalFingerprintProjectionVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalFingerprintProjectionVocabularyKinds =
  Vocabulary.Cryptographic
  ∷ Vocabulary.Information
  ∷ Vocabulary.Entropy
  ∷ Vocabulary.Commitment
  ∷ Vocabulary.Governance
  ∷ Vocabulary.SymbolicRational
  ∷ []

canonicalFingerprintProjectionVocabularyKindCount : Nat
canonicalFingerprintProjectionVocabularyKindCount =
  listCount canonicalFingerprintProjectionVocabularyKinds

record FingerprintProjectionVocabularyReceipt : Set where
  constructor mkFingerprintProjectionVocabularyReceipt
  field
    vocabularyKinds :
      List Vocabulary.FormalLensKind

    vocabularyKindsAreCanonical :
      vocabularyKinds ≡ canonicalFingerprintProjectionVocabularyKinds

    vocabularyKindCount :
      Nat

    vocabularyKindCountIsCanonical :
      vocabularyKindCount ≡ canonicalFingerprintProjectionVocabularyKindCount

    vocabularyCandidateOnly :
      Bool

    vocabularyCandidateOnlyIsTrue :
      vocabularyCandidateOnly ≡ true

    vocabularyPromoted :
      Bool

    vocabularyPromotedIsFalse :
      vocabularyPromoted ≡ false

open FingerprintProjectionVocabularyReceipt public

canonicalFingerprintProjectionVocabularyReceipt :
  FingerprintProjectionVocabularyReceipt
canonicalFingerprintProjectionVocabularyReceipt =
  mkFingerprintProjectionVocabularyReceipt
    canonicalFingerprintProjectionVocabularyKinds
    refl
    canonicalFingerprintProjectionVocabularyKindCount
    refl
    true
    refl
    false
    refl

fingerprintProjectionVocabularyKinds :
  FingerprintProjectionCore →
  List Vocabulary.FormalLensKind
fingerprintProjectionVocabularyKinds _ =
  canonicalFingerprintProjectionVocabularyKinds

fingerprintProjectionVocabularyKindCount :
  FingerprintProjectionCore →
  Nat
fingerprintProjectionVocabularyKindCount _ =
  canonicalFingerprintProjectionVocabularyKindCount

record Fiber (core : FingerprintProjectionCore) : Set where
  constructor mkFiber
  field
    fiberObject :
      objectType core

    fiberCanonicalBytes :
      canonicalBytesType core

    fiberDigest :
      digestType core

    fiberObjectToCanonicalBytesIsCanonical :
      objectToCanonicalBytes core fiberObject ≡ fiberCanonicalBytes

    fiberCanonicalBytesToDigestIsFiberDigest :
      canonicalBytesToDigest core fiberCanonicalBytes ≡ fiberDigest

    fiberObjectToDigestIsFiberDigest :
      objectToDigest core fiberObject ≡ fiberDigest

open Fiber public

record CollisionCollapseIdentityAuthorityBoundary : Set where
  constructor mkCollisionCollapseIdentityAuthorityBoundary
  field
    digestEqualityCandidateOnly :
      Bool

    digestEqualityCandidateOnlyIsTrue :
      digestEqualityCandidateOnly ≡ true

    collisionCollapsesIdentityAuthorityBoundary :
      Bool

    collisionCollapsesIdentityAuthorityBoundaryIsFalse :
      collisionCollapsesIdentityAuthorityBoundary ≡ false

open CollisionCollapseIdentityAuthorityBoundary public

record CollisionReceipt (core : FingerprintProjectionCore) : Set where
  constructor mkCollisionReceipt
  field
    collisionLabel :
      String

    leftFiber :
      Fiber core

    rightFiber :
      Fiber core

    collisionDigestEquality :
      fiberDigest leftFiber ≡ fiberDigest rightFiber

    collisionBoundary :
      CollisionCollapseIdentityAuthorityBoundary

    collisionCandidateOnly :
      Bool

    collisionCandidateOnlyIsTrue :
      collisionCandidateOnly ≡ true

open CollisionReceipt public

record PreimageReceipt (core : FingerprintProjectionCore) : Set where
  constructor mkPreimageReceipt
  field
    preimageLabel :
      String

    preimageFiber :
      Fiber core

    preimageBoundary :
      CollisionCollapseIdentityAuthorityBoundary

    preimageCandidateOnly :
      Bool

    preimageCandidateOnlyIsTrue :
      preimageCandidateOnly ≡ true

    preimageAuthorityPromotion :
      Bool

    preimageAuthorityPromotionIsFalse :
      preimageAuthorityPromotion ≡ false

open PreimageReceipt public

record SecondPreimageReceipt (core : FingerprintProjectionCore) : Set where
  constructor mkSecondPreimageReceipt
  field
    secondPreimageLabel :
      String

    originalFiber :
      Fiber core

    challengerFiber :
      Fiber core

    sameDigest :
      fiberDigest originalFiber ≡ fiberDigest challengerFiber

    secondPreimageBoundary :
      CollisionCollapseIdentityAuthorityBoundary

    secondPreimageCandidateOnly :
      Bool

    secondPreimageCandidateOnlyIsTrue :
      secondPreimageCandidateOnly ≡ true

    secondPreimageAuthorityPromotion :
      Bool

    secondPreimageAuthorityPromotionIsFalse :
      secondPreimageAuthorityPromotion ≡ false

open SecondPreimageReceipt public

canonicalCollisionCollapseIdentityAuthorityBoundary :
  CollisionCollapseIdentityAuthorityBoundary
canonicalCollisionCollapseIdentityAuthorityBoundary =
  mkCollisionCollapseIdentityAuthorityBoundary
    true
    refl
    false
    refl

canonicalNatFingerprintProjectionCore :
  FingerprintProjectionCore
canonicalNatFingerprintProjectionCore =
  mkFingerprintProjectionCore
    "fingerprint projection core"
    "DASHI.Core.FingerprintProjectionCore"
    "canonicalNatFingerprintProjectionCore"
    Nat
    (List Nat)
    Nat
    replicateZeros
    (λ bytes → parity (listCount bytes))
    (λ object → parity (listCount (replicateZeros object)))
    (λ _ → refl)

canonicalFingerprintProjectionVocabularyKindsForCore :
  List Vocabulary.FormalLensKind
canonicalFingerprintProjectionVocabularyKindsForCore =
  fingerprintProjectionVocabularyKinds canonicalNatFingerprintProjectionCore

canonicalFingerprintProjectionVocabularyKindCountForCore :
  Nat
canonicalFingerprintProjectionVocabularyKindCountForCore =
  fingerprintProjectionVocabularyKindCount canonicalNatFingerprintProjectionCore

canonicalFingerprintFiberOne :
  Fiber canonicalNatFingerprintProjectionCore
canonicalFingerprintFiberOne =
  mkFiber
    1
    (replicateZeros 1)
    (suc zero)
    refl
    refl
    refl

canonicalFingerprintFiberThree :
  Fiber canonicalNatFingerprintProjectionCore
canonicalFingerprintFiberThree =
  mkFiber
    3
    (replicateZeros 3)
    (suc zero)
    refl
    refl
    refl

canonicalFingerprintFiberTwo :
  Fiber canonicalNatFingerprintProjectionCore
canonicalFingerprintFiberTwo =
  mkFiber
    2
    (replicateZeros 2)
    zero
    refl
    refl
    refl

canonicalFingerprintFiberFour :
  Fiber canonicalNatFingerprintProjectionCore
canonicalFingerprintFiberFour =
  mkFiber
    4
    (replicateZeros 4)
    zero
    refl
    refl
    refl

canonicalFingerprintCollisionReceipt :
  CollisionReceipt canonicalNatFingerprintProjectionCore
canonicalFingerprintCollisionReceipt =
  mkCollisionReceipt
    "fingerprint collision candidate"
    canonicalFingerprintFiberOne
    canonicalFingerprintFiberThree
    refl
    canonicalCollisionCollapseIdentityAuthorityBoundary
    true
    refl

canonicalFingerprintPreimageReceipt :
  PreimageReceipt canonicalNatFingerprintProjectionCore
canonicalFingerprintPreimageReceipt =
  mkPreimageReceipt
    "fingerprint preimage candidate"
    canonicalFingerprintFiberTwo
    canonicalCollisionCollapseIdentityAuthorityBoundary
    true
    refl
    false
    refl

canonicalFingerprintSecondPreimageReceipt :
  SecondPreimageReceipt canonicalNatFingerprintProjectionCore
canonicalFingerprintSecondPreimageReceipt =
  mkSecondPreimageReceipt
    "fingerprint second-preimage candidate"
    canonicalFingerprintFiberTwo
    canonicalFingerprintFiberFour
    refl
    canonicalCollisionCollapseIdentityAuthorityBoundary
    true
    refl
    false
    refl
