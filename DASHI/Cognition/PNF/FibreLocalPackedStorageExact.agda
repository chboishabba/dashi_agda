module DASHI.Cognition.PNF.FibreLocalPackedStorageExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_)
import DASHI.Cognition.PNF.FibreLocalTokenAddressExact as Address

------------------------------------------------------------------------
-- Compression-friendly local coordinate carrier.
--
-- This is a semantic/storage boundary, not a claim about PostgreSQL heap
-- compression.  The representation exposes concentrated local coordinates:
-- sentence-relative starts, token lengths, local head displacements/addresses,
-- compact annotation codes, and bounded branch ordinals.  Any byte-saving claim
-- still requires a concrete lossless codec and a measurement receipt.
------------------------------------------------------------------------

data HeadDisplacement : Set where
  self : HeadDisplacement
  backward : Nat → HeadDisplacement
  forward : Nat → HeadDisplacement

record PackedTokenColumns : Set where
  constructor packedTokenColumns
  field
    startOffsets : List Nat
    lengths : List Nat
    headDisplacements : List HeadDisplacement
    orthCodes lemmaCodes posCodes tagCodes dependencyCodes morphCodes : List Nat
    lemmaOriginCodes posOriginCodes tagOriginCodes dependencyOriginCodes : List Nat

open PackedTokenColumns public

record PackedSentenceFibre : Set where
  constructor packedSentenceFibre
  field
    semanticFibreIdentity : Nat
    authorityFibreIdentity : Nat
    sentenceOrdinal : Nat
    baseChar : Nat
    columns : PackedTokenColumns
    solverPaths : List Address.BranchPathAddress

open PackedSentenceFibre public

absoluteStart : Nat → Nat → Nat
absoluteStart base offset = base + offset

absoluteEnd : Nat → Nat → Nat → Nat
absoluteEnd base offset length = (base + offset) + length

------------------------------------------------------------------------
-- Any physical codec must be lossless before it can replace the unpacked tape.
------------------------------------------------------------------------

record LosslessPackedFibreCodec (Encoded : Set) : Set₁ where
  constructor losslessPackedFibreCodec
  field
    encode : PackedSentenceFibre → Encoded
    decode : Encoded → PackedSentenceFibre
    decodeEncode :
      (fibre : PackedSentenceFibre) →
      decode (encode fibre) ≡ fibre

open LosslessPackedFibreCodec public

------------------------------------------------------------------------
-- Physical measurements distinguish normalized relational payload, packed hot
-- payload, and optionally compressed cold payload.  Repeated small codes are a
-- candidate statistical advantage, not themselves a byte-saving theorem.
------------------------------------------------------------------------

record FibreStorageMeasurement : Set where
  constructor fibreStorageMeasurement
  field
    tokenCount : Nat
    normalizedPayloadBytes : Nat
    packedPayloadBytes : Nat
    compressedPayloadBytes : Nat
    randomAccessWork : Nat
    decodeWork : Nat

open FibreStorageMeasurement public

record PackedPayloadNoLarger
    (measurement : FibreStorageMeasurement) : Set where
  constructor packedPayloadNoLarger
  field
    packedNoLarger :
      packedPayloadBytes measurement
        ≤ᶜ normalizedPayloadBytes measurement

open PackedPayloadNoLarger public

record CompressedPayloadNoLarger
    (measurement : FibreStorageMeasurement) : Set where
  constructor compressedPayloadNoLarger
  field
    compressedNoLarger :
      compressedPayloadBytes measurement
        ≤ᶜ normalizedPayloadBytes measurement

open CompressedPayloadNoLarger public

record RepeatedLocalCodeObservation : Set where
  constructor repeatedLocalCodeObservation
  field
    localCode : Nat
    occurrenceCount : Nat

open RepeatedLocalCodeObservation public

data RepeatedLocalCodesAutomaticallyCompressPostgresHeap : Set where

data SmallNumericMagnitudeAutomaticallyChoosesOptimalCodec : Set where

data FibrePackingAutomaticallyWinsRandomAccess : Set where

repetitionNeedsPhysicalCodecEvidence :
  RepeatedLocalCodesAutomaticallyCompressPostgresHeap → ⊥
repetitionNeedsPhysicalCodecEvidence ()

numericMagnitudeNeedsPhysicalMeasurement :
  SmallNumericMagnitudeAutomaticallyChoosesOptimalCodec → ⊥
numericMagnitudeNeedsPhysicalMeasurement ()

packingMustAlsoEarnRandomAccess :
  FibrePackingAutomaticallyWinsRandomAccess → ⊥
packingMustAlsoEarnRandomAccess ()
