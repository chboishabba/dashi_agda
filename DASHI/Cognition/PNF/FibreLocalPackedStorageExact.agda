module DASHI.Cognition.PNF.FibreLocalPackedStorageExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
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

open PackedSentenceFibre public

absoluteStart : Nat → Nat → Nat
absoluteStart base offset = base Address.+? offset
