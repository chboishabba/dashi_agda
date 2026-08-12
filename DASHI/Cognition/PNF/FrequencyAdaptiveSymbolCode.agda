module DASHI.Cognition.PNF.FrequencyAdaptiveSymbolCode where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Frequency-adaptive physical codes are a storage/index projection only.
--
-- Very common symbols may receive compact low-valued physical codes, while a
-- rare long lexical form may receive a large code.  Canonical SymbolId remains
-- unchanged: re-ranking a codebook must never rewrite semantic identity.
------------------------------------------------------------------------

record FrequencyAdaptiveCodebook : Set where
  constructor frequencyAdaptiveCodebook
  field
    revision : Nat
    encode : SymbolId → Nat
    decode : Nat → SymbolId
    decodeEncode : (symbol : SymbolId) → decode (encode symbol) ≡ symbol
    hotPrefixLimit : Nat

open FrequencyAdaptiveCodebook public

record SymbolFrequencyObservation : Set where
  constructor symbolFrequencyObservation
  field
    observedSymbol : SymbolId
    occurrenceCount : Nat
    assignedPhysicalCode : Nat

open SymbolFrequencyObservation public

record CodebookMeasurement : Set where
  constructor codebookMeasurement
  field
    incumbentEncodedBytes : Nat
    candidateEncodedBytes : Nat
    incumbentLookupWork : Nat
    candidateLookupWork : Nat
    sampleSymbolCount : Nat

open CodebookMeasurement public

data FrequencyCodeSemanticAuthority : Set where

frequencyRankCannotChangeSemanticIdentity : FrequencyCodeSemanticAuthority → ⊥
frequencyRankCannotChangeSemanticIdentity ()

record FrequencyCodeBoundary : Set where
  constructor frequencyCodeBoundary
  field
    commonSymbolsMayUseCompactCodes : Bool
    commonSymbolsMayUseCompactCodesIsTrue :
      commonSymbolsMayUseCompactCodes ≡ true
    canonicalSymbolIdEqualsPhysicalFrequencyCode : Bool
    canonicalSymbolIdEqualsPhysicalFrequencyCodeIsFalse :
      canonicalSymbolIdEqualsPhysicalFrequencyCode ≡ false
    codebookMayBeRebuiltFromCorpusStatistics : Bool
    codebookMayBeRebuiltFromCorpusStatisticsIsTrue :
      codebookMayBeRebuiltFromCorpusStatistics ≡ true
    physicalCodeOptimalityRequiresMeasurement : Bool
    physicalCodeOptimalityRequiresMeasurementIsTrue :
      physicalCodeOptimalityRequiresMeasurement ≡ true

open FrequencyCodeBoundary public

canonicalFrequencyCodeBoundary : FrequencyCodeBoundary
canonicalFrequencyCodeBoundary =
  frequencyCodeBoundary true refl false refl true refl true refl
