module DASHI.Cognition.PNF.NumericOccurrenceFibre where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy

------------------------------------------------------------------------
-- Post-tokenisation occurrence geometry.
--
-- NumericAuthority and SpacyNumericProjection already supply dense TokenId,
-- SentenceId, SymbolId and lemma observations.  This module does not duplicate
-- token storage.  It packages the existing row as a scoped occurrence and makes
-- the fibre distinction explicit: many occurrence identities may project to
-- one surface/lemma key without being merged.
------------------------------------------------------------------------

record ScopedTokenOccurrence : Set where
  constructor scopedTokenOccurrence
  field
    scope : NumericScope
    row : Spacy.NumericTokenRow

open ScopedTokenOccurrence public

occurrenceToken : ScopedTokenOccurrence → TokenId
occurrenceToken occurrence =
  Spacy.token (Spacy.observation (row occurrence))

occurrenceSentence : ScopedTokenOccurrence → SentenceId
occurrenceSentence occurrence =
  Spacy.sentence (Spacy.observation (row occurrence))

occurrenceOrdinal : ScopedTokenOccurrence → Nat
occurrenceOrdinal occurrence =
  Spacy.localOrdinal (Spacy.observation (row occurrence))

surfaceFibreKey : ScopedTokenOccurrence → SymbolId
surfaceFibreKey occurrence =
  Spacy.orth (Spacy.observation (row occurrence))

lemmaFibreKey : ScopedTokenOccurrence → Spacy.LemmaObservation
lemmaFibreKey occurrence =
  Spacy.lemma (Spacy.observation (row occurrence))

record SurfaceFibreMember : Set where
  constructor surfaceFibreMember
  field
    occurrence : ScopedTokenOccurrence
    surfaceKey : SymbolId
    keyMatchesOccurrence : surfaceKey ≡ surfaceFibreKey occurrence

open SurfaceFibreMember public

------------------------------------------------------------------------
-- Repeated pronouns/words remain distinct occurrences even when they inhabit
-- the same lexical fibre.  Multiplicity is therefore fibre cardinality in the
-- runtime representation, not a larger incidence coefficient.
------------------------------------------------------------------------

record DistinctOccurrencesSameSurface : Set where
  constructor distinctOccurrencesSameSurface
  field
    left right : ScopedTokenOccurrence
    tokensAreDistinct : occurrenceToken left ≡ occurrenceToken right → ⊥
    sameSurface : surfaceFibreKey left ≡ surfaceFibreKey right

open DistinctOccurrencesSameSurface public

data SharedSurfaceIdentityPermission : Set where

sharedSurfaceDoesNotIdentifyOccurrences :
  SharedSurfaceIdentityPermission → ⊥
sharedSurfaceDoesNotIdentifyOccurrences ()

record NumericOccurrenceFibreBoundary : Set where
  constructor numericOccurrenceFibreBoundary
  field
    repeatedSurfaceMergesTokenOccurrences : Bool
    repeatedSurfaceMergesTokenOccurrencesIsFalse :
      repeatedSurfaceMergesTokenOccurrences ≡ false
    multiplicityStoredAsSemanticIncidenceMagnitude : Bool
    multiplicityStoredAsSemanticIncidenceMagnitudeIsFalse :
      multiplicityStoredAsSemanticIncidenceMagnitude ≡ false
    hotCarrierUsesExistingNumericIds : Bool
    hotCarrierUsesExistingNumericIdsIsTrue :
      hotCarrierUsesExistingNumericIds ≡ true

open NumericOccurrenceFibreBoundary public

canonicalNumericOccurrenceFibreBoundary : NumericOccurrenceFibreBoundary
canonicalNumericOccurrenceFibreBoundary =
  numericOccurrenceFibreBoundary
    false refl
    false refl
    true refl
