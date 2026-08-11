module DASHI.Cognition.PNF.LexicalRetrievalProjection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy

------------------------------------------------------------------------
-- Three deliberately distinct lexical coordinates.
--
-- 1. exact surface symbol: authoritative occurrence observation;
-- 2. parser lemma: spaCy-produced linguistic observation;
-- 3. retrieval lexemes: application/search projection, e.g. PostgreSQL FTS.
--
-- Retrieval normalization is allowed to be more aggressive because it proposes
-- neighbourhoods.  No equality between parser lemma and retrieval lexeme is
-- required or inferred.
------------------------------------------------------------------------

data RetrievalProducer : Set where
  postgresFullTextProjection : RetrievalProducer
  numericCueAutomatonProjection : RetrievalProducer
  vectorNeighbourhoodProjection : RetrievalProducer

record LexicalRetrievalProjection : Set where
  constructor lexicalRetrievalProjection
  field
    tokenRow : Spacy.NumericTokenRow
    exactSurface : SymbolId
    exactSurfaceMatchesObservation :
      exactSurface ≡ Spacy.orth (Spacy.observation tokenRow)
    parserLemmaObservation : Spacy.LemmaObservation
    parserLemmaMatchesObservation :
      parserLemmaObservation ≡ Spacy.lemma (Spacy.observation tokenRow)
    producer : RetrievalProducer
    retrievalLexemes : List SymbolId

open LexicalRetrievalProjection public

------------------------------------------------------------------------
-- Retrieval optimisation receipt.
--
-- PostgreSQL FTS, a numeric cue automaton, or a vector proposal earns a place
-- in the hot path when it measurably reduces the candidate frontier.  The
-- receipt is deliberately independent of semantic authority.
------------------------------------------------------------------------

record RetrievalReductionReceipt : Set where
  constructor retrievalReductionReceipt
  field
    reductionProducer : RetrievalProducer
    inputCandidateCount : Nat
    outputCandidateCount : Nat
    outputDoesNotExceedInput :
      outputCandidateCount ≤ᶜ inputCandidateCount

open RetrievalReductionReceipt public

------------------------------------------------------------------------
-- Numeric cue language.
--
-- Multi-token cues such as a governed alias phrase are finite words over
-- SymbolId after tokenisation.  Semantic authority does not require a regex or
-- text-pattern engine in the hot path.  A caller may compile these words to a
-- trie/DFA/Aho-Corasick-style machine, but this module only requires exact
-- numeric-word evidence and therefore does not privilege an implementation.
------------------------------------------------------------------------

record NumericCueWord : Set where
  constructor numericCueWord
  field
    cueSymbols : List SymbolId

open NumericCueWord public

record NumericCueMatch : Set where
  constructor numericCueMatch
  field
    cue : NumericCueWord
    observedSymbols : List SymbolId
    exactCueMatch : observedSymbols ≡ cueSymbols cue

open NumericCueMatch public

------------------------------------------------------------------------
-- Retrieval/cue matches generate candidates only.  They cannot by themselves
-- establish local identity, world identity, or a parser lemma.
------------------------------------------------------------------------

data RetrievalIdentityPromotionPermission : RetrievalProducer → Set where

postgresRetrievalCannotPromoteIdentity :
  RetrievalIdentityPromotionPermission postgresFullTextProjection → ⊥
postgresRetrievalCannotPromoteIdentity ()

numericCueRetrievalCannotPromoteIdentity :
  RetrievalIdentityPromotionPermission numericCueAutomatonProjection → ⊥
numericCueRetrievalCannotPromoteIdentity ()

vectorRetrievalCannotPromoteIdentity :
  RetrievalIdentityPromotionPermission vectorNeighbourhoodProjection → ⊥
vectorRetrievalCannotPromoteIdentity ()

data RegexSemanticAuthority : Set where

regexHasNoSemanticAuthority : RegexSemanticAuthority → ⊥
regexHasNoSemanticAuthority ()

record LexicalRetrievalBoundary : Set where
  constructor lexicalRetrievalBoundary
  field
    parserLemmaEqualsRetrievalStemByDefinition : Bool
    parserLemmaEqualsRetrievalStemByDefinitionIsFalse :
      parserLemmaEqualsRetrievalStemByDefinition ≡ false
    fullTextProjectionIsCanonicalOccurrenceGeometry : Bool
    fullTextProjectionIsCanonicalOccurrenceGeometryIsFalse :
      fullTextProjectionIsCanonicalOccurrenceGeometry ≡ false
    regexMayDirectlyPromoteSemantics : Bool
    regexMayDirectlyPromoteSemanticsIsFalse :
      regexMayDirectlyPromoteSemantics ≡ false
    numericPostTokenisationCueCarrierAvailable : Bool
    numericPostTokenisationCueCarrierAvailableIsTrue :
      numericPostTokenisationCueCarrierAvailable ≡ true

open LexicalRetrievalBoundary public

canonicalLexicalRetrievalBoundary : LexicalRetrievalBoundary
canonicalLexicalRetrievalBoundary =
  lexicalRetrievalBoundary
    false refl
    false refl
    false refl
    true refl
