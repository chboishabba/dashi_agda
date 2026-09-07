module DASHI.Law.SensibLawProofSearchExpansionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawCorpusProducerRoutingExact as Corpus

------------------------------------------------------------------------
-- QUERY EXPANSION != PROOF EXPANSION
------------------------------------------------------------------------

data ExpansionKind : Set where
  terminologyExpansion
  authorityIdentityExpansion
  citationNeighbourhoodExpansion
  doctrinalSynonymExpansion
  lexicalRealisationExpansion
  proofCandidateExpansion
  : ExpansionKind

record QueryExpansion : Set₁ where
  constructor queryExpansion
  field
    intent : Intent.SearchIntent
    kind : ExpansionKind
    seedConceptReference : String
    expandedTerms : List String
    expandedAuthorityReferences : List String
    sourceCorpora : List Corpus.CorpusClass
    resultingQueries : List Query.QueryExpr
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    expansionReference : String

open QueryExpansion public

data ProofExpansionStatus : Set where
  proofExpansionUnresolved
  proofExpansionCandidate
  proofExpansionAdmitted
  proofExpansionRejected
  : ProofExpansionStatus

record ProofExpansion : Set₁ where
  constructor proofExpansion
  field
    sourceQueryExpansionReference : String
    targetProofGapReference : String
    candidatePropositionReferences : List String
    authorityFitnessReference : String
    correspondenceReference : String
    status : ProofExpansionStatus
    expansionReference : String

open ProofExpansion public

------------------------------------------------------------------------
-- Secondary sources can accelerate navigation without becoming legal proof.
------------------------------------------------------------------------

data NavigationSourceKind : Set where
  wikipediaNavigation
  wikidataNavigation
  journalNavigation
  treatiseNavigation
  digestNavigation
  lawReformNavigation
  : NavigationSourceKind

record NavigationExpansion : Set where
  constructor navigationExpansion
  field
    sourceKind : NavigationSourceKind
    seedReference : String
    candidateConceptReference : String
    candidateAuthorityReference : String
    navigationOnly : Bool
    navigationOnlyIsTrue : navigationOnly ≡ true
    navigationReference : String

open NavigationExpansion public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data QueryExpansionAutomaticallyProofExpansion : Set where
data NavigationIdentityAutomaticallyExactAuthority : Set where
data SecondarySourceAutomaticallyPaysBindingRule : Set where
data MoreSynonymsAutomaticallyIncreaseProofValue : Set where

queryExpansionDoesNotPayProof : QueryExpansionAutomaticallyProofExpansion → ⊥
queryExpansionDoesNotPayProof ()

navigationIdentityDoesNotBecomeExactAuthority :
  NavigationIdentityAutomaticallyExactAuthority → ⊥
navigationIdentityDoesNotBecomeExactAuthority ()

secondarySourceDoesNotPayBindingRule : SecondarySourceAutomaticallyPaysBindingRule → ⊥
secondarySourceDoesNotPayBindingRule ()

moreSynonymsDoNotGuaranteeProofValue : MoreSynonymsAutomaticallyIncreaseProofValue → ⊥
moreSynonymsDoNotGuaranteeProofValue ()

record ExpansionBoundary : Set where
  constructor expansionBoundary
  field
    queryExpansionAndProofExpansionSeparated : Bool
    queryExpansionAndProofExpansionSeparatedIsTrue :
      queryExpansionAndProofExpansionSeparated ≡ true
    secondarySourcesMayImproveNavigation : Bool
    secondarySourcesMayImproveNavigationIsTrue : secondarySourcesMayImproveNavigation ≡ true
    navigationAutomaticallyPaysLegalProof : Bool
    navigationAutomaticallyPaysLegalProofIsFalse : navigationAutomaticallyPaysLegalProof ≡ false

canonicalExpansionBoundary : ExpansionBoundary
canonicalExpansionBoundary = expansionBoundary true refl true refl false refl
