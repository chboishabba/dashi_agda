module DASHI.Core.ExternalisationBoundaryEnrichmentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalExternalisationDepthBidiExact as X
import DASHI.Core.OpenScienceKnowledgeReleaseBidiExact as O
import DASHI.Core.ReferencePopulationRosterEnrichmentExact as R
import DASHI.Core.SelectorDiscriminationSearchExact as S

data ExternalisationFeature : Set where
  deepTechnicalExternalisation
  restrictedToPublicTransfer
  : ExternalisationFeature

record DeepFeatureWitness : Set where
  constructor deep-feature-witness
  field
    profile : X.TechnicalExternalisationProfile
    deep : X.DeepExternalisation profile
    witnessReference : String

open DeepFeatureWitness public

record BoundaryFeatureWitness : Set where
  constructor boundary-feature-witness
  field
    receipt : O.OpenScienceReceipt
    transfer : O.RestrictedToPublicTransfer receipt
    witnessReference : String

open BoundaryFeatureWitness public

record ExternalisationEnrichmentClaim
    (roster control : R.PopulationFeatureCount) : Set where
  constructor externalisation-enrichment-claim
  field
    feature : ExternalisationFeature
    matchedDesign : R.MatchedReferenceDesign
    enriched : R.FeatureEnriched roster control
    scoringReference : String

open ExternalisationEnrichmentClaim public

record FeatureAwareSelectorClaim
    (candidate : S.SelectorSearchCandidate) : Set where
  constructor feature-aware-selector-claim
  field
    feature : ExternalisationFeature
    admissible : S.AdmissibleSelectorExplanation candidate
    featureDiscriminationReference : String

open FeatureAwareSelectorClaim public

record ExternalisationSelectionCandidate
    (roster control : R.PopulationFeatureCount)
    (candidate : S.SelectorSearchCandidate) : Set where
  constructor externalisation-selection-candidate
  field
    enrichment : ExternalisationEnrichmentClaim roster control
    selector : FeatureAwareSelectorClaim candidate
    sameFeature :
      ExternalisationEnrichmentClaim.feature enrichment ≡
      FeatureAwareSelectorClaim.feature selector
    selectionHypothesisReference : String

open ExternalisationSelectionCandidate public

data MissingExternalisationSelectionReceipt : Set where
  missingPersonFeatureEvidence
  missingMatchedControlPopulation
  missingEnrichmentComparison
  missingFeatureAwareSelector
  missingSelectorProvenance
  : MissingExternalisationSelectionReceipt

record ExternalisationSelectionFrontier : Set where
  constructor externalisation-selection-frontier
  field
    feature : ExternalisationFeature
    missing : MissingExternalisationSelectionReceipt
    requestedEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open ExternalisationSelectionFrontier public

record ExternalisationSelectionBoundary : Set where
  constructor externalisation-selection-boundary
  field
    deepExternalisationEqualsRestrictedTransfer : Bool
    deepExternalisationEqualsRestrictedTransferIsFalse :
      deepExternalisationEqualsRestrictedTransfer ≡ false
    personFeatureEvidenceAloneEstablishesEnrichment : Bool
    personFeatureEvidenceAloneEstablishesEnrichmentIsFalse :
      personFeatureEvidenceAloneEstablishesEnrichment ≡ false
    enrichmentAloneEstablishesSelection : Bool
    enrichmentAloneEstablishesSelectionIsFalse :
      enrichmentAloneEstablishesSelection ≡ false
    publicVisibilityAloneDiscriminatesExternalisationDepth : Bool
    publicVisibilityAloneDiscriminatesExternalisationDepthIsFalse :
      publicVisibilityAloneDiscriminatesExternalisationDepth ≡ false
    featureAwareSelectionImpliesHarmOrActorIdentity : Bool
    featureAwareSelectionImpliesHarmOrActorIdentityIsFalse :
      featureAwareSelectionImpliesHarmOrActorIdentity ≡ false

canonicalExternalisationSelectionBoundary : ExternalisationSelectionBoundary
canonicalExternalisationSelectionBoundary = externalisation-selection-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
