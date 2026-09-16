module DASHI.Wikimedia.MaboReviewedContextFederationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

-- Canonical merged review/provenance owners.  This module is a thin parity
-- bridge for the SLR P7b runtime and does not introduce another Wikimedia
-- ontology, review calculus, or legal-IR payment model.
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact
import DASHI.Wikimedia.SensibLawBoundaryArtifactMorphismExact
import DASHI.Wikimedia.SensibLawStatementBundleSparseReopenExact
import DASHI.Wikimedia.MaboPropertyTripleProjectionExact

------------------------------------------------------------------------
-- Runtime identity / bounded producer surface
------------------------------------------------------------------------

slrRepository : String
slrRepository = "chboishabba/slr"

slrBranch : String
slrBranch = "agent/mabo-context-federation-v1"

wikidataProviderGreenHead : String
wikidataProviderGreenHead = "bbb155aa5cb0cac2e5a36dc1e955ae688c406086"

maboQid : String
maboQid = "Q1501525"

maboRevision : String
maboRevision = "2333409615"

data MaboContextProperty : Set where
  p1001 p710 p4884 p1594 p4006 : MaboContextProperty

propertyId : MaboContextProperty → String
propertyId p1001 = "P1001"
propertyId p710 = "P710"
propertyId p4884 = "P4884"
propertyId p1594 = "P1594"
propertyId p4006 = "P4006"

relationRole : MaboContextProperty → String
relationRole p1001 = "context:wikidata:jurisdiction"
relationRole p710 = "context:wikidata:participant"
relationRole p4884 = "context:wikidata:court"
relationRole p1594 = "context:wikidata:judge"
relationRole p4006 = "context:wikidata:overrules"

------------------------------------------------------------------------
-- Review -> reviewed context -> persistence -> unchanged walker
------------------------------------------------------------------------

record ReviewedContextFederationBoundary : Set where
  constructor reviewedContextFederationBoundary
  field
    wikidataRevisionPinnedProviderPaid : Bool
    explicitCandidateReviewRequired : Bool
    unreviewedCandidateMaterialises : Bool
    reviewedContextCreatesSemanticAuthority : Bool
    reviewedContextCreatesLegalIRSupport : Bool
    applicabilityPromoted : Bool
    claimTruthPromoted : Bool
    walkerPerformsNetworkIO : Bool

open ReviewedContextFederationBoundary public

canonicalBoundary : ReviewedContextFederationBoundary
canonicalBoundary =
  reviewedContextFederationBoundary
    true
    true
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- P4006 remains an AuthoritySource *candidate family* upstream only.
-- Candidate producer family naming does not itself establish legal authority.
------------------------------------------------------------------------

p4006AuthoritySourceCandidateCreatesAuthority : Bool
p4006AuthoritySourceCandidateCreatesAuthority = false

------------------------------------------------------------------------
-- Explicit non-collapse firewalls.
------------------------------------------------------------------------

data CandidatePropertyEdgeEqualsReviewedContextEdge : Set where
data ReviewedContextEdgeEqualsLegalIRSupport : Set where
data AuthoritySourceCandidateEqualsLegalAuthority : Set where
data PersistedContextRelationEqualsApplicability : Set where
data PersistedContextRelationEqualsClaimTruth : Set where

candidateIsNotReviewedByExistence :
  CandidatePropertyEdgeEqualsReviewedContextEdge → ⊥
candidateIsNotReviewedByExistence ()

reviewedContextIsNotLegalIRSupport :
  ReviewedContextEdgeEqualsLegalIRSupport → ⊥
reviewedContextIsNotLegalIRSupport ()

authoritySourceCandidateIsNotAuthority :
  AuthoritySourceCandidateEqualsLegalAuthority → ⊥
authoritySourceCandidateIsNotAuthority ()

persistedContextDoesNotPayApplicability :
  PersistedContextRelationEqualsApplicability → ⊥
persistedContextDoesNotPayApplicability ()

persistedContextDoesNotPayClaimTruth :
  PersistedContextRelationEqualsClaimTruth → ⊥
persistedContextDoesNotPayClaimTruth ()

------------------------------------------------------------------------
-- Exact parity receipt for the current runtime cut.
------------------------------------------------------------------------

record RuntimeParityReceipt : Set where
  constructor runtimeParityReceipt
  field
    providerHead : String
    providerRevisionPinned : Bool
    reviewedEdgeBuilderPresent : Bool
    persistenceReceiptPresent : Bool
    unchangedWalkerConsumesPersistedEdges : Bool
    legalIRPromotionPerformed : Bool

open RuntimeParityReceipt public

currentRuntimeParity : RuntimeParityReceipt
currentRuntimeParity =
  runtimeParityReceipt
    wikidataProviderGreenHead
    true
    true
    true
    true
    false

providerRevisionPinned : providerRevisionPinned currentRuntimeParity ≡ true
providerRevisionPinned = refl

reviewedEdgeBuilderPresent : reviewedEdgeBuilderPresent currentRuntimeParity ≡ true
reviewedEdgeBuilderPresent = refl

persistenceReceiptPresent : persistenceReceiptPresent currentRuntimeParity ≡ true
persistenceReceiptPresent = refl

unchangedWalkerConsumesPersistedEdges :
  unchangedWalkerConsumesPersistedEdges currentRuntimeParity ≡ true
unchangedWalkerConsumesPersistedEdges = refl

legalIRPromotionNotPerformed : legalIRPromotionPerformed currentRuntimeParity ≡ false
legalIRPromotionNotPerformed = refl
