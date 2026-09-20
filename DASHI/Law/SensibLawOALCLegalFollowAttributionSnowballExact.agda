module DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Interop.SLRWikidataTypedTraversalParetoExact as Wikidata
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Law.SensibLawParetoProofDirectedCorpusSearchBidiExact as ParetoSearch
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact as Promotion
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts

------------------------------------------------------------------------
-- OALC / LEGALFOLLOW / ATTRIBUTION SNOWBALL
--
-- OALC is an Australian primary-law acquisition substrate.  A pinned OALC
-- source receipt contributes source identity, revision, text and provider
-- provenance.  It does not create legal truth, applicability, treatment,
-- citation-use classification, or consumer proof payment.
--
-- External identity (QID/canonical URL/etc.) snowballs opportunistically after
-- or alongside source acquisition.  "Worth checking" is a scheduling hint, not
-- a claim that a Wikidata item exists.
------------------------------------------------------------------------

data OalcDocumentKind : Set where
  decision : OalcDocumentKind
  primaryLegislation : OalcDocumentKind

record PinnedOalcSourceReceipt : Set where
  constructor pinnedOalcSourceReceipt
  field
    demandReference : String
    originReference : String
    citationReference : String
    corpusRevisionReference : String
    versionReference : String
    sourceReference : String
    jurisdictionReference : String
    documentKind : OalcDocumentKind
    courtReference : String
    dateReference : String
    canonicalTextDigestReference : String
    localArtifactReference : String
    resolutionPathReference : String
    networkRequestReference : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open PinnedOalcSourceReceipt public

------------------------------------------------------------------------
-- Dataset Viewer partial-index semantics.
------------------------------------------------------------------------

data OalcIndexCoverage : Set where
  completeIndex : OalcIndexCoverage
  partialIndex : OalcIndexCoverage

data ZeroRowDisposition : Set where
  completeIndexSourceResidual : ZeroRowDisposition
  revisionPinnedStreamingRequired : ZeroRowDisposition

zeroRowDisposition : OalcIndexCoverage → ZeroRowDisposition
zeroRowDisposition completeIndex = completeIndexSourceResidual
zeroRowDisposition partialIndex = revisionPinnedStreamingRequired

partialZeroRequiresStreaming :
  zeroRowDisposition partialIndex ≡ revisionPinnedStreamingRequired
partialZeroRequiresStreaming = refl

completeZeroRemainsSourceResidual :
  zeroRowDisposition completeIndex ≡ completeIndexSourceResidual
completeZeroRemainsSourceResidual = refl

------------------------------------------------------------------------
-- Exact revision identity cannot factor through citation-only metadata.
------------------------------------------------------------------------

data OalcWaltonsRevisionSituation : Set where
  waltonsPinnedRevisionA : OalcWaltonsRevisionSituation
  waltonsPinnedRevisionB : OalcWaltonsRevisionSituation

data CitationOnlySurface : Set where
  waltonsHca7CitationOnly : CitationOnlySurface

citationOnly :
  OalcWaltonsRevisionSituation → CitationOnlySurface
citationOnly waltonsPinnedRevisionA = waltonsHca7CitationOnly
citationOnly waltonsPinnedRevisionB = waltonsHca7CitationOnly

data ExactOalcRevision : Set where
  revisionA : ExactOalcRevision
  revisionB : ExactOalcRevision

exactRevision :
  OalcWaltonsRevisionSituation → ExactOalcRevision
exactRevision waltonsPinnedRevisionA = revisionA
exactRevision waltonsPinnedRevisionB = revisionB

revisionsDiffer :
  exactRevision waltonsPinnedRevisionA
    ≡
  exactRevision waltonsPinnedRevisionB → ⊥
revisionsDiffer ()

citationOnlyRevisionNonFactorability :
  NF.NonFactorabilityWitness citationOnly exactRevision
citationOnlyRevisionNonFactorability =
  NF.nonFactorabilityWitness
    waltonsPinnedRevisionA
    waltonsPinnedRevisionB
    refl
    revisionsDiffer

citationOnlyCannotRecoverPinnedRevision :
  NF.FactorsThrough citationOnly exactRevision → ⊥
citationOnlyCannotRecoverPinnedRevision =
  NF.witnessRulesOutEveryFlatFactorisation
    citationOnlyRevisionNonFactorability

------------------------------------------------------------------------
-- External identity scheduling.
--
-- This is deliberately *not* a probability model.  It records whether a QID
-- lookup is worth spending acquisition budget on for a particular legal-source
-- role.  Existence and exact identity still require an inspected result.
------------------------------------------------------------------------

data LegalIdentitySubjectKind : Set where
  doctrineConcept : LegalIdentitySubjectKind
  apexCourtCase : LegalIdentitySubjectKind
  lowerCourtCase : LegalIdentitySubjectKind
  legislationInstrument : LegalIdentitySubjectKind
  researchRequirement : LegalIdentitySubjectKind

data QidLookupPriority : Set where
  qidNotApplicable : QidLookupPriority
  qidOpportunistic : QidLookupPriority
  qidWorthChecking : QidLookupPriority
  qidHighValueLookup : QidLookupPriority

qidPriority : LegalIdentitySubjectKind → QidLookupPriority
qidPriority doctrineConcept = qidHighValueLookup
qidPriority apexCourtCase = qidWorthChecking
qidPriority lowerCourtCase = qidOpportunistic
qidPriority legislationInstrument = qidOpportunistic
qidPriority researchRequirement = qidNotApplicable

waltonsQidPriority :
  qidPriority apexCourtCase ≡ qidWorthChecking
waltonsQidPriority = refl

estoppelConceptQidPriority :
  qidPriority doctrineConcept ≡ qidHighValueLookup
estoppelConceptQidPriority = refl

researchRequirementQidPriority :
  qidPriority researchRequirement ≡ qidNotApplicable
researchRequirementQidPriority = refl

data ExternalIdentityStatus : Set where
  identityCandidate : ExternalIdentityStatus
  identityVerified : ExternalIdentityStatus

record LegalTraceExternalIdentityAttachment : Set where
  constructor legalTraceExternalIdentityAttachment
  field
    semanticReference : String
    identityKind : Identity.ExternalIdentityKind
    identityValue : String
    status : ExternalIdentityStatus
    verificationReference : String
    supplementalOnly : Bool
    supplementalOnlyIsTrue : supplementalOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    createsApplicability : Bool
    createsApplicabilityIsFalse : createsApplicability ≡ false

open LegalTraceExternalIdentityAttachment public

waltonsQidDemand : Identity.ExternalIdentityDemand
waltonsQidDemand =
  Identity.mkOptionalIdentityDemand
    "Australian contracts / Waltons LegalFollow"
    "inspect Wikidata candidate after exact HCA source identity"
    "Waltons Stores (Interstate) Ltd v Maher"
    Identity.wikidataQid
    (Identity.unresolved
      "QID not assumed; lookup is opportunistic identity enrichment")

estoppelConceptQidDemand : Identity.ExternalIdentityDemand
estoppelConceptQidDemand =
  Identity.mkOptionalIdentityDemand
    "Australian contracts / estoppel concept"
    "inspect external concept identity"
    "estoppel"
    Identity.wikidataQid
    (Identity.unresolved
      "concept identity remains unresolved until inspected")

------------------------------------------------------------------------
-- Attribution and Wikidata control-plane parents are reused directly.
------------------------------------------------------------------------

AttributionBoundary : Set
AttributionBoundary = Attribution.AttributionSnowballBoundary

attributionBoundaryPaid : AttributionBoundary
attributionBoundaryPaid =
  Attribution.canonicalAttributionSnowballBoundary

ExternalIdentityPolicy : Set
ExternalIdentityPolicy = Identity.SnowballExternalIdentityPolicy

externalIdentityPolicyPaid : ExternalIdentityPolicy
externalIdentityPolicyPaid =
  Identity.canonicalExternalIdentityPolicy

WikidataControlPlaneBoundary : Set
WikidataControlPlaneBoundary = Wikidata.SensibLawWikidataControlPlaneAnchor

wikidataControlPlaneBoundaryPaid : WikidataControlPlaneBoundary
wikidataControlPlaneBoundaryPaid =
  Wikidata.canonicalSensibLawWikidataControlPlaneAnchor

LegalFollowBoundary : Set
LegalFollowBoundary = LegalFollow.LegalFollowProofSearchBoundary

legalFollowBoundaryPaid : LegalFollowBoundary
legalFollowBoundaryPaid =
  LegalFollow.canonicalLegalFollowProofSearchBoundary

------------------------------------------------------------------------
-- Contract-trace identity priority is supplemental to the typed legal trace.
------------------------------------------------------------------------

ContractTraceBoundary : Set
ContractTraceBoundary = Contracts.AustralianContractsFollowBoundary

contractTraceBoundaryPaid : ContractTraceBoundary
contractTraceBoundaryPaid =
  Contracts.canonicalAustralianContractsFollowBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OalcReceiptCreatesLegalAuthority : Set where
data OalcFullTextCreatesLegalProposition : Set where
data OalcCitationEdgeMeansPropositionAdoption : Set where
data OalcZeroResultMeansNegativeLegalEvidence : Set where
data PartialIndexZeroMayCloseSourceResidual : Set where
data QidPriorityEntailsQidExistence : Set where
data VerifiedQidCreatesApplicability : Set where
data WikidataClassCreatesCanonicalLegalOntology : Set where
data QidLookupMayPreemptLiveProofGapByDefault : Set where
data CitationOnlyMetadataSufficesForRevisionSensitiveConsumer : Set where

oalcReceiptDoesNotCreateAuthority :
  OalcReceiptCreatesLegalAuthority → ⊥
oalcReceiptDoesNotCreateAuthority ()

oalcTextDoesNotCreateProposition :
  OalcFullTextCreatesLegalProposition → ⊥
oalcTextDoesNotCreateProposition ()

citationEdgeDoesNotMeanAdoption :
  OalcCitationEdgeMeansPropositionAdoption → ⊥
citationEdgeDoesNotMeanAdoption ()

zeroResultDoesNotBecomeNegativeLegalEvidence :
  OalcZeroResultMeansNegativeLegalEvidence → ⊥
zeroResultDoesNotBecomeNegativeLegalEvidence ()

partialZeroCannotCloseResidual :
  PartialIndexZeroMayCloseSourceResidual → ⊥
partialZeroCannotCloseResidual ()

qidPriorityDoesNotEntailExistence :
  QidPriorityEntailsQidExistence → ⊥
qidPriorityDoesNotEntailExistence ()

qidDoesNotCreateApplicability :
  VerifiedQidCreatesApplicability → ⊥
qidDoesNotCreateApplicability ()

wikidataClassDoesNotBecomeLegalOntology :
  WikidataClassCreatesCanonicalLegalOntology → ⊥
wikidataClassDoesNotBecomeLegalOntology ()

qidCleanupDoesNotPreemptLiveProofGap :
  QidLookupMayPreemptLiveProofGapByDefault → ⊥
qidCleanupDoesNotPreemptLiveProofGap ()

citationOnlyCannotServeRevisionSensitiveConsumer :
  CitationOnlyMetadataSufficesForRevisionSensitiveConsumer → ⊥
citationOnlyCannotServeRevisionSensitiveConsumer ()

record OalcLegalFollowAttributionBoundary : Set where
  constructor oalcLegalFollowAttributionBoundary
  field
    oalcCarriesPinnedSourceIdentity : Bool
    oalcCarriesPinnedSourceIdentityIsTrue :
      oalcCarriesPinnedSourceIdentity ≡ true

    caseLawAndLegislationShareAcquisitionSubstrate : Bool
    caseLawAndLegislationShareAcquisitionSubstrateIsTrue :
      caseLawAndLegislationShareAcquisitionSubstrate ≡ true

    partialZeroFallsBackToPinnedStreaming : Bool
    partialZeroFallsBackToPinnedStreamingIsTrue :
      partialZeroFallsBackToPinnedStreaming ≡ true

    sourceIdentitySnowballs : Bool
    sourceIdentitySnowballsIsTrue :
      sourceIdentitySnowballs ≡ true

    qidLookupIsOpportunistic : Bool
    qidLookupIsOpportunisticIsTrue :
      qidLookupIsOpportunistic ≡ true

    qidPriorityClaimsExistence : Bool
    qidPriorityClaimsExistenceIsFalse :
      qidPriorityClaimsExistence ≡ false

    oalcCreatesLegalAuthority : Bool
    oalcCreatesLegalAuthorityIsFalse :
      oalcCreatesLegalAuthority ≡ false

    wikidataCreatesCanonicalLegalOntology : Bool
    wikidataCreatesCanonicalLegalOntologyIsFalse :
      wikidataCreatesCanonicalLegalOntology ≡ false

canonicalOalcLegalFollowAttributionBoundary :
  OalcLegalFollowAttributionBoundary
canonicalOalcLegalFollowAttributionBoundary =
  oalcLegalFollowAttributionBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
