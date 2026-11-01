module DASHI.Reasoning.JMDAristotleSymposiumEpistemicFirewallExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Interop.SensibLawFederatedZOSAcquisitionExact as Federated
import DASHI.Interop.WikimediaWorldBucketPublicationExact as WorldBucket
import DASHI.Ontology.LeanWikidataCertificateBridge as LeanWikidata
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.SFMVerifiedClaimPresentation as SFM
import DASHI.Wikimedia.WikipediaWholeCorpusPNFITIRSensibLawPipelineExact as Wikipedia

------------------------------------------------------------------------
-- JMD / ARISTOTLE SYMPOSIUM EPISTEMIC FIREWALL
--
-- The supplied Lean files distinguish two very different achievements:
--   (1) theorem derivation from a stipulated knowledge base, and
--   (2) evidence that the stipulated premises describe the external world.
--
-- This module makes that distinction first-class and welds it to the existing
-- DASHI Wikipedia/Wikidata, JMD/SOLFUNMEME and ZOS/eRDFa/IPFS authority
-- boundaries.  No new Wikipedia truth ontology is introduced.
------------------------------------------------------------------------

data EvidenceRole : Set where
  transcribedPremise : EvidenceRole
  derivedEntailment : EvidenceRole
  finiteModelWitness : EvidenceRole
  externalSourceObservation : EvidenceRole
  externallyGroundedClaim : EvidenceRole

data ImportedFormalStatus : Set where
  sourceReportedLeanTheorem : ImportedFormalStatus
  sourceReportedFiniteModel : ImportedFormalStatus
  sourceOnlyUnverifiedHere : ImportedFormalStatus

record FormalEntailmentAuthorityBoundary : Set where
  constructor formalEntailmentAuthorityBoundary
  field
    sourceOwner : String
    sourceAtlasRetained : Bool
    transcribedPremiseEqualsWorldFact : Bool
    derivedEntailmentEqualsEmpiricalSupport : Bool
    finiteModelSatisfiabilityEqualsExternalTruth : Bool
    leanKernelProofImportsAgdaProof : Bool
    sourcePreferenceCreatesClaimTruth : Bool
    sourceIPCreatesAuthorship : Bool
    sourceIPCreatesViewAttribution : Bool
    wikipediaBiasCandidateCreatesBiasFact : Bool
    wikidataIdentityCreatesClaimTruth : Bool
    cidCreatesSemanticAuthority : Bool
    publicationCreatesEvidencePayment : Bool
    externalReviewStillRequired : Bool

open FormalEntailmentAuthorityBoundary public

canonicalFormalEntailmentAuthorityBoundary : FormalEntailmentAuthorityBoundary
canonicalFormalEntailmentAuthorityBoundary =
  formalEntailmentAuthorityBoundary
    "James Michael DuPont (JMD / meta-introspector)"
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    true

------------------------------------------------------------------------
-- Finite collision 1: observed source IP does not determine authorship.
------------------------------------------------------------------------

data EditWorld : Set where
  sameIPJMDWorld : EditWorld
  sameIPOtherAuthorWorld : EditWorld

data ObservedIP : Set where
  sameObservedIP : ObservedIP

data AuthorshipQuery : Set where
  authorQuestion : AuthorshipQuery

data AuthorshipAnswer : Set where
  jmdAuthorship : AuthorshipAnswer
  otherAuthorship : AuthorshipAnswer

observedIP : EditWorld → ObservedIP
observedIP sameIPJMDWorld = sameObservedIP
observedIP sameIPOtherAuthorWorld = sameObservedIP

AuthorshipAnswerFor : AuthorshipQuery → Set
AuthorshipAnswerFor authorQuestion = AuthorshipAnswer

askAuthorship : (query : AuthorshipQuery) → EditWorld → AuthorshipAnswerFor query
askAuthorship authorQuestion sameIPJMDWorld = jmdAuthorship
askAuthorship authorQuestion sameIPOtherAuthorWorld = otherAuthorship

authorshipQuestions : Query.InquiryQuestionFamily EditWorld AuthorshipQuery
authorshipQuestions = Query.inquiryQuestionFamily AuthorshipAnswerFor askAuthorship

sourceIPDoesNotDetermineAuthorship :
  Query.FactorsThrough authorshipQuestions observedIP authorQuestion → ⊥
sourceIPDoesNotDetermineAuthorship factor = helper first second
  where
    first :
      jmdAuthorship ≡ Query.quotientAnswer factor sameObservedIP
    first = Query.factorisation factor sameIPJMDWorld

    second :
      otherAuthorship ≡ Query.quotientAnswer factor sameObservedIP
    second = Query.factorisation factor sameIPOtherAuthorWorld

    helper :
      jmdAuthorship ≡ Query.quotientAnswer factor sameObservedIP →
      otherAuthorship ≡ Query.quotientAnswer factor sameObservedIP →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- Finite collision 2: source preference/reputation does not determine truth.
------------------------------------------------------------------------

data SourcePreferenceWorld : Set where
  preferredClaimTrue : SourcePreferenceWorld
  preferredClaimFalse : SourcePreferenceWorld

data PreferenceSurface : Set where
  samePreferredSource : PreferenceSurface

data TruthQuery : Set where
  claimTruthQuestion : TruthQuery

data TruthAnswer : Set where
  claimSupportedHere : TruthAnswer
  claimNotSupportedHere : TruthAnswer

sourcePreference : SourcePreferenceWorld → PreferenceSurface
sourcePreference preferredClaimTrue = samePreferredSource
sourcePreference preferredClaimFalse = samePreferredSource

TruthAnswerFor : TruthQuery → Set
TruthAnswerFor claimTruthQuestion = TruthAnswer

askTruth : (query : TruthQuery) → SourcePreferenceWorld → TruthAnswerFor query
askTruth claimTruthQuestion preferredClaimTrue = claimSupportedHere
askTruth claimTruthQuestion preferredClaimFalse = claimNotSupportedHere

truthQuestions : Query.InquiryQuestionFamily SourcePreferenceWorld TruthQuery
truthQuestions = Query.inquiryQuestionFamily TruthAnswerFor askTruth

sourcePreferenceDoesNotDetermineTruth :
  Query.FactorsThrough truthQuestions sourcePreference claimTruthQuestion → ⊥
sourcePreferenceDoesNotDetermineTruth factor = helper first second
  where
    first :
      claimSupportedHere ≡ Query.quotientAnswer factor samePreferredSource
    first = Query.factorisation factor preferredClaimTrue

    second :
      claimNotSupportedHere ≡ Query.quotientAnswer factor samePreferredSource
    second = Query.factorisation factor preferredClaimFalse

    helper :
      claimSupportedHere ≡ Query.quotientAnswer factor samePreferredSource →
      claimNotSupportedHere ≡ Query.quotientAnswer factor samePreferredSource →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- Finite collision 3: the same formal consequence can sit above differently
-- grounded premises.  Therefore derivability alone cannot answer the empirical
-- support question.
------------------------------------------------------------------------

data FormalWorld : Set where
  theoremWithGroundedPremises : FormalWorld
  theoremWithTranscribedPremisesOnly : FormalWorld

data FormalEntailmentSurface : Set where
  sameDerivedEntailment : FormalEntailmentSurface

data GroundingQuery : Set where
  empiricalGroundingQuestion : GroundingQuery

data GroundingAnswer : Set where
  externallyGrounded : GroundingAnswer
  notExternallyGrounded : GroundingAnswer

formalEntailmentProjection : FormalWorld → FormalEntailmentSurface
formalEntailmentProjection theoremWithGroundedPremises = sameDerivedEntailment
formalEntailmentProjection theoremWithTranscribedPremisesOnly = sameDerivedEntailment

GroundingAnswerFor : GroundingQuery → Set
GroundingAnswerFor empiricalGroundingQuestion = GroundingAnswer

askGrounding : (query : GroundingQuery) → FormalWorld → GroundingAnswerFor query
askGrounding empiricalGroundingQuestion theoremWithGroundedPremises = externallyGrounded
askGrounding empiricalGroundingQuestion theoremWithTranscribedPremisesOnly = notExternallyGrounded

groundingQuestions : Query.InquiryQuestionFamily FormalWorld GroundingQuery
groundingQuestions = Query.inquiryQuestionFamily GroundingAnswerFor askGrounding

formalEntailmentDoesNotDetermineEmpiricalGrounding :
  Query.FactorsThrough
    groundingQuestions
    formalEntailmentProjection
    empiricalGroundingQuestion →
  ⊥
formalEntailmentDoesNotDetermineEmpiricalGrounding factor = helper first second
  where
    first :
      externallyGrounded ≡ Query.quotientAnswer factor sameDerivedEntailment
    first = Query.factorisation factor theoremWithGroundedPremises

    second :
      notExternallyGrounded ≡ Query.quotientAnswer factor sameDerivedEntailment
    second = Query.factorisation factor theoremWithTranscribedPremisesOnly

    helper :
      externallyGrounded ≡ Query.quotientAnswer factor sameDerivedEntailment →
      notExternallyGrounded ≡ Query.quotientAnswer factor sameDerivedEntailment →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- Existing owners remain canonical.  These values are deliberate imports so
-- future drift in Wikipedia/Wikidata, SFM presentation, or ZOS/IPFS publication
-- boundaries is visible to this bridge rather than silently duplicated.
------------------------------------------------------------------------

existingWikipediaBoundary : Wikipedia.WikipediaWholeCorpusBoundary
existingWikipediaBoundary = Wikipedia.canonicalWikipediaWholeCorpusBoundary

existingSFMViewAuthorityBoundary : SFM.SFMViewAuthorityBoundary
existingSFMViewAuthorityBoundary = SFM.canonicalSFMViewAuthorityBoundary

existingFederatedContentBoundary : Federated.FederatedContentBoundary
existingFederatedContentBoundary = Federated.canonicalFederatedContentBoundary

existingWorldBucketManifestBoundary : WorldBucket.WorldBucketManifestBoundary
existingWorldBucketManifestBoundary = WorldBucket.canonicalManifestBoundary

sourceOwnershipDeclaration : Source.OwnershipDeclaration
sourceOwnershipDeclaration = Source.jmdOwnershipDeclaration

leanCertificateTruthAuthorityStillFalse :
  (cert : LeanWikidata.LeanOntologyCertificate) →
  LeanWikidata.certificateCarriesTruthAuthority cert ≡ false
leanCertificateTruthAuthorityStillFalse = LeanWikidata.certificateTruthAuthorityIsFalse

leanCertificateEditAuthorityStillFalse :
  (cert : LeanWikidata.LeanOntologyCertificate) →
  LeanWikidata.certificateCarriesEditAuthority cert ≡ false
leanCertificateEditAuthorityStillFalse = LeanWikidata.certificateEditAuthorityIsFalse
