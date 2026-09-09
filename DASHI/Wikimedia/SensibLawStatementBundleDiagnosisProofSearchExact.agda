module DASHI.Wikimedia.SensibLawStatementBundleDiagnosisProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Wikimedia.SensibLawStatementBundleSparseReopenExact as Bundle

------------------------------------------------------------------------
-- STATEMENT-BUNDLE DIAGNOSIS FIBRE + LEAST-PRIVILEGE SEARCH ROUTING
--
-- Cross-pollinates the repository proof-search constitution into the native
-- Wikidata/SensibLaw bundle review loop.  A changed bundle coordinate does not
-- automatically determine one diagnosis, and a live diagnosis does not
-- automatically license theorem search.  Proof, acquisition, and review moves
-- remain distinct ways of paying different producer obligations.
------------------------------------------------------------------------

data BundleDiagnosis : Set where
  mainSnakMismatch
  qualifierDrift
  referenceDrift
  rankQuestion
  provenanceGap
  : BundleDiagnosis

record BundleDiagnosisFibre : Set₁ where
  constructor bundle-diagnosis-fibre
  field
    live : BundleDiagnosis → Set
    fibreReference : String
open BundleDiagnosisFibre public

-- The bounded Nat review packet can legitimately keep several explanations
-- live at once.  No singleton diagnosis is forced merely by splitRequired.
data NatLiveDiagnosis : BundleDiagnosis → Set where
  natMainLive : NatLiveDiagnosis mainSnakMismatch
  natQualifierLive : NatLiveDiagnosis qualifierDrift
  natReferenceLive : NatLiveDiagnosis referenceDrift
  natRankLive : NatLiveDiagnosis rankQuestion
  natProvenanceLive : NatLiveDiagnosis provenanceGap

natDiagnosisFibre : BundleDiagnosisFibre
natDiagnosisFibre =
  bundle-diagnosis-fibre
    NatLiveDiagnosis
    "Nat P5991/P14143 statement-bundle live diagnosis fibre"

------------------------------------------------------------------------
-- First live obligation chooses a producer kind, not a completed repair.
------------------------------------------------------------------------

data BundleProducerKind : Set where
  establishSemanticCorrespondence
  proveQualifierTransport
  acquireReferenceEvidence
  interpretRank
  acquireProvenanceEvidence
  : BundleProducerKind

producerForDiagnosis : BundleDiagnosis → BundleProducerKind
producerForDiagnosis mainSnakMismatch = establishSemanticCorrespondence
producerForDiagnosis qualifierDrift = proveQualifierTransport
producerForDiagnosis referenceDrift = acquireReferenceEvidence
producerForDiagnosis rankQuestion = interpretRank
producerForDiagnosis provenanceGap = acquireProvenanceEvidence

------------------------------------------------------------------------
-- Search mechanisms stay separate.
------------------------------------------------------------------------

data SearchRouteKind : Set where
  proofRoute acquisitionRoute reviewRoute : SearchRouteKind

data RouteCapability : SearchRouteKind → Set where
  admittedProofRoute : ProofSearch.RouteAdmission → RouteCapability proofRoute
  admittedAcquisitionRoute : String → RouteCapability acquisitionRoute
  admittedReviewRoute : String → RouteCapability reviewRoute

record BundleSearchCandidate : Set₁ where
  constructor bundle-search-candidate
  field
    targetDiagnosis : BundleDiagnosis
    producer : BundleProducerKind
    producerExact : producer ≡ producerForDiagnosis targetDiagnosis
    routeKind : SearchRouteKind
    capability : RouteCapability routeKind
    moveKind : Loop.EpistemicMoveKind
    cost : Nat
    candidateReference : String
    consumerGainReference : String
open BundleSearchCandidate public

record EligibleBundleSearchCandidate
    (fibre : BundleDiagnosisFibre)
    (candidate : BundleSearchCandidate) : Set₁ where
  constructor eligible-bundle-search-candidate
  field
    targetStillLive : live fibre (targetDiagnosis candidate)
    producerPaymentReference : String
open EligibleBundleSearchCandidate public

------------------------------------------------------------------------
-- Admitted proof routes use the repository least-privilege admission object.
------------------------------------------------------------------------

semanticCorrespondenceAdmission : ProofSearch.RouteAdmission
semanticCorrespondenceAdmission =
  ProofSearch.route-admission
    ProofSearch.exactTarget
    ProofSearch.sameObjectSpine
    ProofSearch.prerequisiteClosure
    ProofSearch.noKnownNoGo
    ProofSearch.noCircularDependency
    ProofSearch.noSilentStrengthening
    ProofSearch.authorityAdequacy
    ProofSearch.noveltyAgainstRepo
    ProofSearch.frontierImproves

qualifierTransportAdmission : ProofSearch.RouteAdmission
qualifierTransportAdmission = semanticCorrespondenceAdmission

semanticProofCandidate : BundleSearchCandidate
semanticProofCandidate =
  bundle-search-candidate
    mainSnakMismatch
    establishSemanticCorrespondence
    refl
    proofRoute
    (admittedProofRoute semanticCorrespondenceAdmission)
    Loop.thinkMove
    (suc (suc (suc zero)))
    "prove exact P5991/P14143 semantic correspondence on the same statement-bundle carrier"
    "collapse mainsnak semantic mismatch for the selected migration consumer"

qualifierProofCandidate : BundleSearchCandidate
qualifierProofCandidate =
  bundle-search-candidate
    qualifierDrift
    proveQualifierTransport
    refl
    proofRoute
    (admittedProofRoute qualifierTransportAdmission)
    Loop.thinkMove
    (suc (suc zero))
    "prove exact qualifier-preserving transport for the bounded qualifier family"
    "collapse qualifier-drift diagnosis only if the transport theorem is actually paid"

referenceLookupCandidate : BundleSearchCandidate
referenceLookupCandidate =
  bundle-search-candidate
    referenceDrift
    acquireReferenceEvidence
    refl
    acquisitionRoute
    (admittedAcquisitionRoute "follow/inspect P248/P854 source candidate with revision-locked receipt")
    Loop.lookMove
    (suc zero)
    "acquire/inspect the changed reference source rather than theorem-searching around it"
    "collapse reference-drift diagnosis if the acquired source/reference relation resolves it"

rankReviewCandidate : BundleSearchCandidate
rankReviewCandidate =
  bundle-search-candidate
    rankQuestion
    interpretRank
    refl
    reviewRoute
    (admittedReviewRoute "review native rank treatment without equating rank to truth")
    Loop.lookMove
    (suc zero)
    "inspect rank semantics for the active consumer"
    "collapse rank-question diagnosis without promoting rank to epistemic truth"

provenanceLookupCandidate : BundleSearchCandidate
provenanceLookupCandidate =
  bundle-search-candidate
    provenanceGap
    acquireProvenanceEvidence
    refl
    acquisitionRoute
    (admittedAcquisitionRoute "acquire independent provenance receipt; P143 alone is insufficient")
    Loop.lookMove
    (suc zero)
    "acquire provenance rather than manufacture it from a theorem or import marker"
    "collapse provenance-gap diagnosis only after the provenance producer is paid"

semanticProofIsLiveProofRoute : ProofSearch.LiveProofSearch
semanticProofIsLiveProofRoute = ProofSearch.elaborateRoute semanticCorrespondenceAdmission

------------------------------------------------------------------------
-- Coordinate-conditioned search: the existing sparse wake constrains which
-- diagnosis/search candidates enter the current comparison set.
------------------------------------------------------------------------

data ReferenceWakeDeclared : BundleSearchCandidate → Set where
  referenceLookupDeclared : ReferenceWakeDeclared referenceLookupCandidate

referenceLookupEligible :
  EligibleBundleSearchCandidate natDiagnosisFibre referenceLookupCandidate
referenceLookupEligible =
  eligible-bundle-search-candidate
    natReferenceLive
    "P854 sparse wake selects acquireReferenceEvidence producer"

record LeastCostBundleSearchChoice
    (fibre : BundleDiagnosisFibre)
    (Declared : BundleSearchCandidate → Set) : Set₁ where
  constructor least-cost-bundle-search-choice
  field
    selected : BundleSearchCandidate
    selectedDeclared : Declared selected
    selectedEligible : EligibleBundleSearchCandidate fibre selected
    minimalCost :
      (alternative : BundleSearchCandidate) →
      Declared alternative →
      cost selected ≤ cost alternative
    selectionReference : String
open LeastCostBundleSearchChoice public

referenceWakeChoice :
  LeastCostBundleSearchChoice natDiagnosisFibre ReferenceWakeDeclared
referenceWakeChoice =
  least-cost-bundle-search-choice
    referenceLookupCandidate
    referenceLookupDeclared
    referenceLookupEligible
    referenceMinimal
    "changed P854 coordinate admits only the declared reference-evidence route"
  where
    referenceMinimal :
      (alternative : BundleSearchCandidate) →
      ReferenceWakeDeclared alternative →
      cost referenceLookupCandidate ≤ cost alternative
    referenceMinimal .referenceLookupCandidate referenceLookupDeclared = s≤s z≤n

referenceWakeSelectsAcquisitionNotProof :
  routeKind (selected referenceWakeChoice) ≡ acquisitionRoute
referenceWakeSelectsAcquisitionNotProof = refl

referenceWakeUsesLookMove :
  moveKind (selected referenceWakeChoice) ≡ Loop.lookMove
referenceWakeUsesLookMove = refl

referenceWakeTargetsReferenceDiagnosis :
  targetDiagnosis (selected referenceWakeChoice) ≡ referenceDrift
referenceWakeTargetsReferenceDiagnosis = refl

referenceWakeProducerIsReferenceEvidence :
  producer (selected referenceWakeChoice) ≡ acquireReferenceEvidence
referenceWakeProducerIsReferenceEvidence = refl

------------------------------------------------------------------------
-- No-collapse boundaries from proof-search + source-attribution constitutions.
------------------------------------------------------------------------

data TheoremNameClosesBundleDiagnosis : Set where
data ProofRouteAcquiresMissingReferenceSource : Set where
data AcquisitionRouteProvesSemanticEquivalence : Set where
data CheapestRouteCreatesAuthority : Set where
data SplitRequiredDeterminesUniqueDiagnosis : Set where
data MoreLemmasMeansMoreBundleProgress : Set where

theoremNameDoesNotCloseBundleDiagnosis : TheoremNameClosesBundleDiagnosis → ⊥
theoremNameDoesNotCloseBundleDiagnosis ()

proofRouteDoesNotAcquireMissingReferenceSource :
  ProofRouteAcquiresMissingReferenceSource → ⊥
proofRouteDoesNotAcquireMissingReferenceSource ()

acquisitionDoesNotProveSemanticEquivalence :
  AcquisitionRouteProvesSemanticEquivalence → ⊥
acquisitionDoesNotProveSemanticEquivalence ()

cheapestRouteDoesNotCreateAuthority : CheapestRouteCreatesAuthority → ⊥
cheapestRouteDoesNotCreateAuthority ()

splitRequiredDoesNotDetermineUniqueDiagnosis :
  SplitRequiredDeterminesUniqueDiagnosis → ⊥
splitRequiredDoesNotDetermineUniqueDiagnosis ()

moreLemmasDoesNotMeanMoreBundleProgress :
  MoreLemmasMeansMoreBundleProgress → ⊥
moreLemmasDoesNotMeanMoreBundleProgress ()

record BundleDiagnosisProofSearchBoundary : Set where
  constructor bundle-diagnosis-proof-search-boundary
  field
    splitRequiredMayHaveMultipleLiveDiagnoses : Bool
    proofRoutesRequireLeastPrivilegeAdmission : Bool
    referenceGapRoutesToAcquisition : Bool
    proofAndAcquisitionAreSameMechanism : Bool
    theoremNameClosesDiagnosis : Bool
    cheapestRouteCreatesAuthority : Bool
    progressMeasuredByLemmaCount : Bool

canonicalBundleDiagnosisProofSearchBoundary : BundleDiagnosisProofSearchBoundary
canonicalBundleDiagnosisProofSearchBoundary =
  bundle-diagnosis-proof-search-boundary true true true false false false false
