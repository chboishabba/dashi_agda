module DASHI.Law.SensibLawMaboDistributedLegalCorpusMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Interop.SensibLawFederatedZOSAcquisitionExact as Federation
import DASHI.Law.SensibLawPreferredAustralianAuthorityAcquisitionExact as Authority
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Law.SensibLawMaboPabaiExecutableProofSearchExact as MaboSearch

------------------------------------------------------------------------
-- MABO DISTRIBUTED LEGAL CORPUS MATERIALISATION
--
-- This owner is deliberately not another corpus/storage subsystem.  It pins
-- which legal-consumer queries may use a skeletal representation and when the
-- existing proof-search/federation machinery must reacquire an exact source.
--
-- The four coordinates remain separate:
--   semantic adequacy / materialisation / retrieval lane / legal authority.
------------------------------------------------------------------------

data LegalMaterialisation : Set where
  referenceOnly skeletalLegalGraph derivedSpan verifiedFullSource : LegalMaterialisation

infix 4 _≺m_
data _≺m_ : LegalMaterialisation → LegalMaterialisation → Set where
  reference≺skeleton : referenceOnly ≺m skeletalLegalGraph
  skeleton≺span : skeletalLegalGraph ≺m derivedSpan
  span≺full : derivedSpan ≺m verifiedFullSource

data LegalRetrievalLane : Set where
  localLane : LegalRetrievalLane
  oalcHfLane : LegalRetrievalLane
  ipfsContentMirrorLane : LegalRetrievalLane
  livePrimaryReacquisitionLane : LegalRetrievalLane

record DistributedLegalCorpusBoundary : Set where
  constructor distributedLegalCorpusBoundary
  field
    materialisationAndRetrievalAreSeparateCoordinates : Bool
    materialisationAndRetrievalAreSeparateCoordinatesIsTrue :
      materialisationAndRetrievalAreSeparateCoordinates ≡ true
    moreMaterialisedMeansMoreAuthoritative : Bool
    moreMaterialisedMeansMoreAuthoritativeIsFalse :
      moreMaterialisedMeansMoreAuthoritative ≡ false
    skeletonMayNavigateWithoutFullTextResident : Bool
    skeletonMayNavigateWithoutFullTextResidentIsTrue :
      skeletonMayNavigateWithoutFullTextResident ≡ true
    exactQuotationRequiresExactText : Bool
    exactQuotationRequiresExactTextIsTrue : exactQuotationRequiresExactText ≡ true
    strictPrimaryReviewRequiresVerifiedFullSource : Bool
    strictPrimaryReviewRequiresVerifiedFullSourceIsTrue :
      strictPrimaryReviewRequiresVerifiedFullSource ≡ true
    strictPrimaryReviewRequiresExactSpan : Bool
    strictPrimaryReviewRequiresExactSpanIsTrue :
      strictPrimaryReviewRequiresExactSpan ≡ true
    sharedPublicSkeletonCreatesDistributedAuthority : Bool
    sharedPublicSkeletonCreatesDistributedAuthorityIsFalse :
      sharedPublicSkeletonCreatesDistributedAuthority ≡ false

open DistributedLegalCorpusBoundary public

canonicalDistributedLegalCorpusBoundary : DistributedLegalCorpusBoundary
canonicalDistributedLegalCorpusBoundary =
  distributedLegalCorpusBoundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Query-indexed adequacy witness.
--
-- Both worlds expose exactly the same legal skeleton.  That skeleton is enough
-- for the navigation question but not for exact quotation.  This is a finite
-- witness that storage adequacy is consumer-relative rather than intrinsic.
------------------------------------------------------------------------

data MaboMaterialisationWorld : Set where
  skeletonOnlyWorld fullSourceWorld : MaboMaterialisationWorld

data LegalSkeletonObservation : Set where
  sameMaboAuthoritySkeleton : LegalSkeletonObservation

data DiscoveryObservation : Set where
  sameOalcDiscoveryObject : DiscoveryObservation

data MaboMaterialisationQuery : Set where
  navigationQuery exactQuotationQuery strictPrimaryPaymentQuery : MaboMaterialisationQuery

data MaboMaterialisationAnswer : Set where
  navigationAnswer quotationUnavailable quotationAvailable paymentIneligible paymentEligible : MaboMaterialisationAnswer

skeletonProjection : MaboMaterialisationWorld → LegalSkeletonObservation
skeletonProjection world = sameMaboAuthoritySkeleton

discoveryProjection : MaboMaterialisationWorld → DiscoveryObservation
discoveryProjection world = sameOalcDiscoveryObject

materialisationAnswer : MaboMaterialisationQuery → MaboMaterialisationWorld → MaboMaterialisationAnswer
materialisationAnswer navigationQuery world = navigationAnswer
materialisationAnswer exactQuotationQuery skeletonOnlyWorld = quotationUnavailable
materialisationAnswer exactQuotationQuery fullSourceWorld = quotationAvailable
materialisationAnswer strictPrimaryPaymentQuery skeletonOnlyWorld = paymentIneligible
materialisationAnswer strictPrimaryPaymentQuery fullSourceWorld = paymentEligible

materialisationSemantics :
  Query.QuerySemantics MaboMaterialisationWorld MaboMaterialisationQuery MaboMaterialisationAnswer
materialisationSemantics = Query.querySemantics materialisationAnswer

NavigationAdequateThroughSkeleton : Set₁
NavigationAdequateThroughSkeleton =
  Query.AdequateFor skeletonProjection materialisationSemantics navigationQuery

maboNavigationAdequateThroughSkeleton : NavigationAdequateThroughSkeleton
maboNavigationAdequateThroughSkeleton =
  Query.factorsForQuery (λ observation → navigationAnswer) (λ state → refl)

QuotationSkeletonDefect : Set₁
QuotationSkeletonDefect =
  Query.QueryAdequacyDefect skeletonProjection materialisationSemantics exactQuotationQuery

maboQuotationSkeletonDefect : QuotationSkeletonDefect
maboQuotationSkeletonDefect =
  Query.queryAdequacyDefect
    skeletonOnlyWorld
    fullSourceWorld
    refl
    (λ ())

PrimaryPaymentDiscoveryDefect : Set₁
PrimaryPaymentDiscoveryDefect =
  Query.QueryAdequacyDefect discoveryProjection materialisationSemantics strictPrimaryPaymentQuery

maboPrimaryPaymentDiscoveryDefect : PrimaryPaymentDiscoveryDefect
maboPrimaryPaymentDiscoveryDefect =
  Query.queryAdequacyDefect
    skeletonOnlyWorld
    fullSourceWorld
    refl
    (λ ())

maboSkeletonCannotPayExactQuotation :
  Query.AdequateFor skeletonProjection materialisationSemantics exactQuotationQuery → ⊥
maboSkeletonCannotPayExactQuotation =
  Query.queryAdequacyDefectBlocksFactorisation maboQuotationSkeletonDefect

maboDiscoveryObjectCannotPayStrictPrimaryAuthority :
  Query.AdequateFor discoveryProjection materialisationSemantics strictPrimaryPaymentQuery → ⊥
maboDiscoveryObjectCannotPayStrictPrimaryAuthority =
  Query.queryAdequacyDefectBlocksFactorisation maboPrimaryPaymentDiscoveryDefect

------------------------------------------------------------------------
-- Existing Australian/federated lanes pinned as parents.
------------------------------------------------------------------------

selectedOalcBoundary : Authority.OalcExactMncBoundary
selectedOalcBoundary = Authority.canonicalOalcExactMncBoundary

selectedFederatedContentBoundary : Federation.FederatedContentBoundary
selectedFederatedContentBoundary = Federation.canonicalFederatedContentBoundary

selectedProgressiveDeepeningBoundary : Federation.ProgressiveDeepeningBoundary
selectedProgressiveDeepeningBoundary = Federation.canonicalProgressiveDeepeningBoundary

selectedLegalFollowBoundary : LegalFollow.LegalFollowProofSearchBoundary
selectedLegalFollowBoundary = LegalFollow.canonicalLegalFollowProofSearchBoundary

selectedMaboSearchBoundary : MaboSearch.MaboPabaiSearchBoundary
selectedMaboSearchBoundary = MaboSearch.canonicalMaboPabaiSearchBoundary

------------------------------------------------------------------------
-- Australian corpus hierarchy: discovery/possession/authority/payment are not
-- collapsed.  The hierarchy is operational, not a ranking of truth.
------------------------------------------------------------------------

record AustralianLegalCorpusHierarchy : Set where
  constructor australianLegalCorpusHierarchy
  field
    oalcHfSupportsDiscoveryAndSkeletalFollow : Bool
    oalcHfSupportsDiscoveryAndSkeletalFollowIsTrue :
      oalcHfSupportsDiscoveryAndSkeletalFollow ≡ true
    ipfsMirrorIsSameDigestAlternativePossession : Bool
    ipfsMirrorIsSameDigestAlternativePossessionIsTrue :
      ipfsMirrorIsSameDigestAlternativePossession ≡ true
    officialCourtIsPrimaryManifestationCandidate : Bool
    officialCourtIsPrimaryManifestationCandidateIsTrue :
      officialCourtIsPrimaryManifestationCandidate ≡ true
    verifiedFullSourceAndExactSpanCreatePaymentEligibility : Bool
    verifiedFullSourceAndExactSpanCreatePaymentEligibilityIsTrue :
      verifiedFullSourceAndExactSpanCreatePaymentEligibility ≡ true
    paymentEligibilityEqualsPayment : Bool
    paymentEligibilityEqualsPaymentIsFalse : paymentEligibilityEqualsPayment ≡ false

open AustralianLegalCorpusHierarchy public

canonicalAustralianLegalCorpusHierarchy : AustralianLegalCorpusHierarchy
canonicalAustralianLegalCorpusHierarchy =
  australianLegalCorpusHierarchy true refl true refl true refl true refl false refl

------------------------------------------------------------------------
-- Concrete distributed Mabo specimen.
--
-- The specimen starts from the existing recognition-condition residual.  A
-- legal-follow skeleton may identify a candidate authority cheaply, but a strict
-- legal consumer detects that exact source text/span is still absent and emits a
-- reacquisition obligation.  Reacquisition reaches eligibility only; reviewed
-- payment remains a later operation.
------------------------------------------------------------------------

record MaboDistributedSpecimen : Set where
  constructor maboDistributedSpecimen
  field
    propositionResidualReference : String
    legalFollowSkeletonIdentifiesAuthority : Bool
    strictConsumerDetectsMissingFullText : Bool
    reacquisitionRequired : Bool
    verifiedSourceAndExactSpanRequired : Bool
    verifiedSourceAndSpanCreateEligibility : Bool
    reacquisitionAutomaticallyPaysResidual : Bool
    britishAuthorityDiscoveryAutomaticallyAppliesRuleInAustralia : Bool

open MaboDistributedSpecimen public

canonicalMaboDistributedSpecimen : MaboDistributedSpecimen
canonicalMaboDistributedSpecimen =
  maboDistributedSpecimen
    "Mabo recognitionConditionResidual"
    true
    true
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HFShardAvailabilityImpliesSourcePossession : Set where
data HFShardAvailabilityImpliesAuthority : Set where
data OalcHitImpliesBindingAuthority : Set where
data LegalFollowEdgeImpliesApplicability : Set where
data LegalFollowEdgeImpliesEvidencePayment : Set where
data CIDAvailabilityImpliesSemanticAuthority : Set where
data SkeletonNavigationAdequacyImpliesQuotationAdequacy : Set where
data BritishAuthorityDiscoveredImpliesBritishRuleAppliesInAustralia : Set where
data FullSourceAcquiredImpliesPropositionTrue : Set where
data MoreMaterialisedImpliesMoreAuthoritative : Set where

hfShardAvailabilityDoesNotImplySourcePossession :
  HFShardAvailabilityImpliesSourcePossession → ⊥
hfShardAvailabilityDoesNotImplySourcePossession ()

hfShardAvailabilityDoesNotImplyAuthority : HFShardAvailabilityImpliesAuthority → ⊥
hfShardAvailabilityDoesNotImplyAuthority ()

oalcHitDoesNotImplyBindingAuthority : OalcHitImpliesBindingAuthority → ⊥
oalcHitDoesNotImplyBindingAuthority ()

legalFollowEdgeDoesNotImplyApplicability : LegalFollowEdgeImpliesApplicability → ⊥
legalFollowEdgeDoesNotImplyApplicability ()

legalFollowEdgeDoesNotPayEvidence : LegalFollowEdgeImpliesEvidencePayment → ⊥
legalFollowEdgeDoesNotPayEvidence ()

cidAvailabilityDoesNotCreateSemanticAuthority : CIDAvailabilityImpliesSemanticAuthority → ⊥
cidAvailabilityDoesNotCreateSemanticAuthority ()

navigationAdequacyDoesNotLiftToQuotation :
  SkeletonNavigationAdequacyImpliesQuotationAdequacy → ⊥
navigationAdequacyDoesNotLiftToQuotation ()

britishAuthorityDiscoveryDoesNotApplyRuleInAustralia :
  BritishAuthorityDiscoveredImpliesBritishRuleAppliesInAustralia → ⊥
britishAuthorityDiscoveryDoesNotApplyRuleInAustralia ()

fullSourceAcquisitionDoesNotMakePropositionTrue :
  FullSourceAcquiredImpliesPropositionTrue → ⊥
fullSourceAcquisitionDoesNotMakePropositionTrue ()

moreMaterialisedDoesNotMeanMoreAuthoritative :
  MoreMaterialisedImpliesMoreAuthoritative → ⊥
moreMaterialisedDoesNotMeanMoreAuthoritative ()
