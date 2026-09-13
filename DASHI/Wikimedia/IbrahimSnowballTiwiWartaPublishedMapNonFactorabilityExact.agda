module DASHI.Wikimedia.IbrahimSnowballTiwiWartaPublishedMapNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiWartaTypologyMechanismBidiDeweyDoiQidExact as Warta

------------------------------------------------------------------------
-- PUBLISHED-MAP NONFACTORABILITY FOR THE TWO TIWI WARTA SUBTYPES
--
-- Young et al. 2025 defines two local warta eucalypt-savanna ecosystem types,
-- but explicitly reports that the mapping/training data could not distinguish
-- them.  The published spatial model therefore maps one eucalypt-savanna class
-- representing a mosaic of both.  This is a source-level information-loss
-- boundary: no post-processing of that published map class can recover whether
-- a site is warta type 1 or type 2 without additional subtype-resolving data.
------------------------------------------------------------------------

savannaQid : Identity.ExternalIdentityDemand
savannaQid = Warta.savannaQid

ecosystemQid : Identity.ExternalIdentityDemand
ecosystemQid = Warta.ecosystemQid

localWartaQid : Identity.ExternalIdentityDemand
localWartaQid = Warta.wartaLocalQid

publishedMapCoordinate : Traversal.DashiKnowledgeCoordinate
publishedMapCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiWartaPublishedMapNonFactorabilityExact.agda"
  "Young et al. 2025 published Tiwi ecosystem map"
  "577.4 — savanna ecology; published map classification does not recover local warta subtype"
  "Q42320; Q37813; unresolved local-warta QID"
  "DOI 10.1111/cobi.70099; Supporting Information cobi70099-sup-0001-SupMatt.docx"

subtypeConsumerCoordinate : Traversal.DashiKnowledgeCoordinate
subtypeConsumerCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiWartaPublishedMapNonFactorabilityExact.agda"
  "local warta subtype consumer"
  "577.4 — same coarse Dewey coordinate for both subtypes"
  "Q42320; unresolved local-warta QID"
  "DOI 10.1111/cobi.70099"

publishedMapNominatesSubtypeResidual : Traversal.DashiFirstLinkEdge
publishedMapNominatesSubtypeResidual = Traversal.dashi-first-link-edge
  publishedMapCoordinate subtypeConsumerCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "the published map nominates a subtype-resolution residual; it does not pay subtype identity because the two warta savannas were merged into one mapped class"
  true

record PublishedMapPrimaryReceipt : Set where
  constructor published-map-primary-receipt
  field
    source : Warta.WartaPrimarySource
    sourceIsYoung2025 : source ≡ Warta.youngEtAl2025
    trainingPointCount : Nat
    mappedEcosystemTypeCount : Nat
    twoWartaSubtypesDefined : Bool
    twoWartaSubtypesSeparatelyMapped : Bool
    combinedEucalyptSavannaMapClass : Bool
    limitationReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiBoundaryOwner : Attribution.ClaimOwner
    dashiOwnsBoundaryOnly : dashiBoundaryOwner ≡ Attribution.dashiFormalisationOwner

open PublishedMapPrimaryReceipt public

canonicalPublishedMapPrimaryReceipt : PublishedMapPrimaryReceipt
canonicalPublishedMapPrimaryReceipt = published-map-primary-receipt
  Warta.youngEtAl2025 refl
  5298 11
  true false true
  "Young et al. 2025 Methods/Training points and Mapping results: 5298 training points for 11 ecosystem types; eucalypt open-forest savanna and eucalypt mixed-species savanna could not be distinguished in existing datasets and were mapped as one eucalypt-savanna mosaic class"
  Attribution.externalSourceOwner refl
  Attribution.dashiFormalisationOwner refl

------------------------------------------------------------------------
-- Exact nonfactorability witness.
------------------------------------------------------------------------

data PublishedWartaMapClass : Set where
  mappedEucalyptSavannaMosaic : PublishedWartaMapClass

publishedMapClassOf : Warta.WartaSubtype → PublishedWartaMapClass
publishedMapClassOf Warta.eucalyptOpenForestSavanna = mappedEucalyptSavannaMosaic
publishedMapClassOf Warta.eucalyptMixedSpeciesSavanna = mappedEucalyptSavannaMosaic

subtypeIndicator : Warta.WartaSubtype → Bool
subtypeIndicator Warta.eucalyptOpenForestSavanna = false
subtypeIndicator Warta.eucalyptMixedSpeciesSavanna = true

subtypeIndicatorDiffers :
  subtypeIndicator Warta.eucalyptOpenForestSavanna ≡
  subtypeIndicator Warta.eucalyptMixedSpeciesSavanna → ⊥
subtypeIndicatorDiffers ()

publishedMapSubtypeNonFactorability :
  NF.NonFactorabilityWitness publishedMapClassOf subtypeIndicator
publishedMapSubtypeNonFactorability =
  NF.nonFactorabilityWitness
    Warta.eucalyptOpenForestSavanna
    Warta.eucalyptMixedSpeciesSavanna
    refl
    subtypeIndicatorDiffers

publishedMapCannotRecoverWartaSubtype :
  NF.FactorsThrough publishedMapClassOf subtypeIndicator → ⊥
publishedMapCannotRecoverWartaSubtype =
  NF.witnessRulesOutEveryFlatFactorisation
    publishedMapSubtypeNonFactorability

publishedMapRechartingCannotRecoverWartaSubtype :
  ∀ {Recharted : Set} →
  (rechart : PublishedWartaMapClass → Recharted) →
  NF.FactorsThrough (λ subtype → rechart (publishedMapClassOf subtype)) subtypeIndicator → ⊥
publishedMapRechartingCannotRecoverWartaSubtype rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart publishedMapSubtypeNonFactorability

------------------------------------------------------------------------
-- Consequence for the 88-site mechanism join.
------------------------------------------------------------------------

record WartaSpatialJoinResidual : Set where
  constructor warta-spatial-join-residual
  field
    localSubtypeDefinitionsPaid : Bool
    publishedMapAcquired : Bool
    publishedMapClassIdentityPaid : Bool
    exact88SiteMapPixelJoinMayBeAcquired : Bool
    exact88SiteWartaSubtypePaid : Bool
    publishedMapAloneCanPaySubtype : Bool
    subtypeResolvingExternalDataRequired : Bool
    subtypeSpecificMechanismEffectPaid : Bool
    firstUnpaidGate : String

open WartaSpatialJoinResidual public

canonicalWartaSpatialJoinResidual : WartaSpatialJoinResidual
canonicalWartaSpatialJoinResidual = warta-spatial-join-residual
  true true true true
  false false true false
  "Acquire a subtype-resolving primary carrier (field/training labels or geometry) that distinguishes warta type 1 from type 2 at the mechanism sites; the published Young et al. ecosystem map cannot pay this because it intentionally merges the two savanna subtypes"

record WartaMapSnowballAcquisitionState : Set where
  constructor warta-map-snowball-acquisition-state
  field
    Young2025PrimaryAcquired : Bool
    supportingInformationAcquired : Bool
    publishedMapAcquired : Bool
    trainingPointMetadataAcquired : Bool
    mapPixelAt88SitesMayBeAcquired : Bool
    laterMechanismEvidenceRetained : Bool

record WartaMapSnowballPaymentState : Set where
  constructor warta-map-snowball-payment-state
  field
    sourceIdentityPaid : Bool
    sourceAttributionPaid : Bool
    mapClassPaid : Bool
    exactMapPixelJoinPaid : Bool
    localSubtypePaid : Bool
    mechanismBySubtypePaid : Bool
    firstUnpaidGate : String

snowballAcquisitionDoesNotAdvanceWartaMapPayment :
  WartaMapSnowballAcquisitionState → WartaMapSnowballPaymentState → WartaMapSnowballPaymentState
snowballAcquisitionDoesNotAdvanceWartaMapPayment _ payment = payment

data PublishedMapMeansLocalSubtype : Set where
data MorePreciseMapPixelMeansSubtype : Set where
data QidMeansLocalSubtype : Set where
data DeweyMeansLocalSubtype : Set where
data PrimarySourceCompletenessMeansSubtypeJoin : Set where

publishedMapDoesNotMeanLocalSubtype : PublishedMapMeansLocalSubtype → ⊥
publishedMapDoesNotMeanLocalSubtype ()

morePreciseMapPixelDoesNotMeanSubtype : MorePreciseMapPixelMeansSubtype → ⊥
morePreciseMapPixelDoesNotMeanSubtype ()

qidDoesNotMeanLocalSubtype : QidMeansLocalSubtype → ⊥
qidDoesNotMeanLocalSubtype ()

deweyDoesNotMeanLocalSubtype : DeweyMeansLocalSubtype → ⊥
deweyDoesNotMeanLocalSubtype ()

primarySourceCompletenessDoesNotCreateSubtypeJoin : PrimarySourceCompletenessMeansSubtypeJoin → ⊥
primarySourceCompletenessDoesNotCreateSubtypeJoin ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
