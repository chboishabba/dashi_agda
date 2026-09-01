module DASHI.Culture.IntellectualReceptionConsumerObservationDemandPreorderExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / CONSUMER OBSERVATION-DEMAND PREORDER
--
-- A consumer is observationally no-more-demanding than another when the
-- current filtration can expose its supported divergence using no finer a
-- precision.  The "no divergence within this filtration" outcome is therefore
-- treated as requiring strictly beyond the currently modelled finite depth.
--
-- This is a separation-demand order, not support inclusion, truth strength,
-- importance, evidential quality, or a global distance on histories.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionCertificateRelativeDivergenceDepthExact as Depth

------------------------------------------------------------------------
-- 1. Current finite demand codes derived from the existing depth outcomes.
------------------------------------------------------------------------

data ObservationDemandCode : Set where
  exposedByStage2
  beyondCurrentFiltration
  : ObservationDemandCode

demandCode : Reuse.CertificateSupport → ObservationDemandCode
demandCode Reuse.presentFutureSupport = beyondCurrentFiltration
demandCode Reuse.authoritySensitiveSupport = exposedByStage2

presentFutureDemandCodeMatchesDepth :
  demandCode Reuse.presentFutureSupport ≡ beyondCurrentFiltration
presentFutureDemandCodeMatchesDepth = refl

authorityDemandCodeMatchesDepth :
  demandCode Reuse.authoritySensitiveSupport ≡ exposedByStage2
authorityDemandCodeMatchesDepth = refl

------------------------------------------------------------------------
-- 2. "No finer observation than" is ordered in increasing demanded depth.
--
-- exposedByStage2 <= beyondCurrentFiltration.
------------------------------------------------------------------------

data NoFinerThan : ObservationDemandCode → ObservationDemandCode → Set where
  stage2-refl : NoFinerThan exposedByStage2 exposedByStage2
  stage2-before-beyond : NoFinerThan exposedByStage2 beyondCurrentFiltration
  beyond-refl : NoFinerThan beyondCurrentFiltration beyondCurrentFiltration

noFinerThanRefl :
  (demand : ObservationDemandCode) →
  NoFinerThan demand demand
noFinerThanRefl exposedByStage2 = stage2-refl
noFinerThanRefl beyondCurrentFiltration = beyond-refl

noFinerThanTrans :
  ∀ {a b c} →
  NoFinerThan a b →
  NoFinerThan b c →
  NoFinerThan a c
noFinerThanTrans stage2-refl bc = bc
noFinerThanTrans stage2-before-beyond beyond-refl = stage2-before-beyond
noFinerThanTrans beyond-refl beyond-refl = beyond-refl

------------------------------------------------------------------------
-- 3. Consumer preorder induced by certificate-relative divergence depth.
------------------------------------------------------------------------

ConsumerNoMoreObservationDemanding :
  Reuse.CertificateSupport → Reuse.CertificateSupport → Set
ConsumerNoMoreObservationDemanding left right =
  NoFinerThan (demandCode left) (demandCode right)

consumerDemandRefl :
  (support : Reuse.CertificateSupport) →
  ConsumerNoMoreObservationDemanding support support
consumerDemandRefl support = noFinerThanRefl (demandCode support)

consumerDemandTrans :
  ∀ {a b c} →
  ConsumerNoMoreObservationDemanding a b →
  ConsumerNoMoreObservationDemanding b c →
  ConsumerNoMoreObservationDemanding a c
consumerDemandTrans = noFinerThanTrans

------------------------------------------------------------------------
-- 4. Canonical comparison.
--
-- Authority-sensitive divergence is exposed at stage 2; present/future-only
-- support remains shared throughout the current filtration.  Hence authority
-- support requires no finer separation observation than present/future support.
------------------------------------------------------------------------

authorityNoMoreDemandingThanPresentFuture :
  ConsumerNoMoreObservationDemanding
    Reuse.authoritySensitiveSupport
    Reuse.presentFutureSupport
authorityNoMoreDemandingThanPresentFuture = stage2-before-beyond

presentFutureNotNoMoreDemandingThanAuthority :
  ConsumerNoMoreObservationDemanding
    Reuse.presentFutureSupport
    Reuse.authoritySensitiveSupport → ⊥
presentFutureNotNoMoreDemandingThanAuthority ()

canonicalDemandIsStrict :
  ConsumerNoMoreObservationDemanding
    Reuse.authoritySensitiveSupport
    Reuse.presentFutureSupport
canonicalDemandIsStrict = authorityNoMoreDemandingThanPresentFuture

------------------------------------------------------------------------
-- 5. Depth outcomes are the source interpretation of the demand codes.
------------------------------------------------------------------------

presentFutureDepthOutcome :
  Depth.DivergenceDepthOutcome Reuse.presentFutureSupport
presentFutureDepthOutcome = Depth.presentFutureDivergenceDepth

authorityDepthOutcome :
  Depth.DivergenceDepthOutcome Reuse.authoritySensitiveSupport
authorityDepthOutcome = Depth.authoritySensitiveDivergenceDepth

certificateDepthCodesStillDiffer :
  Depth.depthCode Reuse.presentFutureSupport
  ≡ Depth.depthCode Reuse.authoritySensitiveSupport → ⊥
certificateDepthCodesStillDiffer = Depth.certificateDepthsDiffer

------------------------------------------------------------------------
-- 6. Separation demand is independent of support inclusion and value ranking.
------------------------------------------------------------------------

data ObservationDemandPromotesSupportInclusion : Set where
data ObservationDemandPromotesTruthStrength : Set where
data ObservationDemandPromotesImportance : Set where
data ObservationDemandPromotesEvidenceQuality : Set where
data ObservationDemandPromotesGlobalHistoryDistance : Set where
data ObservationDemandPromotesPAdicNorm : Set where

observationDemandDoesNotPromoteSupportInclusion :
  ObservationDemandPromotesSupportInclusion → ⊥
observationDemandDoesNotPromoteSupportInclusion ()

observationDemandDoesNotPromoteTruthStrength :
  ObservationDemandPromotesTruthStrength → ⊥
observationDemandDoesNotPromoteTruthStrength ()

observationDemandDoesNotPromoteImportance :
  ObservationDemandPromotesImportance → ⊥
observationDemandDoesNotPromoteImportance ()

observationDemandDoesNotPromoteEvidenceQuality :
  ObservationDemandPromotesEvidenceQuality → ⊥
observationDemandDoesNotPromoteEvidenceQuality ()

observationDemandDoesNotPromoteGlobalHistoryDistance :
  ObservationDemandPromotesGlobalHistoryDistance → ⊥
observationDemandDoesNotPromoteGlobalHistoryDistance ()

observationDemandDoesNotPromotePAdicNorm :
  ObservationDemandPromotesPAdicNorm → ⊥
observationDemandDoesNotPromotePAdicNorm ()

------------------------------------------------------------------------
-- 7. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionConsumerObservationDemandPreorderBoundary : Set where
  constructor intellectual-reception-consumer-observation-demand-preorder-boundary
  field
    demandOrderIsCertificateRelative : Bool
    demandOrderIsReflexive : Bool
    demandOrderIsTransitive : Bool
    stage2ExposureRequiresNoFinerObservationThanBeyondFiltration : Bool
    authoritySupportIsNoMoreDemandingThanPresentFutureSupport : Bool
    presentFutureSupportIsNoMoreDemandingThanAuthoritySupport : Bool
    demandOrderIsSupportInclusion : Bool
    demandOrderRanksTruth : Bool
    demandOrderRanksImportance : Bool
    demandOrderIsGlobalHistoryDistance : Bool
    demandOrderIsLiteralPAdicNorm : Bool
    sourceAttributionBoundarySurvivesDemandOrdering : Bool

canonicalIntellectualReceptionConsumerObservationDemandPreorderBoundary :
  IntellectualReceptionConsumerObservationDemandPreorderBoundary
canonicalIntellectualReceptionConsumerObservationDemandPreorderBoundary =
  intellectual-reception-consumer-observation-demand-preorder-boundary
    true true true true true false false false false false false true
