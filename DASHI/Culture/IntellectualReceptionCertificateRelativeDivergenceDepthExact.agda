module DASHI.Culture.IntellectualReceptionCertificateRelativeDivergenceDepthExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / CERTIFICATE-RELATIVE DIVERGENCE DEPTH
--
-- The first observation stage exposing divergence is indexed by certificate
-- support.  Different certificates over the same pair of fine histories can
-- therefore have different divergence-depth outcomes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionObserverDerivedSupportPartitionExact as Observer
import DASHI.Culture.IntellectualReceptionPrecisionFiltrationFirstDivergenceExact as Filtration

------------------------------------------------------------------------
-- 1. A support-relative divergence-depth outcome.
------------------------------------------------------------------------

data DivergenceDepthOutcome (support : Reuse.CertificateSupport) : Set where
  firstAt :
    (stage : Filtration.PrecisionStage) →
    Filtration.FirstSupportedDivergenceAt support stage →
    DivergenceDepthOutcome support

  noSupportedDivergenceInFiltration :
    (∀ {stage coordinate} →
      Filtration.SelectedAtStage stage coordinate →
      Reuse.SupportedCoordinate support coordinate →
      Observer.SharedByObserver coordinate) →
    DivergenceDepthOutcome support

------------------------------------------------------------------------
-- 2. Present/future-only support never diverges on this filtration.
------------------------------------------------------------------------

presentFutureSupportAlwaysShared :
  ∀ {stage coordinate} →
  Filtration.SelectedAtStage stage coordinate →
  Reuse.SupportedCoordinate Reuse.presentFutureSupport coordinate →
  Observer.SharedByObserver coordinate
presentFutureSupportAlwaysShared {coordinate = Reuse.presentCoordinate}
  selected Reuse.supportPresent = Observer.presentSharedByObserver
presentFutureSupportAlwaysShared {coordinate = Reuse.futureCoordinate}
  selected Reuse.supportFuture = Observer.futureSharedByObserver

presentFutureDivergenceDepth :
  DivergenceDepthOutcome Reuse.presentFutureSupport
presentFutureDivergenceDepth =
  noSupportedDivergenceInFiltration presentFutureSupportAlwaysShared

------------------------------------------------------------------------
-- 3. Authority-sensitive support first diverges exactly at stage 2.
------------------------------------------------------------------------

authoritySensitiveDivergenceDepth :
  DivergenceDepthOutcome Reuse.authoritySensitiveSupport
authoritySensitiveDivergenceDepth =
  firstAt
    Filtration.stage2PresentFutureAuthority
    Filtration.authorityFirstDivergesAtStage2

------------------------------------------------------------------------
-- 4. The first two stages cannot witness supported divergence.
------------------------------------------------------------------------

noAuthorityFirstDivergenceAtStage0 :
  Filtration.FirstSupportedDivergenceAt
    Reuse.authoritySensitiveSupport
    Filtration.stage0Present → ⊥
noAuthorityFirstDivergenceAtStage0 witness
  with Filtration.coordinate witness
     | Filtration.supported witness
     | Filtration.selectedHere witness
     | Filtration.divergentHere witness
... | Reuse.presentCoordinate | Reuse.supportPresent | Filtration.s0Present | divergent =
      divergent Observer.presentSharedByObserver

noAuthorityFirstDivergenceAtStage1 :
  Filtration.FirstSupportedDivergenceAt
    Reuse.authoritySensitiveSupport
    Filtration.stage1PresentFuture → ⊥
noAuthorityFirstDivergenceAtStage1 witness
  with Filtration.coordinate witness
     | Filtration.supported witness
     | Filtration.selectedHere witness
     | Filtration.divergentHere witness
... | Reuse.presentCoordinate | Reuse.supportPresent | Filtration.s1Present | divergent =
      divergent Observer.presentSharedByObserver
... | Reuse.futureCoordinate | Reuse.supportFuture | Filtration.s1Future | divergent =
      divergent Observer.futureSharedByObserver

------------------------------------------------------------------------
-- 5. Same histories and filtration can induce different consumer depths.
------------------------------------------------------------------------

data CertificateDepthCode : Set where
  finiteStage2Depth
  noDivergenceWithinFiltration
  : CertificateDepthCode

depthCode : Reuse.CertificateSupport → CertificateDepthCode
depthCode Reuse.presentFutureSupport = noDivergenceWithinFiltration
depthCode Reuse.authoritySensitiveSupport = finiteStage2Depth

certificateDepthsDiffer :
  depthCode Reuse.presentFutureSupport
  ≡ depthCode Reuse.authoritySensitiveSupport → ⊥
certificateDepthsDiffer ()

------------------------------------------------------------------------
-- 6. Consumer-relative depth is not a global history distance.
------------------------------------------------------------------------

data ConsumerRelativeDepthPromotesGlobalHistoryDistance : Set where
data InfiniteWithinFiltrationPromotesAbsoluteIndistinguishability : Set where
data DivergenceDepthPromotesPAdicValuation : Set where

consumerRelativeDepthDoesNotPromoteGlobalHistoryDistance :
  ConsumerRelativeDepthPromotesGlobalHistoryDistance → ⊥
consumerRelativeDepthDoesNotPromoteGlobalHistoryDistance ()

infiniteWithinFiltrationDoesNotPromoteAbsoluteIndistinguishability :
  InfiniteWithinFiltrationPromotesAbsoluteIndistinguishability → ⊥
infiniteWithinFiltrationDoesNotPromoteAbsoluteIndistinguishability ()

divergenceDepthDoesNotPromotePAdicValuation :
  DivergenceDepthPromotesPAdicValuation → ⊥
divergenceDepthDoesNotPromotePAdicValuation ()

------------------------------------------------------------------------
-- 7. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionCertificateRelativeDivergenceDepthBoundary : Set where
  constructor intellectual-reception-certificate-relative-divergence-depth-boundary
  field
    divergenceDepthIsSupportIndexed : Bool
    sameHistoriesCanYieldDifferentCertificateDepths : Bool
    presentFutureSupportDivergesInCurrentFiltration : Bool
    authoritySensitiveSupportFirstDivergesAtStage2 : Bool
    noDivergenceWithinFiniteFiltrationMeansAbsoluteEquality : Bool
    divergenceDepthIsGlobalHistoryDistance : Bool
    divergenceDepthIsLiteralPAdicValuation : Bool
    sourceAttributionBoundarySurvivesDepthComparison : Bool

canonicalIntellectualReceptionCertificateRelativeDivergenceDepthBoundary :
  IntellectualReceptionCertificateRelativeDivergenceDepthBoundary
canonicalIntellectualReceptionCertificateRelativeDivergenceDepthBoundary =
  intellectual-reception-certificate-relative-divergence-depth-boundary
    true true false true false false false true
