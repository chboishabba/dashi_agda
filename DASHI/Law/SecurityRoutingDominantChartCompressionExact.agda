module DASHI.Law.SecurityRoutingDominantChartCompressionExact where

open import DASHI.Core.Prelude

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import DASHI.Law.SecurityRoutingComparatorHypervoxelExact as Routing

------------------------------------------------------------------------
-- SECURITY INTENSITY / CLASSIFICATION AS LOSSY OBSERVERS
------------------------------------------------------------------------

securityIntensityCompression :
  Compression.ProjectionInadequacyReceipt
    Routing.coarseSecurityObserver
    Routing.routingTarget
securityIntensityCompression =
  Compression.projection-inadequacy-receipt
    Compression.administrativeClassificationCompression
    "coarse security-intensity observer"
    "protective-versus-coercive routing consumer"
    "same high-security intensity can coexist with protective-dominant and coercive-dominant routing"
    Routing.coarseIntensityNonFactorability
    true refl
    false refl
    false refl
    false refl

securityIntensityCannotCarryRouting :
  INF.FactorsThrough Routing.coarseSecurityObserver Routing.routingTarget → ⊥
securityIntensityCannotCarryRouting =
  Compression.projectionCannotFactorTarget securityIntensityCompression

securityIntensityRelabellingCannotRecoverRouting :
  ∀ {Recharted : Set} →
  (rechart : Routing.CoarseSecurityIntensity → Recharted) →
  INF.FactorsThrough
    (λ event → rechart (Routing.coarseSecurityObserver event))
    Routing.routingTarget → ⊥
securityIntensityRelabellingCannotRecoverRouting =
  Compression.projectionCannotBeRepairedByPostcomposition securityIntensityCompression

------------------------------------------------------------------------
-- A system-is-what-it-does boundary for security policy.
------------------------------------------------------------------------

record SecurityOperationalSemanticsBoundary : Set where
  constructor security-operational-semantics-boundary
  field
    declaredSecurityPurposeDeterminesRealizedRouting : Bool
    declaredSecurityPurposeDeterminesRealizedRoutingIsFalse :
      declaredSecurityPurposeDeterminesRealizedRouting ≡ false
    highSecurityIntensityDeterminesProtectivePurpose : Bool
    highSecurityIntensityDeterminesProtectivePurposeIsFalse :
      highSecurityIntensityDeterminesProtectivePurpose ≡ false
    highSecurityIntensityDeterminesCoercivePurpose : Bool
    highSecurityIntensityDeterminesCoercivePurposeIsFalse :
      highSecurityIntensityDeterminesCoercivePurpose ≡ false
    realizedRoutingMustBeInspectedSeparately : Bool
    realizedRoutingMustBeInspectedSeparatelyIsTrue :
      realizedRoutingMustBeInspectedSeparately ≡ true
    classificationProvenanceRemainsSeparateResidual : Bool
    classificationProvenanceRemainsSeparateResidualIsTrue :
      classificationProvenanceRemainsSeparateResidual ≡ true

canonicalSecurityOperationalSemanticsBoundary : SecurityOperationalSemanticsBoundary
canonicalSecurityOperationalSemanticsBoundary =
  security-operational-semantics-boundary
    false refl
    false refl
    false refl
    true refl
    true refl

------------------------------------------------------------------------
-- Amalek / terminalisation x-pollination.
--
-- Ordinary asymmetric routing is NOT by itself terminalisation.  Terminalising
-- risk begins when the authority loop additionally closes correction and turns
-- dissent/evidence into confirming fault.
------------------------------------------------------------------------

amalekClosedAuthorityRisk : Amalek.ClosedAuthorityLoop
amalekClosedAuthorityRisk = Amalek.canonicalClosedAuthorityRisk

ordinaryRoutingDifferenceIsNotTerminalisation :
  Compression.terminalisationIsOnlyOrdinaryProjectionLoss
    Compression.canonicalTerminalisationRiskBoundary ≡ false
ordinaryRoutingDifferenceIsNotTerminalisation = refl

terminalisingLoopMayCloseCorrection :
  Compression.terminalisationMayCloseCorrectionChannel
    Compression.canonicalTerminalisationRiskBoundary ≡ true
terminalisingLoopMayCloseCorrection = refl

closedAmalekLoopHasNoIndependentCorrection :
  Amalek.correctionChannelIndependent amalekClosedAuthorityRisk ≡ false
closedAmalekLoopHasNoIndependentCorrection = refl

humanGroupEnemyPromotionRemainsForbidden :
  Compression.humanGroupMayBePromotedToTerminalEnemyPredicate
    Compression.canonicalTerminalisationRiskBoundary ≡ false
humanGroupEnemyPromotionRemainsForbidden = refl

------------------------------------------------------------------------
-- Comparator residual routing remains source-disciplined.
------------------------------------------------------------------------

observedRoutingStillDoesNotSkipSecurityNeedComparison :
  Routing.firstComparatorResidual
    Routing.routingDifferencePersistsAfterConditioning
    Routing.canonicalObservedRoutingOnly
  ≡ Routing.securityNeedResidual
observedRoutingStillDoesNotSkipSecurityNeedComparison = refl

record SecurityCompressionBoundary : Set where
  constructor security-compression-boundary
  field
    compressionWitnessProvesDiscriminatoryMotive : Bool
    compressionWitnessProvesDiscriminatoryMotiveIsFalse :
      compressionWitnessProvesDiscriminatoryMotive ≡ false
    routingDifferenceProvesFascism : Bool
    routingDifferenceProvesFascismIsFalse : routingDifferenceProvesFascism ≡ false
    terminalisationEqualsEverySecurityClassification : Bool
    terminalisationEqualsEverySecurityClassificationIsFalse :
      terminalisationEqualsEverySecurityClassification ≡ false
    realizedRoutingAndCorrectionResponseRemainSystemRelevant : Bool
    realizedRoutingAndCorrectionResponseRemainSystemRelevantIsTrue :
      realizedRoutingAndCorrectionResponseRemainSystemRelevant ≡ true

canonicalSecurityCompressionBoundary : SecurityCompressionBoundary
canonicalSecurityCompressionBoundary =
  security-compression-boundary
    false refl
    false refl
    false refl
    true refl
