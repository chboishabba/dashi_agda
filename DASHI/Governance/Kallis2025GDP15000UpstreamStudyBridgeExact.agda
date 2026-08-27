module DASHI.Governance.Kallis2025GDP15000UpstreamStudyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.SafeJustSourceRegistryExact as Sources
import DASHI.Governance.Kallis2025EvidenceAtlasExact as Atlas
import DASHI.Governance.Kallis2025ClaimByClaimEvidenceRealizationExact as Claims

------------------------------------------------------------------------
-- KALLIS 2025 -> COLLSTE ET AL. 2021: EXPLICIT UPSTREAM STUDY EDGE
--
-- Review source:
-- Giorgos Kallis et al., "Post-growth: the science of wellbeing within
-- planetary boundaries", The Lancet Planetary Health 9 (2025), e62--e78,
-- DOI 10.1016/S2542-5196(24)00310-3.
--
-- Upstream study:
-- David Collste, Sarah E. Cornell, Jorgen Randers, Johan Rockstrom &
-- Per Espen Stoknes,
-- "Human well-being in the Anthropocene: limits to growth",
-- Global Sustainability 4 (2021), e30,
-- DOI 10.1017/sus.2021.26.
--
-- The upstream study tracks SDG 1--7 indicators against GDP per person across
-- seven world regions and the world and reports the approximately US$15,000
-- (2011 PPP) pattern.  This bridge retains the existing DASHI residual
-- associationNotCausation: neither the study nor the Kallis review is promoted
-- into a context-free causal GDP threshold or policy mandate.
------------------------------------------------------------------------

collste2021 : Sources.SourceReference
collste2021 = Sources.sourceReference
  "David Collste; Sarah E. Cornell; Jorgen Randers; Johan Rockstrom; Per Espen Stoknes"
  "Human well-being in the Anthropocene: limits to growth"
  "Global Sustainability 4:e30"
  2021
  "DOI"
  "10.1017/sus.2021.26"
  "peer-reviewed cross-regional empirical study"
  "upstream source for the approximately US$15,000 2011-PPP SDG 1-7 pattern; not a context-free causal income threshold or policy mandate"

record UpstreamStudyEdge : Set where
  constructor upstreamStudyEdge
  field
    reviewSource : Sources.SourceReference
    upstreamSource : Sources.SourceReference
    reviewAnchor : Atlas.EvidenceAnchor
    claimRealization : Claims.ClaimEvidenceRealization
    intendedConsumer : Claims.ClaimConsumer
    liveResidual : Claims.LiveResidual

canonicalGDP15000UpstreamEdge : UpstreamStudyEdge
canonicalGDP15000UpstreamEdge = upstreamStudyEdge
  Sources.kallis2025
  collste2021
  Atlas.gdp15000Owner
  Claims.gdp15000Realization
  Claims.descriptiveSynthesisConsumer
  Claims.associationNotCausation

reviewReferenceIs98 :
  Atlas.EvidenceAnchor.reviewReference
    (UpstreamStudyEdge.reviewAnchor canonicalGDP15000UpstreamEdge) ≡ 98
reviewReferenceIs98 = refl

realizationIsGDP15000Claim :
  Claims.ClaimEvidenceRealization.claim
    (UpstreamStudyEdge.claimRealization canonicalGDP15000UpstreamEdge) ≡
  Claims.gdp15000Claim
realizationIsGDP15000Claim = refl

consumerRemainsDescriptive :
  UpstreamStudyEdge.intendedConsumer canonicalGDP15000UpstreamEdge ≡
  Claims.descriptiveSynthesisConsumer
consumerRemainsDescriptive = refl

residualRemainsAssociationNotCausation :
  UpstreamStudyEdge.liveResidual canonicalGDP15000UpstreamEdge ≡
  Claims.associationNotCausation
residualRemainsAssociationNotCausation = refl

upstreamStudyDoesNotOpenCausalConsumer :
  Claims.AdequateFor Claims.gdp15000Realization Claims.causalMechanismConsumer → ⊥
upstreamStudyDoesNotOpenCausalConsumer =
  Claims.gdp15000ReceiptDoesNotBecomeCausalThreshold

record GDP15000UpstreamBoundary : Set where
  constructor gdp15000UpstreamBoundary
  field
    KallisReviewAuthorsCollsteStudy : Bool
    KallisReviewAuthorsCollsteStudyIsFalse : KallisReviewAuthorsCollsteStudy ≡ false
    upstreamStudyIsExplicitlyBoundToReviewClaim : Bool
    upstreamStudyIsExplicitlyBoundToReviewClaimIsTrue :
      upstreamStudyIsExplicitlyBoundToReviewClaim ≡ true
    observedCrossRegionalPatternIsUniversalCausalThreshold : Bool
    observedCrossRegionalPatternIsUniversalCausalThresholdIsFalse :
      observedCrossRegionalPatternIsUniversalCausalThreshold ≡ false
    descriptiveAdequacyCreatesPolicyMandate : Bool
    descriptiveAdequacyCreatesPolicyMandateIsFalse :
      descriptiveAdequacyCreatesPolicyMandate ≡ false
    upstreamStudyDischargesAssociationResidual : Bool
    upstreamStudyDischargesAssociationResidualIsFalse :
      upstreamStudyDischargesAssociationResidual ≡ false

canonicalGDP15000UpstreamBoundary : GDP15000UpstreamBoundary
canonicalGDP15000UpstreamBoundary =
  gdp15000UpstreamBoundary false refl true refl false refl false refl false refl
