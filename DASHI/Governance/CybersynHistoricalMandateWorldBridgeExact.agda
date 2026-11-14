module DASHI.Governance.CybersynHistoricalMandateWorldBridgeExact where

-- DASHI-original formal extension, 2026-11-12.
-- This is an owner-preserving bridge, NOT proof of actual governance mandate,
-- source admission, policy efficacy, or world-builder integration.
-- Source policy: Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Cyber
import DASHI.Governance.CybersynAuthorityFeedbackExact as Feedback
import DASHI.Governance.MandateBackedAuthorityRoutingExact as Mandate
import DASHI.Economics.HistoryIndexedMarketMechanismOODALoopExact as Market
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Core.TemporalStrandProvenanceBidiExact as Temporal
import DASHI.Core.IntersectionalNonFactorability as NonFactor

-- Action is not authorisation.  Reuse the actual mandate-backed route owner
-- and preserve its scope, recall, and review witnesses.
mandatedRouteOwner :
  Mandate.MandateBackedAdmissibleRoute
    Mandate.demoRouting
    Mandate.demoMandate
    Mandate.demoInterpretation
    Mandate.delegatedResponseSituation
    Mandate.delegatedResponderRoute
mandatedRouteOwner = Mandate.canonicalMandateBackedRoute

mandateRetainsReviewAndRecall :
  Mandate.RouteAuthorityIsDiachronicallyScoped
    Mandate.demoRouting
    Mandate.demoMandate
    Mandate.demoInterpretation
    Mandate.delegatedResponseSituation
    Mandate.delegatedResponderRoute
mandateRetainsReviewAndRecall =
  Mandate.mandateBackedRouteYieldsBoundedAuthority mandatedRouteOwner

-- Reuse historical market-regime control, without asserting that observed
-- behaviour is a stable preference or that a regulator chooses all actions.
marketRuleHistoryBoundary : Market.HistoryIndexedMarketMechanismBoundary
marketRuleHistoryBoundary =
  Market.canonicalHistoryIndexedMarketMechanismBoundary

-- Source-time receipts are append-only and strand-local.
temporalEvidenceBoundary : Temporal.TemporalStrandBoundary
temporalEvidenceBoundary = Temporal.canonicalTemporalStrandBoundary

proofActionBoundary : Loop.ProofExperimentActionLoopBoundary
proofActionBoundary = Loop.canonicalProofExperimentActionLoopBoundary

-- Two histories can produce the same headline but differ in authority and
-- remedy.  No post-processing of a flattened headline can recover the latter.
data Episode : Set where
  consultationOnly : Episode
  communityMandatedRepair : Episode

data Headline : Set where
  publiclyAnnounced : Headline

data AuthorityResult : Set where
  reportWithoutMandate : AuthorityResult
  scopedRecallableRemedy : AuthorityResult

publicHeadline : Episode → Headline
publicHeadline _ = publiclyAnnounced

actualAuthorityResult : Episode → AuthorityResult
actualAuthorityResult consultationOnly = reportWithoutMandate
actualAuthorityResult communityMandatedRepair = scopedRecallableRemedy

sameHeadline :
  publicHeadline consultationOnly ≡
  publicHeadline communityMandatedRepair
sameHeadline = refl

authorityOutcomesDiffer :
  actualAuthorityResult consultationOnly ≡
  actualAuthorityResult communityMandatedRepair → ⊥
authorityOutcomesDiffer ()

headlineCannotDetermineMandate :
  NonFactor.FactorsThrough publicHeadline actualAuthorityResult → ⊥
headlineCannotDetermineMandate =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      consultationOnly communityMandatedRepair
      sameHeadline authorityOutcomesDiffer)

-- Temporal evidence admission must not back-date receipt creation.  This
-- example does not conflate reception of evidence with prior knowledge.
data ReceiptPhase : Set where
  sourceFirstSeen : ReceiptPhase
  independentVerificationLater : ReceiptPhase

data EvidenceAuthority : Set where
  sourceOnly : EvidenceAuthority
  verifiedLater : EvidenceAuthority

receiptAt : ReceiptPhase → EvidenceAuthority
receiptAt sourceFirstSeen = sourceOnly
receiptAt independentVerificationLater = verifiedLater

laterVerificationCannotRewriteEarlierReceipt :
  receiptAt sourceFirstSeen ≡ sourceOnly
laterVerificationCannotRewriteEarlierReceipt = refl

laterReceiptNotAlreadyEarlier :
  receiptAt sourceFirstSeen ≡
  receiptAt independentVerificationLater → ⊥
laterReceiptNotAlreadyEarlier ()

-- A literal join is sound only when both sources explicitly provide the same
-- object identifier.  Merely matching text labels is insufficient.
record SameWorldObject
  (ObjectIdentifier : Set) (left right : ObjectIdentifier) : Set where
  constructor sameWorldObject
  field
    exactObject : left ≡ right

open SameWorldObject public

identityTransport :
  ∀ {ObjectIdentifier : Set} {a b : ObjectIdentifier} →
  SameWorldObject ObjectIdentifier a b →
  (P : ObjectIdentifier → Set) → P a → P b
identityTransport {a = a} {b = b} witness P proof
  with exactObject witness
... | refl = proof

-- No auto-promotion from qualitative state and source receipts to observed
-- market behaviour, legitimate representation, or causal effectiveness.
data SameLabelImpliesAuthorityPermission : Set where

sameLabelCannotManufactureAuthority :
  SameLabelImpliesAuthorityPermission → ⊥
sameLabelCannotManufactureAuthority ()
