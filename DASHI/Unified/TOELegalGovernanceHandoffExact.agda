module DASHI.Unified.TOELegalGovernanceHandoffExact where

------------------------------------------------------------------------
-- TOE LEGAL / GOVERNANCE INVARIANT HANDOFF
--
-- Reuse order:
--   1. SensibLaw semantic promotion policy.
--   2. SensibLaw ITIR parity aggregate.
--   3. Governed legal network strategy.
--   4. Generic claim-audit manifest.
--
-- No Actionstep-specific owner was found in the searched repository graph.
-- This module therefore does not invent one.
--
-- ZKP frame:
--   O observation
--   R risk
--   C control
--   S state
--   L lineage
--   P preconditions
--   G guarantees
--   F failure boundary
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawSemanticPromotionPolicy as Semantic
import DASHI.Law.SensibLawITIRParityEverything as Parity
import DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact as Network
import DASHI.Reasoning.ClaimAuditManifestExact as Audit
import DASHI.Core.AuthorityNonPromotionCore as Authority

record ZKPTOELegalGovernanceHandoff : Set₁ where
  constructor zkpTOELegalGovernanceHandoff
  field
    O-observation : String
    R-risk : String
    C-control : String
    S-state : String
    L-lineage : List String
    P-preconditions : List String
    G-guarantees : List String
    F-failureBoundary : List String

    semanticPolicy : Semantic.SemanticPromotionPolicySurface
    legalRuntime : LegalRuntime.AgdaFirstLegalRuntimeContract
    networkBoundary : Network.GovernedLegalNetworkBoundary
    claimAuditBoundary : Audit.ClaimAuditManifestBoundary

    heuristicOnlyRemainsNeither :
      ∀ heuristic-for heuristic-against target source →
      Semantic.promote
        (Semantic.heuristicCandidate
          heuristic-for heuristic-against target source)
      ≡ Tetralemma.neither

    heuristicBitsCannotChangePromotion :
      ∀ structural-for structural-against
        heuristic-for₁ heuristic-against₁
        heuristic-for₂ heuristic-against₂
        target source →
      Semantic.promote
        (Semantic.mixedCandidate
          structural-for structural-against
          heuristic-for₁ heuristic-against₁
          target source)
      ≡
      Semantic.promote
        (Semantic.mixedCandidate
          structural-for structural-against
          heuristic-for₂ heuristic-against₂
          target source)

    semanticGateDoesNotPromoteAuthority :
      Authority.promotesAnyAuthority
        Semantic.semanticPromotionAuthorityBoundary
      ≡ false

    governedNetworkRequiresGovernance :
      Network.GovernedLegalNetworkBoundary.liveAccessRequiresGovernance
        networkBoundary
      ≡ true

    governedNetworkForbidsCrawling :
      Network.GovernedLegalNetworkBoundary.crawlingPermitted
        networkBoundary
      ≡ false

    parserCannotRunBeforeLocalIngestion :
      Network.GovernedLegalNetworkBoundary.parserMayRunBeforeLocalIngestion
        networkBoundary
      ≡ false

    auditStageDoesNotEqualTruthStatus :
      Audit.ClaimAuditManifestBoundary.auditStageEqualsTruthStatus
        claimAuditBoundary
      ≡ false

    constructDoesNotEqualApplication :
      Audit.ClaimAuditManifestBoundary.constructEqualsApplication
        claimAuditBoundary
      ≡ false

    partialCoverageDoesNotEqualWholeClaim :
      Audit.ClaimAuditManifestBoundary.partialObligationCoverageEqualsWholeClaimSupport
        claimAuditBoundary
      ≡ false

    actionstepSpecificOwnerResolved : Bool
    actionstepSpecificOwnerResolvedIsFalse :
      actionstepSpecificOwnerResolved ≡ false

open ZKPTOELegalGovernanceHandoff public

canonicalZKPTOELegalGovernanceHandoff :
  ZKPTOELegalGovernanceHandoff
canonicalZKPTOELegalGovernanceHandoff =
  zkpTOELegalGovernanceHandoff
    "SensibLaw structural evidence, ITIR parity, governed legal acquisition, and claim-audit state enter one TOE handoff."
    "Heuristic evidence, network convenience, citation match, or local construct support may be promoted into legal or truth authority."
    "Use structural-only promotion, closed authority boundaries, governed network execution, and typed claim-audit receipts."
    "The current legal/governance lane is integrated but fail-closed for unsupported authority promotion."
    ( "DASHI.Interop.SensibLawSemanticPromotionPolicy"
    ∷ "DASHI.Law.SensibLawITIRParityEverything"
    ∷ "DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact"
    ∷ "DASHI.Reasoning.ClaimAuditManifestExact"
    ∷ [] )
    ( "Typed structural evidence must exist before semantic promotion."
    ∷ "The legal runtime contract must remain the canonical Agda-first owner."
    ∷ "Live legal acquisition must use the governed network boundary."
    ∷ "Claim scope and receipt kind must remain explicit."
    ∷ [] )
    ( "Heuristic-only evidence promotes to neither."
    ∷ "Heuristic bit changes do not alter canonical promotion."
    ∷ "The semantic gate does not confer authority."
    ∷ "Crawling remains forbidden."
    ∷ "Parsing follows local ingestion."
    ∷ "Audit maturity is not truth status."
    ∷ "Partial obligation coverage is not whole-claim support."
    ∷ [] )
    ( "No Actionstep-specific owner was found by repository search, so no Actionstep equivalence or authority claim is introduced."
    ∷ "No ESD surface is edited or used as an ownership source."
    ∷ "No cross-domain analogy upgrades legal authority."
    ∷ [] )
    Semantic.semanticPromotionPolicySurface
    Parity.selectedLegalRuntimeContract
    Network.canonicalGovernedLegalNetworkBoundary
    Audit.canonicalClaimAuditManifestBoundary
    Semantic.heuristic-only-abstains
    Semantic.promotion-ignores-heuristic-bits
    Semantic.semantic-promotion-all-authority-closed
    Network.GovernedLegalNetworkBoundary.liveAccessRequiresGovernanceIsTrue
      Network.canonicalGovernedLegalNetworkBoundary
    Network.GovernedLegalNetworkBoundary.crawlingPermittedIsFalse
      Network.canonicalGovernedLegalNetworkBoundary
    Network.GovernedLegalNetworkBoundary.parserMayRunBeforeLocalIngestionIsFalse
      Network.canonicalGovernedLegalNetworkBoundary
    refl
    refl
    refl
    false
    refl

toeLegalGovernancePostcondition :
  Authority.promotesAnyAuthority
    Semantic.semanticPromotionAuthorityBoundary
  ≡ false
toeLegalGovernancePostcondition =
  semanticGateDoesNotPromoteAuthority
    canonicalZKPTOELegalGovernanceHandoff

toeLegalGovernanceNetworkPostcondition :
  Network.GovernedLegalNetworkBoundary.crawlingPermitted
    (networkBoundary canonicalZKPTOELegalGovernanceHandoff)
  ≡ false
toeLegalGovernanceNetworkPostcondition =
  governedNetworkForbidsCrawling
    canonicalZKPTOELegalGovernanceHandoff

toeLegalGovernanceAuditPostcondition :
  Audit.ClaimAuditManifestBoundary.partialObligationCoverageEqualsWholeClaimSupport
    (claimAuditBoundary canonicalZKPTOELegalGovernanceHandoff)
  ≡ false
toeLegalGovernanceAuditPostcondition =
  partialCoverageDoesNotEqualWholeClaim
    canonicalZKPTOELegalGovernanceHandoff
