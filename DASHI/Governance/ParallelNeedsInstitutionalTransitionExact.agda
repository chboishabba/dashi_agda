{-# OPTIONS --safe #-}
module DASHI.Governance.ParallelNeedsInstitutionalTransitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Education.CommunityConnectednessTopologyExact as Connection
import DASHI.Governance.LocalGlobalCouncilGluing as Council
import DASHI.Governance.RevolutionaryPracticeBraid as Practice

------------------------------------------------------------------------
-- A user-supplied Instagram SRT proposes this sequence:
-- business service -> capabilities -> wellness/solidarity institution ->
-- needs infrastructure -> federated parallel institutions.
--
-- This module formalises the CONDITIONAL stage grammar, rather than
-- claiming that any stage or real-world transition has occurred.
-- The social/political strategy is attributed to the supplied reel;
-- mathematical definitions, counterexample and proof terms are DASHI's.
------------------------------------------------------------------------

reelSource : Source.AttributedSource
reelSource = Source.mkNoDOISource
  "Instagram account label supplied by user: I will help you run your business; speaker not independently established"
  "Reel DfFvTOlAMCq: commercial services to parallel needs infrastructure"
  "Instagram reel; user-supplied SRT transcript dated 2026-10-30"
  "publication date not verified"
  "https://www.instagram.com/reel/DfFvTOlAMCq/"
  Source.communitySource
  "proposed institutional sequence; no outcome, causation, legitimacy or universality is certified"
  Source.publicAttribution

------------------------------------------------------------------------
-- Typed stages.  The speaker's metaphors are not identities or proofs.
------------------------------------------------------------------------

data InstitutionalStage : Set where
  commercialService : InstitutionalStage
  accumulatedCapability : InstitutionalStage
  communityInstitution : InstitutionalStage
  needsInfrastructure : InstitutionalStage
  federatedParallelProvision : InstitutionalStage

record CommercialCapabilityReceipt : Set where
  field
    actualService : Bool
    sustainableSurplus : Bool
    transferableCapability : Bool
    actualServiceVerified : actualService ≡ true
    surplusVerified : sustainableSurplus ≡ true
    capabilityVerified : transferableCapability ≡ true

record CommunityInstitutionReceipt : Set where
  field
    voluntaryMembership : Bool
    accountableGovernance : Bool
    transparentPurpose : Bool
    membershipVerified : voluntaryMembership ≡ true
    governanceVerified : accountableGovernance ≡ true
    transparencyVerified : transparentPurpose ≡ true

record ProvisionReceipt : Set where
  field
    materialDelivery : Bool
    reachableAccess : Bool
    durableResourcing : Bool
    deliveryVerified : materialDelivery ≡ true
    accessVerified : reachableAccess ≡ true
    resourcingVerified : durableResourcing ≡ true

record FederationReceipt : Set where
  field
    localAutonomy : Bool
    compatibleCoordination : Bool
    meaningfulExit : Bool
    autonomyVerified : localAutonomy ≡ true
    coordinationVerified : compatibleCoordination ≡ true
    exitVerified : meaningfulExit ≡ true

-- Evidence-bearing transitions are constructors, not empirical assertions.
data AdmissibleTransition : InstitutionalStage → InstitutionalStage → Set where
  capacityFromService :
    CommercialCapabilityReceipt →
    AdmissibleTransition commercialService accumulatedCapability
  institutionFromCapacity :
    CommunityInstitutionReceipt →
    AdmissibleTransition accumulatedCapability communityInstitution
  infrastructureFromInstitution :
    ProvisionReceipt →
    AdmissibleTransition communityInstitution needsInfrastructure
  federationFromInfrastructure :
    FederationReceipt →
    AdmissibleTransition needsInfrastructure federatedParallelProvision

-- Standard reflexive/transitive closure of the evidenced step relation.
data TransitionPath : InstitutionalStage → InstitutionalStage → Set where
  stay : ∀ {s} → TransitionPath s s
  advance : ∀ {s t u} →
    AdmissibleTransition s t →
    TransitionPath t u →
    TransitionPath s u

conditionalCommercialToFederation :
  CommercialCapabilityReceipt →
  CommunityInstitutionReceipt →
  ProvisionReceipt →
  FederationReceipt →
  TransitionPath commercialService federatedParallelProvision
conditionalCommercialToFederation c i p f =
  advance (capacityFromService c)
    (advance (institutionFromCapacity i)
      (advance (infrastructureFromInstitution p)
        (advance (federationFromInfrastructure f) stay)))

------------------------------------------------------------------------
-- Nonfactorability: generating revenue cannot by itself determine whether
-- essential needs are really provisioned. Two finite abstract situations
-- share the exact revenue projection while differing in delivery.
------------------------------------------------------------------------

record InstitutionalOutcome : Set where
  constructor institutionalOutcome
  field
    commercialRevenuePresent : Bool
    needsActuallyProvided : Bool
    accessActuallyReachable : Bool
    governedByAffectedPeople : Bool

open InstitutionalOutcome public

revenueWithoutProvision : InstitutionalOutcome
revenueWithoutProvision = institutionalOutcome true false false false

revenueWithProvision : InstitutionalOutcome
revenueWithProvision = institutionalOutcome true true true true

revenueProjection : InstitutionalOutcome → Bool
revenueProjection = commercialRevenuePresent

provisionProjection : InstitutionalOutcome → Bool
provisionProjection = needsActuallyProvided

sameRevenue :
  revenueProjection revenueWithoutProvision
  ≡ revenueProjection revenueWithProvision
sameRevenue = refl

differentProvision :
  provisionProjection revenueWithoutProvision
  ≡ provisionProjection revenueWithProvision → ⊥
differentProvision ()

revenueDoesNotFactorProvisionWitness :
  NonFactor.NonFactorabilityWitness revenueProjection provisionProjection
revenueDoesNotFactorProvisionWitness =
  NonFactor.nonFactorabilityWitness
    revenueWithoutProvision revenueWithProvision
    sameRevenue differentProvision

revenueCannotDetermineNeedsProvision :
  NonFactor.FactorsThrough revenueProjection provisionProjection → ⊥
revenueCannotDetermineNeedsProvision =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    revenueDoesNotFactorProvisionWitness

-- Reuse the already proven distinctions:
-- formal membership != effective connection != independent authority.
formalMembershipCannotGuaranteeEffectiveConnection :
  NonFactor.FactorsThrough
    Connection.formalProjection Connection.effectiveProjection → ⊥
formalMembershipCannotGuaranteeEffectiveConnection =
  Connection.formalConnectionCannotDetermineEffectiveConnection

effectiveConnectionCannotConferAuthority :
  NonFactor.FactorsThrough
    Connection.effectiveProjection Connection.authorityProjection → ⊥
effectiveConnectionCannotConferAuthority =
  Connection.effectiveConnectionCannotDetermineAuthority

-- Local-to-global compatibility is a distinct existing obligation;
-- a plurality of service clubs does not magically glue into a federation.
federationCompatibilityObligation :
  (locals : Council.CouncilBasePoint → Council.LocalCouncilSection) → Set
federationCompatibilityObligation locals = Council.CompatibleCouncilFamily locals

-- The source's practice examples are already represented by the governance
-- braid; no redundant political or ethical ontology is constructed here.
prefigurativePracticeReference : List Practice.PrefigurativePractice
prefigurativePracticeReference = Practice.canonicalPrefigurativePractices

------------------------------------------------------------------------
-- Fail-closed epistemic boundary.  These flags describe the transcript
-- carrier and the scope of this formalisation, not historical outcomes.
------------------------------------------------------------------------

record SourceBoundary : Set where
  constructor sourceBoundary
  field
    transcriptDescribesProposedSequence : Bool
    reelIndependentlyViewed : Bool
    economicFeasibilityEstablished : Bool
    actualNeedsCoverageEstablished : Bool
    politicalOrReligiousAuthorityCreated : Bool
    sequenceIsProposal : transcriptDescribesProposedSequence ≡ true
    noDirectReelObservation : reelIndependentlyViewed ≡ false
    noFeasibilityPromotion : economicFeasibilityEstablished ≡ false
    noCoveragePromotion : actualNeedsCoverageEstablished ≡ false
    noAuthorityPromotion : politicalOrReligiousAuthorityCreated ≡ false

canonicalBoundary : SourceBoundary
canonicalBoundary = sourceBoundary
  true false false false false refl refl refl refl refl
