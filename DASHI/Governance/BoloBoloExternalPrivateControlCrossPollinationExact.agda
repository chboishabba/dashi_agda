module DASHI.Governance.BoloBoloExternalPrivateControlCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir
import DASHI.Economics.NvidiaCoreWeaveReflexiveInvestment2026Exact as Financing

------------------------------------------------------------------------
-- EXTERNAL PRIVATE-CONTROL / AUTONOMY CROSS-POLLINATION
--
-- DASHI synthesis over source roles already present in the repository plus a
-- bounded current-literature atlas.  The question is narrower than any claim
-- of common command or conspiracy:
--
--   can an internally non-dominating federation remain dependent on external
--   information/workflow, capital/ownership, or relationship/brokerage
--   channels that constrain its practical option set or contestability?
--
-- Conversely, the existence of any such channel does NOT establish domination
-- unless same-object decision authority / dependency / contestability evidence
-- is separately paid.
--
-- Source-role firewall:
--
--   corporate role != platform capability != deployment authority
--   financing participation != ownership/control != causal governance effect
--   common ownership != one common controller
--   network/relation path != direct influence or proposition inheritance
--   released archive/file != truth of every proposition in the file
--   structural similarity != shared authorship or coordinated command.
------------------------------------------------------------------------

data ExternalSourceRole : Set where
  firstPartyCorporateRole : ExternalSourceRole
  firstPartyPlatformCapability : ExternalSourceRole
  firstPartyCapitalAllocation : ExternalSourceRole
  peerReviewedGovernanceReview : ExternalSourceRole
  peerReviewedGovernanceExperiment : ExternalSourceRole
  officialReleasedArchiveManifest : ExternalSourceRole
  repositoryDerivedSynthesis : ExternalSourceRole

record ExternalControlSource : Set where
  constructor external-control-source
  field
    sourceName : String
    sourceReference : String
    sourceRole : ExternalSourceRole
    boundedSupport : String
    doesNotByItselfSupport : String

open ExternalControlSource public

palantirThielRoleSource : ExternalControlSource
palantirThielRoleSource = external-control-source
  "Palantir Technologies Inc. investor relations"
  "Board of Directors, accessed 2026"
  firstPartyCorporateRole
  "Peter Thiel is a Palantir co-founder and has served as Chairman of its Board since 2003"
  "deployment-specific decision authority, government policy authority, platform abuse, or control over a target governance institution"

palantirCapabilitySource : ExternalControlSource
palantirCapabilitySource = external-control-source
  "Palantir Foundry documentation / repository capability owner"
  "DASHI.Governance.PalantirPlatformCapabilityEvidenceExact"
  firstPartyPlatformCapability
  "generic object/link ontology, operational action layer, granular permissioning and audit-log capabilities"
  "what any named deployment ingests, decides, or permits a subject to inspect, correct or appeal"

nvidiaCapitalPlatformSource : ExternalControlSource
nvidiaCapitalPlatformSource = external-control-source
  "NVIDIA investor relations / repository financing owner"
  "2026-08-10 financing-platform announcement; DASHI.Economics.NvidiaCoreWeaveReflexiveInvestment2026Exact"
  firstPartyCapitalAllocation
  "announced compute-financing platform partnerships including BlackRock and Blackstone among several capital providers, intended to mobilize third-party capital"
  "common control, collusion, fraud, terminal demand, or any target governance decision"

blackstoneInfrastructureSource : ExternalControlSource
blackstoneInfrastructureSource = external-control-source
  "Blackstone Infrastructure"
  "official infrastructure business page, accessed 2026"
  firstPartyCapitalAllocation
  "Blackstone describes itself as an active investor in energy, transport, digital infrastructure, water and waste, including substantial infrastructure assets under management"
  "control of any unrelated institution, political authority, or a measured governance effect"

commonOwnershipReviewSource : ExternalControlSource
commonOwnershipReviewSource = external-control-source
  "Maria Goranova"
  "Common Ownership Research: Implications for Corporate Governance, Corporate Governance: An International Review 33(6), 2025, DOI 10.1111/corg.12657"
  peerReviewedGovernanceReview
  "common-ownership governance effects are an active contested research field spanning activism, accountability, compensation, boards and stakeholder governance"
  "a universal direction of effect, BlackRock-specific causal control, or a common-controller theorem"

bigThreeReviewSource : ExternalControlSource
bigThreeReviewSource = external-control-source
  "Kurt A. Desender et al."
  "From Universal Owners to Owners of the Universe? How the Big Three Are Reshaping Corporate Governance, DOI 10.1111/corg.12611"
  peerReviewedGovernanceReview
  "the concentrated ownership position of BlackRock, Vanguard and State Street creates a governance question whose effects vary across governance dimensions"
  "a finding that the three firms act as one controller or that concentration is uniformly beneficial or harmful"

expectationDocumentExperimentSource : ExternalControlSource
expectationDocumentExperimentSource = external-control-source
  "Ruth V. Aguilera, Vicente J. Bermejo, Javier Capape, Vicente Cunat"
  "The Systemic Governance Influence of Expectation Documents: Evidence from a Universal Owner, Review of Corporate Finance Studies 14(2), 2025, DOI 10.1093/rcfs/cfae009"
  peerReviewedGovernanceExperiment
  "a natural experiment on the Norwegian sovereign wealth fund finds portfolio firms can respond to investor expectation documents; the paper also discusses BlackRock letters as an example of this activism form"
  "a BlackRock-specific treatment-effect estimate or evidence that every asset-manager communication controls investee decisions"

dojEpsteinManifestSource : ExternalControlSource
dojEpsteinManifestSource = external-control-source
  "United States Department of Justice"
  "Epstein Files Transparency Act disclosures / dataset manifests, 2026"
  officialReleasedArchiveManifest
  "official release/file identities and DOJ redaction/privacy context"
  "truth of every statement contained in a released file, direct influence between every related person, culpability, or a universal coordinated network"

canonicalExternalControlSources : List ExternalControlSource
canonicalExternalControlSources =
  palantirThielRoleSource ∷
  palantirCapabilitySource ∷
  nvidiaCapitalPlatformSource ∷
  blackstoneInfrastructureSource ∷
  commonOwnershipReviewSource ∷
  bigThreeReviewSource ∷
  expectationDocumentExperimentSource ∷
  dojEpsteinManifestSource ∷ []

------------------------------------------------------------------------
-- Merged repository-source anchors.
------------------------------------------------------------------------

palantirCapabilityBoundary : Palantir.PalantirCapabilityBoundary
palantirCapabilityBoundary = Palantir.canonicalPalantirCapabilityBoundary

financingCalibration : Financing.VendorCustomerReflexivityCalibration
financingCalibration = Financing.canonicalVendorCustomerReflexivityCalibration

------------------------------------------------------------------------
-- External-autonomy consumer.
--
-- Internal governance and external dependency are distinct consumers.  The
-- codes below are intentionally synthetic; they demonstrate information loss,
-- not an empirical diagnosis of Palantir, Thiel, BlackRock, Blackstone,
-- Epstein, Occupy or bolo'bolo.
------------------------------------------------------------------------

record FederationExternalAutonomyWorld : Set where
  constructor federation-external-autonomy-world
  field
    internalAgendaControlCode : Nat
    internalDelegationControlCode : Nat
    internalReopeningAccessCode : Nat

    informationInfrastructureDependencyCode : Nat
    capitalAllocationDependencyCode : Nat
    ownershipStewardshipExposureCode : Nat
    relationshipBrokerageExposureCode : Nat
    externalContestabilityCode : Nat

open FederationExternalAutonomyWorld public

InternalControlOutcome : Set
InternalControlOutcome = Nat × (Nat × Nat)

ExternalAutonomyOutcome : Set
ExternalAutonomyOutcome = Nat × (Nat × (Nat × (Nat × Nat)))

internalControlObserver : FederationExternalAutonomyWorld → InternalControlOutcome
internalControlObserver world =
  internalAgendaControlCode world ,
  (internalDelegationControlCode world , internalReopeningAccessCode world)

externalAutonomyConsumer : FederationExternalAutonomyWorld → ExternalAutonomyOutcome
externalAutonomyConsumer world =
  informationInfrastructureDependencyCode world ,
  (capitalAllocationDependencyCode world ,
   (ownershipStewardshipExposureCode world ,
    (relationshipBrokerageExposureCode world , externalContestabilityCode world)))

------------------------------------------------------------------------
-- Synthetic collision 1:
-- same internally dispersed/reopenable governance, different external
-- dependency/contestability topology.
------------------------------------------------------------------------

internallySameExternallyIndependent : FederationExternalAutonomyWorld
internallySameExternallyIndependent =
  federation-external-autonomy-world 1 1 1 0 0 0 0 2

internallySameExternallyDependent : FederationExternalAutonomyWorld
internallySameExternallyDependent =
  federation-external-autonomy-world 1 1 1 2 2 2 2 0

sameInternalControlCollision :
  internalControlObserver internallySameExternallyIndependent ≡
  internalControlObserver internallySameExternallyDependent
sameInternalControlCollision = refl

externalAutonomyDiffers :
  externalAutonomyConsumer internallySameExternallyIndependent ≡
  externalAutonomyConsumer internallySameExternallyDependent → ⊥
externalAutonomyDiffers ()

internalControlExternalAutonomyNonDescent :
  Descent.ConsumerNonDescentWitness internalControlObserver externalAutonomyConsumer
internalControlExternalAutonomyNonDescent =
  Descent.consumerNonDescentWitness
    internallySameExternallyIndependent
    internallySameExternallyDependent
    sameInternalControlCollision
    externalAutonomyDiffers

internalControlCannotCertifyExternalAutonomy :
  Descent.ConsumerSufficient internalControlObserver externalAutonomyConsumer → ⊥
internalControlCannotCertifyExternalAutonomy =
  Descent.nonDescentWitnessBlocksSufficiency internalControlExternalAutonomyNonDescent

------------------------------------------------------------------------
-- Consumer-relative minimum information requirement.
------------------------------------------------------------------------

externalAutonomyConsumerIsLeast :
  Descent.LeastSufficientConsumerObserver externalAutonomyConsumer
externalAutonomyConsumerIsLeast =
  Descent.canonicalConsumerObserverIsLeast externalAutonomyConsumer

everyExternalAutonomyAdequateObserverRefinesCanonical :
  ∀ {Surface : Set}
    (observe : FederationExternalAutonomyWorld → Surface) →
  Descent.ConsumerSufficient observe externalAutonomyConsumer →
  Observer.Refines externalAutonomyConsumer observe
everyExternalAutonomyAdequateObserverRefinesCanonical observe sufficient =
  Descent.belowEverySufficient externalAutonomyConsumerIsLeast observe sufficient

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ExternalPrivateControlBoundary : Set where
  constructor external-private-control-boundary
  field
    sourceRolesRemainDistinct : Bool
    palantirGenericCapabilityPaid : Bool
    blackRockBlackstoneFinancingParticipationPaid : Bool
    commonOwnershipEffectsContestedInReviewLiterature : Bool
    releasedArchiveManifestRolePaid : Bool

    internalControlObserverConsumerSufficient : Bool
    externalAutonomyConsumerLeastSufficientPaid : Bool
    targetExternalAutonomyAuditRequired : Bool

    externalChannelEvidencePaysDomination : Bool
    sameActorOrFirmRelationPaysCommonController : Bool
    platformCapabilityPaysDeploymentDecisionAuthority : Bool
    thielCorporateRolePaysDeploymentDecisionAuthority : Bool
    financingParticipationPaysInstitutionalControl : Bool
    ownershipPositionPaysCausalGovernanceEffect : Bool
    networkReachabilityPaysDirectInfluence : Bool
    releasedArtifactPaysClaimTruth : Bool
    sourceAgreementPaysUnifiedCommand : Bool
    externalDependencyAutomaticallyRefutesLocalNonDomination : Bool
    internalNonDominationAutomaticallyPaysExternalAutonomy : Bool

open ExternalPrivateControlBoundary public

canonicalExternalPrivateControlBoundary : ExternalPrivateControlBoundary
canonicalExternalPrivateControlBoundary =
  external-private-control-boundary
    true
    true true true true
    false true true
    false false false false false false false false false false false
