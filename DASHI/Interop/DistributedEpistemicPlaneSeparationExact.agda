module DASHI.Interop.DistributedEpistemicPlaneSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawFederatedZOSAcquisitionExact as Federated
import DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact as Sources

------------------------------------------------------------------------
-- DISTRIBUTED EPISTEMIC PLANE SEPARATION
--
-- Architecture composition: Johl Brown discussion-origin proposal.
-- JMD/meta-introspector and external projects provide attributed implementation
-- precedents through DistributedEpistemicFabricSourceAtlasExact.
-- The typed decomposition and empty-type firewalls below are DASHI synthesis.
------------------------------------------------------------------------

data EpistemicPlane : Set where
  artifactPlane : EpistemicPlane
  historyPlane : EpistemicPlane
  projectionPlane : EpistemicPlane
  situatedAccessPlane : EpistemicPlane
  contractPlane : EpistemicPlane
  proofSearchPlane : EpistemicPlane
  admissionPlane : EpistemicPlane
  settlementPlane : EpistemicPlane

data FabricEvent : Set where
  sourceObserved : FabricEvent
  sourceRevisionSeen : FabricEvent
  residualRaised : FabricEvent
  proofRequested : FabricEvent
  proofReturned : FabricEvent
  promotionProposed : FabricEvent
  promotionAccepted : FabricEvent
  promotionRejected : FabricEvent
  accessPathCreated : FabricEvent
  contractQuoted : FabricEvent
  contractAuthorized : FabricEvent
  resourceProvisioned : FabricEvent
  deliveryObserved : FabricEvent
  measurementObserved : FabricEvent
  settlementCommitted : FabricEvent

record TechnologyRoleMap : Set where
  constructor technologyRoleMap
  field
    artifactRole : String
    replicatedHistoryRole : String
    transportRole : String
    operationalProjectionRole : String
    proofProducerRole : String
    semanticAdmissionRole : String
    settlementRole : String
    orbitDbCurrentlyDeployed : Bool
    orbitDbCurrentlyDeployedIsFalse : orbitDbCurrentlyDeployed ≡ false
    solanaIsApplicationDatabase : Bool
    solanaIsApplicationDatabaseIsFalse : solanaIsApplicationDatabase ≡ false
    settlementCreatesTruth : Bool
    settlementCreatesTruthIsFalse : settlementCreatesTruth ≡ false
    postgresIsGlobalSemanticTruth : Bool
    postgresIsGlobalSemanticTruthIsFalse : postgresIsGlobalSemanticTruth ≡ false

open TechnologyRoleMap public

canonicalTechnologyRoleMap : TechnologyRoleMap
canonicalTechnologyRoleMap =
  technologyRoleMap
    "IPFS / DASL / eRDFa: immutable or content-addressed artifact identity/publication precedents"
    "OrbitDB: external replicated authenticated log plus materialized-projection precedent; not asserted deployed here"
    "JMD mesh-sync-rs / ZOS: synchronization, reconciliation and recovery precedents; transport is not semantic authority"
    "SLR/Postgres/local indexes/UI: consumer-relative operational materializations"
    "Lean/wiki-prover and other checkers: bounded executable proof/search/check producers"
    "Agda/DASHI: semantic interpretation, admission contracts and non-collapse laws"
    "SOLFUNMEME/Solana: optional scarce/global settlement, governance or value commitment"
    false refl
    false refl
    false refl
    false refl

sourceAtlas : Sources.ContributionAttribution
sourceAtlas = Sources.johlDiscussionContribution

-- Reuse the already-canonical federated CID/content boundary instead of making
-- a second content-addressing authority ontology.
federatedContentBoundary : Federated.FederatedContentBoundary
federatedContentBoundary = Federated.canonicalFederatedContentBoundary

------------------------------------------------------------------------
-- Cross-plane firewalls.
------------------------------------------------------------------------

data CIDCreatesAuthority : Set where
data ReplicatedEventCreatesTruth : Set where
data ProjectionStatusCreatesKernelProof : Set where
data KernelReceiptCreatesAdmission : Set where
data EffectiveAccessCreatesClaimTruth : Set where
data ContractCreatesSemanticAuthority : Set where
data SettlementCreatesEpistemicTruth : Set where
data PostgresProjectionIsGlobalTruth : Set where
data TransportArrivalCreatesPromotion : Set where

cidIsNotAuthority : CIDCreatesAuthority → ⊥
cidIsNotAuthority ()

replicatedEventIsNotTruth : ReplicatedEventCreatesTruth → ⊥
replicatedEventIsNotTruth ()

projectionStatusIsNotKernelProof : ProjectionStatusCreatesKernelProof → ⊥
projectionStatusIsNotKernelProof ()

kernelReceiptIsNotAdmission : KernelReceiptCreatesAdmission → ⊥
kernelReceiptIsNotAdmission ()

effectiveAccessIsNotClaimTruth : EffectiveAccessCreatesClaimTruth → ⊥
effectiveAccessIsNotClaimTruth ()

contractIsNotSemanticAuthority : ContractCreatesSemanticAuthority → ⊥
contractIsNotSemanticAuthority ()

settlementIsNotEpistemicTruth : SettlementCreatesEpistemicTruth → ⊥
settlementIsNotEpistemicTruth ()

postgresProjectionIsNotGlobalTruth : PostgresProjectionIsGlobalTruth → ⊥
postgresProjectionIsNotGlobalTruth ()

transportArrivalIsNotPromotion : TransportArrivalCreatesPromotion → ⊥
transportArrivalIsNotPromotion ()

------------------------------------------------------------------------
-- Explicit eight-plane canonical path. This is an architecture coordinate,
-- not an implication chain: every boundary remains separately witnessed.
------------------------------------------------------------------------

canonicalPlanePath : List EpistemicPlane
canonicalPlanePath =
  artifactPlane ∷ historyPlane ∷ projectionPlane ∷ situatedAccessPlane ∷
  contractPlane ∷ proofSearchPlane ∷ admissionPlane ∷ settlementPlane ∷ []
