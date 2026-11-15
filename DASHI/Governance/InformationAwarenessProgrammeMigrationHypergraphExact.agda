module DASHI.Governance.InformationAwarenessProgrammeMigrationHypergraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Governance.TIAComponentDispositionAtlasExact as Disposition
import DASHI.Governance.WadeRoleChronologyExact as Wade
import DASHI.Governance.PalantirEarlyIntelDevelopmentChronologyExact as Early
import DASHI.Governance.PalantirTIAHistoricalGenealogyExact as Genealogy
import DASHI.Biology.CausalIdentificationFamiliesExact as Causal

------------------------------------------------------------------------
-- INFORMATION-AWARENESS PROGRAMME MIGRATION HYPERGRAPH
------------------------------------------------------------------------

data NodeKind : Set where
  publicProgramme : NodeKind
  intelligenceProgramme : NodeKind
  intelligenceAgency : NodeKind
  ventureInterface : NodeKind
  privateVendor : NodeKind
  technicalCapability : NodeKind
  personRole : NodeKind

data MigrationRelation : Set where
  statutoryContinuation : MigrationRelation
  personnelContinuity : MigrationRelation
  capitalAccess : MigrationRelation
  customerAccess : MigrationRelation
  technicalFeedback : MigrationRelation
  capabilitySimilarity : MigrationRelation
  exactAssetTransfer : MigrationRelation
  exactRequirementTransfer : MigrationRelation
  exactContractContinuity : MigrationRelation
  exactDecisionAuthorityContinuity : MigrationRelation

data EdgePayment : Set where
  strongPaid : EdgePayment
  boundedSecondary : EdgePayment
  hypothesisOnly : EdgePayment
  unpaidRequired : EdgePayment

record MigrationEdge : Set where
  constructor migration-edge
  field
    fromNode : String
    toNode : String
    relation : MigrationRelation
    payment : EdgePayment
    sourceOwner : String
    sameObject : Bool
    boundedReading : String

open MigrationEdge public

publicTIAtoNFIPTools : MigrationEdge
publicTIAtoNFIPTools = migration-edge
  "DARPA TIA public umbrella"
  "NFIP processing/analysis/collaboration tools exception"
  statutoryContinuation strongPaid
  "TIAComponentDispositionAtlasExact"
  false
  "Congress pays a continuation category under a statutory exception, but the classified-annex programme/component identity is not public in the acquired record."

inQTelToPalantir : MigrationEdge
inQTelToPalantir = migration-edge
  "In-Q-Tel" "Palantir" capitalAccess strongPaid
  "PalantirTIAHistoricalGenealogyExact / PalantirEarlyIntelDevelopmentChronologyExact"
  true
  "investment/portfolio and intelligence-community entry are supported; this does not pay TIA programme identity."

ciaAnalystsToPalantir : MigrationEdge
ciaAnalystsToPalantir = migration-edge
  "CIA/intelligence analysts" "Palantir early product" technicalFeedback strongPaid
  "PalantirTIAHistoricalGenealogyExact / PalantirEarlyIntelDevelopmentChronologyExact"
  true
  "iterative analyst feedback/refinement is supported by independent histories; no TIA asset/code transfer follows."

palantirToNCTCCandidate : MigrationEdge
palantirToNCTCCandidate = migration-edge
  "Palantir prototype" "NCTC live databases" customerAccess boundedSecondary
  "PalantirEarlyIntelDevelopmentChronologyExact"
  true
  "RAND secondary chronology reports a live-database beta; exact primary beta artefact and authorization remain acquisition targets."

wadeToTIAcandidate : MigrationEdge
wadeToTIAcandidate = migration-edge
  "Alan Wade" "TIA/IAO participation" personnelContinuity hypothesisOnly
  "WadeRoleChronologyExact"
  false
  "official CIA/IC CIO role is paid, but the same-person TIA assignment remains secondary-claim only."

tiaToPalantirAssetTransfer : MigrationEdge
tiaToPalantirAssetTransfer = migration-edge
  "TIA/IAO assets or code" "Palantir" exactAssetTransfer unpaidRequired
  "PrivatizedTIAPromotionReceipt"
  false
  "no same-object asset/code transfer receipt acquired."

tiaToPalantirRequirementTransfer : MigrationEdge
tiaToPalantirRequirementTransfer = migration-edge
  "TIA/IAO programme requirements" "Palantir" exactRequirementTransfer unpaidRequired
  "terminal acquisition frontier"
  false
  "functional resemblance and customer feedback do not identify transferred requirements."

palantirContractContinuity : MigrationEdge
palantirContractContinuity = migration-edge
  "TIA/NFIP programme contract scope" "Palantir government contract scope" exactContractContinuity unpaidRequired
  "terminal acquisition frontier"
  false
  "same-object procurement continuity remains unpaid."

migrationEdges : List MigrationEdge
migrationEdges =
  publicTIAtoNFIPTools ∷ inQTelToPalantir ∷ ciaAnalystsToPalantir ∷
  palantirToNCTCCandidate ∷ wadeToTIAcandidate ∷ tiaToPalantirAssetTransfer ∷
  tiaToPalantirRequirementTransfer ∷ palantirContractContinuity ∷ []

------------------------------------------------------------------------
-- Multi-dimensional promotion lattice.
------------------------------------------------------------------------

data SynthesisStatus : Set where
  documentedContactAndCapabilityContinuity : SynthesisStatus
  capabilityMigrationHypothesis : SynthesisStatus
  documentedInstitutionalReconstitution : SynthesisStatus
  documentedProgrammeSuccession : SynthesisStatus

currentStatus : SynthesisStatus
currentStatus = capabilityMigrationHypothesis

capabilityMigrationHypothesisLive : Bool
capabilityMigrationHypothesisLive = true

programmeReconstitutionPromoted : Bool
programmeReconstitutionPromoted = false

programmeSuccessionPromoted : Bool
programmeSuccessionPromoted = false

networkPathCreatesDirectTransfer : Bool
networkPathCreatesDirectTransfer = false

sharedCapabilityCreatesProgrammeIdentity : Bool
sharedCapabilityCreatesProgrammeIdentity = false

benefitCreatesMotive : Bool
benefitCreatesMotive = false

allFivePrivatizationCoordinatesPaid : Bool
allFivePrivatizationCoordinatesPaid = Genealogy.promotionReady Genealogy.currentPromotionReceipt

allFivePrivatizationCoordinatesRemainUnpaid :
  allFivePrivatizationCoordinatesPaid ≡ false
allFivePrivatizationCoordinatesRemainUnpaid = refl

------------------------------------------------------------------------
-- Causal-identification cross-pollination.
------------------------------------------------------------------------

causalIdentificationFamilyAvailable : Set
causalIdentificationFamilyAvailable = Causal.CausalIdentificationFamily

causalEffectPromotedFromChronology : Bool
causalEffectPromotedFromChronology = false

causalEffectPromotedFromNetworkReachability : Bool
causalEffectPromotedFromNetworkReachability = false

------------------------------------------------------------------------
-- Honest terminal boundary for this evidence tranche.
------------------------------------------------------------------------

record MigrationBoundary : Set where
  constructor migration-boundary
  field
    publicContinuationCategoryProvesPrivateSuccessor : Bool
    ciaDevelopmentRelationshipProvesTIAInheritance : Bool
    wadeICCIOProvesTIAParticipation : Bool
    multiHopReachabilityProvesDirectTransfer : Bool
    capabilityMigrationMayRemainLiveWithoutSuccession : Bool
    chronologyCreatesCausalIdentification : Bool

canonicalMigrationBoundary : MigrationBoundary
canonicalMigrationBoundary = migration-boundary false false false false true false
