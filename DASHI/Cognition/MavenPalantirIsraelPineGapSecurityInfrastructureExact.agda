module DASHI.Cognition.MavenPalantirIsraelPineGapSecurityInfrastructureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import DASHI.Physics.Foundations.CabarlahPalestineSourceAtlas as PineGap

record SecurityInfrastructureBoundary : Set where
  constructor security-infrastructure-boundary
  field
    googleMavenParticipationPaid : Bool
    workerDissentContributedToNonRenewalPaid : Bool
    whittakerMavenOrganisingPaid : Bool
    whittakerLaterSignalPresidentPaid : Bool
    palantirMavenContinuityPaid : Bool
    palantir2024Maven480mPaid : Bool
    palantirIsraelWarPartnershipPaid : Bool
    pineGapMiddleEastTargetingSupportCapabilityPaid : Bool
    pineGapSpecificTargetAttributionUniversallyPaid : Bool
    publicProIsraelLobbyingAndElectionSpendingPaid : Bool
    lobbyingImpliesVendorSelection : Bool
    infrastructureContinuityImpliesHiddenUnifiedCommand : Bool
    amalekRhetoricUsePaid : Bool
    amalekRhetoricAloneProvesOperationalCommand : Bool
open SecurityInfrastructureBoundary public

canonicalSecurityInfrastructureBoundary : SecurityInfrastructureBoundary
canonicalSecurityInfrastructureBoundary = security-infrastructure-boundary
  true true true true true true true true false true false false true false

record InfrastructureReceipt : Set where
  constructor infrastructure-receipt
  field
    source : String
    boundedFinding : String
    relationPaid : Bool
    hiddenCoordinationPaid : Bool
open InfrastructureReceipt public

mavenGoogleReceipt : InfrastructureReceipt
mavenGoogleReceipt = infrastructure-receipt
  "Reuters 2018; Google SEC disclosure; Meredith Whittaker interviews"
  "Google worked on Project Maven; employee opposition helped produce a decision not to renew. Meredith Whittaker helped draft the anti-Maven petition and later became Signal president."
  true false

palantirMavenReceipt : InfrastructureReceipt
palantirMavenReceipt = infrastructure-receipt
  "US Department of Defense contract announcement, 2024-05-29"
  "Palantir USG received a $480m firm-fixed-price Maven Smart System prototype contract through May 2029."
  true false

palantirIsraelReceipt : InfrastructureReceipt
palantirIsraelReceipt = infrastructure-receipt
  "Bloomberg 2024; Palantir public materials"
  "Palantir and Israel's Defense Ministry announced a strategic partnership to support war-related missions after senior Palantir leadership met Israeli defense officials."
  true false

pineGapReceipt : InfrastructureReceipt
pineGapReceipt = infrastructure-receipt
  "ABC 2024-2026; existing Cabarlah/Palestine source atlas"
  "Pine Gap has Middle-East SIGINT and targeting-chain capability and experts assess its data feeds US military operations and can be shared onward with Israel; exact target-level use remains difficult to prove publicly."
  true false

lobbyReceipt : InfrastructureReceipt
lobbyReceipt = infrastructure-receipt
  "FEC/OpenSecrets/Reuters AIPAC and United Democracy Project records"
  "AIPAC and its affiliated electoral infrastructure spend substantial disclosed sums on lobbying and congressional elections in support of pro-Israel policy. This pays political influence capacity, not secret command over vendors, agencies or every officeholder."
  true false

amalekReceipt : InfrastructureReceipt
amalekReceipt = infrastructure-receipt
  "ICJ South Africa v Israel application citing Netanyahu's October/November 2023 Amalek references; existing repo Amalek provenance owners"
  "Contemporary Israeli leadership's invocation of Amalek is source-paid as rhetoric and is relevant to the repo's authority-projection/terminalisation analysis. It is not by itself proof of a hidden operational command architecture."
  true false

data CapabilityImpliesUse : Set where
data PublicIdeologyImpliesSecretCoordination : Set where
data LobbyingImpliesProcurementSelection : Set where
data ContractorContinuityImpliesSingleCommand : Set where
data PineGapCapabilityImpliesEveryStrike : Set where
data AmalekRhetoricImpliesEveryOperationalDecision : Set where

capabilityDoesNotCreateUse : CapabilityImpliesUse → ⊥
capabilityDoesNotCreateUse ()

ideologyDoesNotCreateSecretCoordination : PublicIdeologyImpliesSecretCoordination → ⊥
ideologyDoesNotCreateSecretCoordination ()

lobbyingDoesNotCreateProcurementSelection : LobbyingImpliesProcurementSelection → ⊥
lobbyingDoesNotCreateProcurementSelection ()

continuityDoesNotCreateSingleCommand : ContractorContinuityImpliesSingleCommand → ⊥
continuityDoesNotCreateSingleCommand ()

pineGapCapabilityDoesNotCreateEveryStrike : PineGapCapabilityImpliesEveryStrike → ⊥
pineGapCapabilityDoesNotCreateEveryStrike ()

amalekRhetoricDoesNotCreateEveryDecision : AmalekRhetoricImpliesEveryOperationalDecision → ⊥
amalekRhetoricDoesNotCreateEveryDecision ()
