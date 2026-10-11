module DASHI.Governance.BoloBoloGovernanceMetricProvenanceExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.NumberRoleProvenanceAtlasExact as NumberAtlas

------------------------------------------------------------------------
-- GOVERNANCE METRIC / ROLE PROVENANCE FIREWALL.
--
-- Cross-pollination source:
-- `NumberRoleProvenanceAtlasExact` establishes a repo-wide methodological
-- discipline: equal printed numbers do not identify the semantic role in which
-- they occur.  The governance-specific role vocabulary below is a DASHI
-- construction and is not attributed back to that donor module's historical or
-- mathematical sources.
--
-- This owner protects the bolo'bolo calibration lane from silently equating,
-- for example, 120 minutes of meeting duration with 120 units of interface
-- capacity or a threshold whose underlying `Nat` happens to be the same.
------------------------------------------------------------------------

data GovernanceMetricRole : Set where
  sourceScalePopulation : GovernanceMetricRole
  observedDurationMinutes : GovernanceMetricRole
  councilPersonMinutes : GovernanceMetricRole
  participantCount : GovernanceMetricRole
  incidenceEdgeCount : GovernanceMetricRole
  costComponent : GovernanceMetricRole
  costWeight : GovernanceMetricRole
  meaningfulThreshold : GovernanceMetricRole
  interfaceCapacity : GovernanceMetricRole
  peakBoundaryDemand : GovernanceMetricRole
  backlogCount : GovernanceMetricRole
  realisedCrossGroupChannelCount : GovernanceMetricRole

record GovernanceMetricReceipt : Set where
  constructor governanceMetricReceipt
  field
    scalarValue : Nat
    metricRole : GovernanceMetricRole
    unitLabel : String
    provenance : String

open GovernanceMetricReceipt public

------------------------------------------------------------------------
-- Exact same-scalar / different-role witness.
------------------------------------------------------------------------

duration120 : GovernanceMetricReceipt
duration120 =
  governanceMetricReceipt
    120
    observedDurationMinutes
    "minutes"
    "DASHI finite witness: duration-role example"

capacity120 : GovernanceMetricReceipt
capacity120 =
  governanceMetricReceipt
    120
    interfaceCapacity
    "declared coordination-capacity units"
    "DASHI finite witness: interface-capacity-role example"

sameUnderlyingScalar : scalarValue duration120 ≡ scalarValue capacity120
sameUnderlyingScalar = refl

durationRoleDistinctFromCapacityRole :
  metricRole duration120 ≡ metricRole capacity120 → ⊥
durationRoleDistinctFromCapacityRole ()

meaningfulThresholdRoleDistinctFromCostWeightRole :
  meaningfulThreshold ≡ costWeight → ⊥
meaningfulThresholdRoleDistinctFromCostWeightRole ()

incidenceRoleDistinctFromParticipantRole :
  incidenceEdgeCount ≡ participantCount → ⊥
incidenceRoleDistinctFromParticipantRole ()

------------------------------------------------------------------------
-- The imported repo atlas is retained as an explicit methodological donor.
-- Its concrete number roles are not reinterpreted as governance metrics.
------------------------------------------------------------------------

repoNumberRoleDonorWitness : NumberAtlas.NumberRole
repoNumberRoleDonorWitness = NumberAtlas.branchingCriticalAvailability

record GovernanceMetricProvenanceBoundary : Set where
  constructor governanceMetricProvenanceBoundary
  field
    sameNatImpliesSameMetricRole : Bool
    unitLabelMayBeDropped : Bool
    provenanceMayBeDropped : Bool
    comparatorMetricAutomaticallyTransfersToTarget : Bool
    targetThresholdMayBeChosenAfterOutcome : Bool
    numberRoleAtlasReusedAsMethodologicalDonor : Bool
    governanceRoleConstructorsAttributedToNumberAtlas : Bool

open GovernanceMetricProvenanceBoundary public

canonicalGovernanceMetricProvenanceBoundary : GovernanceMetricProvenanceBoundary
canonicalGovernanceMetricProvenanceBoundary =
  governanceMetricProvenanceBoundary
    false false false false false true false

canonicalGovernanceMetricProvenanceReceipt : GenericReceipt.GenericReceipt
canonicalGovernanceMetricProvenanceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo governance metric role provenance firewall"
    "DASHI.Governance.BoloBoloGovernanceMetricProvenanceExact"
    "GovernanceMetricReceipt / canonicalGovernanceMetricProvenanceBoundary"
    "cross-pollinates the repo-wide number/role provenance discipline into governance calibration: scalar value, semantic role, unit label and provenance remain separate; an exact finite witness gives the same Nat value 120 in duration and interface-capacity roles while proving the roles distinct"
    "equal scalars do not identify metric meanings, units or evidence provenance; comparator observations do not auto-transfer to target bolo quantities and target thresholds cannot be chosen retrospectively merely to fit observed outcomes"
    "agda -i . DASHI/Governance/BoloBoloGovernanceMetricProvenanceRegression.agda"
