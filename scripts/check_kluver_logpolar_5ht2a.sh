#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
files=(
  "DASHI/Biology/KluverLogPolar5HT2ASourceAtlasExact.agda"
  "DASHI/Biology/Psychedelic5HT2AAttentionBoundaryExact.agda"
  "DASHI/Cognition/LogPolarKluverDerivationExact.agda"
  "DASHI/Cognition/Kluver5HT2ACrossPollinationExact.agda"
  "DASHI/Cognition/KluverLogPolar5HT2AEverything.agda"
  "DASHI/Biology/Kluver5HT2ACrossScaleHyperfibreExact.agda"
  "DASHI/Biology/Kluver5HT2AMolecularProteinInstantiationExact.agda"
  "DASHI/Biology/FiveHT2ASignalingDialecticExact.agda"
  "DASHI/Biology/FiveHT2AProtocolIndexedSignalTransportExact.agda"
  "DASHI/Biology/FiveHT2AVisualCortexBioelectricBridgeExact.agda"
  "DASHI/Cognition/FiveHT2AVisualModeObservationBridgeExact.agda"
)

for relative in "${files[@]}"; do
  file="$root/$relative"
  test -f "$file"
  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!!\}|TODO|FIXME|--allow-unsolved-metas' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $relative" >&2
    exit 1
  fi
done

atlas="$root/DASHI/Biology/KluverLogPolar5HT2ASourceAtlasExact.agda"
grep -Fq 'Docs/SourceAttributionPolicy.md' "$atlas"
grep -Fq '10.1007/BF00336965' "$atlas"
grep -Fq '10.1016/0042-6989(80)90090-5' "$atlas"
grep -Fq '10.1016/0042-6989(94)00187-Q' "$atlas"
grep -Fq '10.1098/rstb.2000.0769' "$atlas"
grep -Fq '10.1073/pnas.071582498' "$atlas"
grep -Fq 'pubmed.ncbi.nlm.nih.gov/10688105' "$atlas"
grep -Fq '10.1523/JNEUROSCI.2830-16.2016' "$atlas"
grep -Fq '10.1016/j.cub.2016.12.030' "$atlas"
grep -Fq '10.7554/eLife.35082' "$atlas"
grep -Fq '10.1523/JNEUROSCI.4692-12.2013' "$atlas"
grep -Fq '10.1016/j.cortex.2024.11.010' "$atlas"
grep -Fq '10.1038/s41467-024-51861-1' "$atlas"
grep -Fq '10.1038/s42003-025-09492-9' "$atlas"
grep -Fq '10.1016/j.neubiorev.2026.106649' "$atlas"

boundary="$root/DASHI/Biology/Psychedelic5HT2AAttentionBoundaryExact.agda"
grep -Fq 'imperativeLookAtThisMechanismEstablishedIsFalse' "$boundary"
grep -Fq 'telepathicEntitySignalEstablishedIsFalse' "$boundary"
grep -Fq 'anteriorCingulate5HT2ABindingSourceBoundIsTrue' "$boundary"

cross="$root/DASHI/Cognition/Kluver5HT2ACrossPollinationExact.agda"
grep -Fq 'geometryAndPharmacologyAreSeparateEvidenceLayersIsTrue' "$cross"
grep -Fq 'jointMechanismEmpiricallyClosedIsFalse' "$cross"
grep -Fq 'feltImportanceProvesExternalAgencyIsFalse' "$cross"

hyperfibre="$root/DASHI/Biology/Kluver5HT2ACrossScaleHyperfibreExact.agda"
grep -Fq 'NeurochemicalAtomicChemistryBridge' "$hyperfibre"
grep -Fq 'NeurochemicalProteinTargetBridge' "$hyperfibre"
grep -Fq 'NeurochemicalTransmissionBridge' "$hyperfibre"
grep -Fq 'NeurochemicalBrainCarrierBridge' "$hyperfibre"
grep -Fq 'ProteinConformationAttractor' "$hyperfibre"
grep -Fq 'AtomicPeriodicTable369ChemistryHyperfibreBridgeExact' "$hyperfibre"
grep -Fq 'receptorToCorticalModeTransferIsQuantitativelyClosedIsFalse' "$hyperfibre"
grep -Fq 'visualPhenomenologyIsRecoveredFromMolecularStateIsFalse' "$hyperfibre"

molecular="$root/DASHI/Biology/Kluver5HT2AMolecularProteinInstantiationExact.agda"
grep -Fq 'PubChem CID 5202' "$molecular"
grep -Fq 'PubChem CID 5761' "$molecular"
grep -Fq 'PubChem CID 3822' "$molecular"
grep -Fq 'PDB 9AS4' "$molecular"
grep -Fq 'wacker5HT2BNeighborEvidence' "$molecular"
grep -Fq 'assayBoundAffinityStillMissingIsTrue' "$molecular"
grep -Fq 'receptorStateToKluverModeTransferStillMissingIsTrue' "$molecular"
grep -Fq 'ketanserinIdentityAloneDoesNotProveSelective5HT2ABlockade' "$molecular"

signaling="$root/DASHI/Biology/FiveHT2ASignalingDialecticExact.agda"
grep -Fq 'wallachGqHTR' "$signaling"
grep -Fq 'xuGiHallucinogenicAssay' "$signaling"
grep -Fq 'universalGqOnlyMechanismBlocked' "$signaling"
grep -Fq 'universalGiOnlyMechanismBlocked' "$signaling"
grep -Fq 'humanPhenomenologyMechanismClosedIsFalse' "$signaling"

transport="$root/DASHI/Biology/FiveHT2AProtocolIndexedSignalTransportExact.agda"
grep -Fq 'protocolIdentityPreservedIsTrue' "$transport"
grep -Fq 'signalingModulatorCanChangeOutputAtFixedInput' "$transport"
grep -Fq 'quantitativeBiophysicalCalibrationPresentIsFalse' "$transport"
grep -Fq 'receptorSignalDeterminesBrainStateIsFalse' "$transport"

v1="$root/DASHI/Biology/FiveHT2AVisualCortexBioelectricBridgeExact.agda"
grep -Fq 'chemicalCoordinateCanChangeNetworkState' "$v1"
grep -Fq 'quantitativeVoltageCurrentTransferClosedIsFalse' "$v1"
grep -Fq 'mouseV1DoesNotDetermineHumanHallucination' "$v1"

mode="$root/DASHI/Cognition/FiveHT2AVisualModeObservationBridgeExact.agda"
grep -Fq 'temporalDoesNotDetermineSpatial' "$mode"
grep -Fq 'gainDoesNotDetermineForm' "$mode"
grep -Fq 'spatialFieldProtocolPresentIsFalse' "$mode"

echo 'Kluver/log-polar/5-HT2A attribution and boundary static contract: OK'
