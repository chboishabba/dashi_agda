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

echo 'Kluver/log-polar/5-HT2A attribution and boundary static contract: OK'
