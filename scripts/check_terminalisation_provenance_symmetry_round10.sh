#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_itir_reopenable_evidence_hyperfibre.sh"
if [[ -x "$BASE_CHECKER" ]]; then
  "$BASE_CHECKER"
fi

FILES=(
  DASHI/Core/TerminalisationArchitectureExact.agda
  DASHI/Core/SelfSealingTerminalisationExact.agda
  DASHI/Core/PropositionIndependenceExact.agda
  DASHI/Core/TerminalisationMasterArchitectureExact.agda
  DASHI/Core/FiniteC3OrbitStabilizerExact.agda
  DASHI/Core/C3OrbitProvenanceQuotientExact.agda
  DASHI/Core/EfficientRecoverableQuotientExact.agda
  DASHI/Core/C3EfficientReopeningExampleExact.agda
  DASHI/Core/GradedProvenanceDynamicalSystemExact.agda
  DASHI/Core/HiddenPhaseDynamicInsufficiencyExact.agda
  DASHI/Cognition/PNF/CoupledDepthPhaseFrustrationExact.agda
  DASHI/Foundations/DepthWheelMacroBranchingExact.agda
  DASHI/Cognition/PNF/MemoryCommandSeparationExact.agda
  DASHI/Crypto/ReopeningArchitectureExact.agda
  DASHI/Crypto/MLKEMNoisyReopeningExact.agda
  DASHI/Arithmetic/PrimeSupportTransportTaxiMoonshineExact.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'selfSealingContradictsCorrectiveReopening' DASHI/Core/SelfSealingTerminalisationExact.agda
grep -q 'closedTerminalRegionContradictsAntiTerminalisation' DASHI/Core/TerminalisationMasterArchitectureExact.agda
grep -q 'orbitStabilizerFixedCardinality' DASHI/Core/FiniteC3OrbitStabilizerExact.agda
grep -q 'c3SymmetryEnhancementReceipt' DASHI/Core/FiniteC3OrbitStabilizerExact.agda
grep -q 'c3OrbitProvenanceBearingQuotient' DASHI/Core/C3OrbitProvenanceQuotientExact.agda
grep -q 'EfficientRecoverableFamily' DASHI/Core/EfficientRecoverableQuotientExact.agda
grep -q 'c3EfficientRecoverableFamily' DASHI/Core/C3EfficientReopeningExampleExact.agda
grep -q 'dynamicInsufficiencyContradictsSufficiency' DASHI/Core/GradedProvenanceDynamicalSystemExact.agda
grep -q 'noPhaseErasingCoarseStep' DASHI/Core/HiddenPhaseDynamicInsufficiencyExact.agda
grep -q 'synchronisedAttainsGlobalLowerBound' DASHI/Cognition/PNF/CoupledDepthPhaseFrustrationExact.agda
grep -q 'polarOneWheelIs8' DASHI/Foundations/DepthWheelMacroBranchingExact.agda
grep -q 'ternaryOneWheelIs27' DASHI/Foundations/DepthWheelMacroBranchingExact.agda
grep -q 'extinctionIsMemoryCommandSeparation' DASHI/Cognition/PNF/MemoryCommandSeparationExact.agda
grep -q 'ModelRelativeReopening' DASHI/Crypto/ReopeningArchitectureExact.agda
grep -q 'toyPublicCollision' DASHI/Crypto/MLKEMNoisyReopeningExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMNoisyReopeningExact.agda
grep -q 'taxiEarns196883' DASHI/Arithmetic/PrimeSupportTransportTaxiMoonshineExact.agda
grep -q 'chooseTwelveThreeIs220' DASHI/Arithmetic/PrimeSupportTransportTaxiMoonshineExact.agda
grep -q 'arithmeticLandingDoesNotConstructMoonshine' DASHI/Arithmetic/PrimeSupportTransportTaxiMoonshineExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed scan completed; no kernel-clean claim"
fi
