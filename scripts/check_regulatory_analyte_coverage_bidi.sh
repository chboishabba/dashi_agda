#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Chemistry/TGO93PhEurPesticideMembershipExact.agda
  DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
  DASHI/Chemistry/AssayDetectionEnvelopeExact.agda
  DASHI/Chemistry/SpeciesMethodDetectionCrossPollinationExact.agda
  DASHI/Chemistry/DefensiveRegulatoryAssayStressAuditExact.agda
  DASHI/Chemistry/RegulatoryAnalytePanelRefinementExact.agda
  DASHI/Chemistry/Everything.agda
  DASHI/RegulatoryAnalyteCoverageValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required regulatory-analyte source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^ddtIsPresentInAustralianTGO93PhEurPanel :' DASHI/Chemistry/TGO93PhEurPesticideMembershipExact.agda
grep -q '^acephateIsPresentInAustralianTGO93PhEurPanel :' DASHI/Chemistry/TGO93PhEurPesticideMembershipExact.agda
grep -q '^chlorpyriphosEthylIsPresentInAustralianTGO93PhEurPanel :' DASHI/Chemistry/TGO93PhEurPesticideMembershipExact.agda
grep -q '^notExplicitTableMemberCannotAutoPromoteToNoRegulatoryLimit :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^complianceCannotRecoverCompleteOffPanelState :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^certificateCannotRecoverCompleteOffPanelState :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^offPanelCannotAutoPromoteToUndetectable :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^socialMediaAssertionCannotAutoPromoteToVerifiedBypass :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^notDetectedCannotRecoverTrueAbsence :' DASHI/Chemistry/AssayDetectionEnvelopeExact.agda
grep -q '^tableLimitCannotAutoPromoteToLOD :' DASHI/Chemistry/AssayDetectionEnvelopeExact.agda
grep -q '^tableLimitCannotAutoPromoteToLOQ :' DASHI/Chemistry/AssayDetectionEnvelopeExact.agda
grep -q '^moleculeIdentityCannotRecoverMethodDetectability :' DASHI/Chemistry/SpeciesMethodDetectionCrossPollinationExact.agda
grep -q '^methodFamilyAloneCannotRecoverDetectionThreshold :' DASHI/Chemistry/SpeciesMethodDetectionCrossPollinationExact.agda
grep -q '^stressWitnessRefutesCompleteRecovery :' DASHI/Chemistry/DefensiveRegulatoryAssayStressAuditExact.agda
grep -q '^canonicalScreenshotApplicationBoundary :' DASHI/Chemistry/DefensiveRegulatoryAssayStressAuditExact.agda
grep -q '^requiredPanelCannotRecoverOffPanelPresence :' DASHI/Chemistry/RegulatoryAnalytePanelRefinementExact.agda
grep -q '^expandedProjectionRecoversDeclaredOffPanelCoordinate :' DASHI/Chemistry/RegulatoryAnalytePanelRefinementExact.agda
grep -q '^expandedPanelCannotAutoPromoteToUniversalChemicalCompleteness :' DASHI/Chemistry/RegulatoryAnalytePanelRefinementExact.agda

scripts/run_agda29_parallel_check.sh DASHI/RegulatoryAnalyteCoverageValidation.agda
