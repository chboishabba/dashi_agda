#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ProofDebtRouterExact.agda
  DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required proof-debt source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^routeDebt :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^sourceEstablishedAlignedDeferredIsCertificationDebt :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^sourceEstablishedAlignedDeferredIsNotMathematicalDebt :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^record SourceAlignedDeferredTheorem' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^ConditionalDevelopment :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^certifyDeferred :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^scheduleAction :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^constrainedHeavyEstablishedReplayGoesToAristotle :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^constrainedMachineCannotReclassifyNovelMathematics :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^unAlignedCertificationCannotBeDelegatedAsProofReplay :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^record ExternalCertificationDemand' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^scheduleExternalCertification :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^heavyAlignedDemandUsesAristotle :' DASHI/Core/ProofDebtRouterExact.agda

grep -q '^rhLowVerifiedHeightSource :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^osReconstructionSourceI :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^coordinateRoute :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^cutClass :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^constrainedAction :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^rhHighRemainsMathematical :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^rhLowIsNotMathematicalDebt :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^nsR406EstimateRemainsMathematical :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^nsDyadicEquivalenceIsAlignmentDebt :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^ymOSReconstructionIsAlignmentDebt :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^ymClusteringRemainsMathematical :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^exactHeadValidationIsCertificationDebt :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^rhLowFirstActionIsAlignment :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^nsDyadicFirstActionIsAlignment :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
grep -q '^ymOSFirstActionIsAlignment :' DASHI/Core/ClayProofDebtFrontierAtlasExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/ProofDebtRouterExact.agda \
  DASHI/Core/ClayProofDebtFrontierAtlasExact.agda
