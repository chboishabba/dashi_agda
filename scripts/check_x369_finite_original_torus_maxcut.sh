#!/usr/bin/env bash
# Exact original-carrier X369 C3² action / orthogonality leaf checker.
# Must NOT claim this is a physical NS/YM proof or whole-system promotion.
set -euo pipefail
cd "$(dirname "$0")/.."
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369OriginalTorusGroupLawExact.agda \
  DASHI/Cognition/PNF/X369FiniteTorusAndRouterActionWeldExact.agda \
  DASHI/Cognition/PNF/X369OriginalTorusCharacterOrthogonalityExact.agda \
  DASHI/Cognition/PNF/X369OriginalSignedSiteOrderBidiExact.agda \
  DASHI/Cognition/PNF/X369OriginalTorusSpectralBasisExact.agda \
  DASHI/Cognition/PNF/X369OriginalTorusPointedAffineBidiExact.agda \
  DASHI/Cognition/PNF/X369OrbitAbsolutePhaseGaugeExact.agda
echo "X369 finite original-torus selected Agda leaf modules passed Track B; authoritative Track A still independent."
