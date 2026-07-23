#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

cognition_files=(
  DASHI/Cognition/AnesthesiaLanguagePhaseDynamics.agda
  DASHI/Cognition/Base369ZeroFibre.agda
  DASHI/Cognition/BaselineMarginModelSelection.agda
  DASHI/Cognition/CognitiveObservableDistributions.agda
  DASHI/Cognition/CognitiveProjectionCategory.agda
  DASHI/Cognition/CognitiveResearchSources.agda
  DASHI/Cognition/CognitiveSystemAnalyticClosure.agda
  DASHI/Cognition/CognitiveVacuumClassBoundary.agda
  DASHI/Cognition/CommaDiffusionLanguage.agda
  DASHI/Cognition/DashiCognitiveSystem.agda
  DASHI/Cognition/FibreBraidReasoning.agda
  DASHI/Cognition/IdEgoSuperego369.agda
  DASHI/Cognition/IdentityVacuumClosure.agda
  DASHI/Cognition/KepplerFiniteResonanceMDL.agda
  DASHI/Cognition/Monoidal369Nonseparability.agda
  DASHI/Cognition/MultipleDraftsQuotient.agda
  DASHI/Cognition/PhaseEnrichedTrit.agda
  DASHI/Cognition/PhaseObservableIndependence.agda
  DASHI/Cognition/PhysicalCouplingFactorisation.agda
  DASHI/Cognition/PsychedelicNetworkDiffusion.agda
  DASHI/Cognition/QuantumMindEnrichedRetyping.agda
  DASHI/Cognition/QuantumMindRetypingBoundary.agda
  DASHI/Cognition/RecursiveFibreTower.agda
  DASHI/Cognition/TernaryDerivationAddress.agda
  DASHI/Cognition/TernaryDerivationUltrametric.agda
  DASHI/Cognition/VisualAttractorDefect.agda
  DASHI/Cognition/VisualPatternGeneratorMDL.agda
  DASHI/Cognition/ZeroFibreContextuality.agda
)

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{-# TERMINATING #-\}|\{-# NON_TERMINATING #-\}|TODO|FIXME' \
  "${cognition_files[@]}"; then
  echo "Cognition formalism placeholder audit failed." >&2
  exit 1
fi

agda_bin="${AGDA_BIN:-$(command -v agda)}"
"$agda_bin" \
  -i . \
  -l standard-library \
  DASHI/Cognition/LanguagePhaseEverything.agda
