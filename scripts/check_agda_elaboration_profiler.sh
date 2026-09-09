#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash -n scripts/profile_agda_elaboration_residency.sh
bash -n scripts/profile_agda_elaboration_matrix.sh

grep -q '^record ElaborationProfile' \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda
grep -q '^selectIntervention :' \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda
grep -q '^canonicalPathElaborationBoundary :' \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda

grep -q 'ComputerScienceFibreFoundationValidationExact.agda|cs-fibre-control' \
  scripts/profile_agda_elaboration_matrix.sh
grep -q 'NSTriadKNLuoFiniteRationalOrderCore.agda|ns-rational-control' \
  scripts/profile_agda_elaboration_matrix.sh
grep -q 'NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary.agda|ns-repaired-holder' \
  scripts/profile_agda_elaboration_matrix.sh
grep -q 'BalabanPath4PhysicalVarianceDecompositionExact.agda|ym-variance-stressor' \
  scripts/profile_agda_elaboration_matrix.sh

# Keep this check deliberately small: it validates the new formal boundary on
# the classical CS cone.  Running the NS/YM stress matrix is a diagnostic action,
# not a prerequisite for every PR edit.
scripts/run_agda29_parallel_check.sh \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda
