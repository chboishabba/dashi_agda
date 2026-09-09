#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash -n scripts/profile_agda_elaboration_residency.sh
bash -n scripts/profile_agda_elaboration_matrix.sh
bash -n scripts/profile_agda_profiler_views.sh

grep -q '^record ElaborationProfile' \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda
grep -q '^selectIntervention :' \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda
grep -q '^canonicalPathElaborationBoundary :' \
  DASHI/ComputerScience/AgdaElaborationResidencyComplexityExact.agda

grep -q '^data AgdaTimingProfile' \
  DASHI/ComputerScience/AgdaProfilerObservationFibreExact.agda
grep -q '^record AgdaProfilerReceipt' \
  DASHI/ComputerScience/AgdaProfilerObservationFibreExact.agda
grep -q '^profileAllConfiguration :' \
  DASHI/ComputerScience/AgdaProfilerObservationFibreExact.agda
grep -q '^selectedRepair :' \
  DASHI/ComputerScience/AgdaProfilerObservationFibreExact.agda

grep -q 'AGDA_PROFILE="all"\|AGDA_PROFILE="$profile"' \
  scripts/profile_agda_profiler_views.sh
grep -q 'run_view definitions definitions' \
  scripts/profile_agda_profiler_views.sh
grep -q 'run_view modules modules' \
  scripts/profile_agda_profiler_views.sh

grep -q 'ComputerScienceFibreFoundationValidationExact.agda|cs-fibre-control' \
  scripts/profile_agda_elaboration_matrix.sh
grep -q 'NSTriadKNLuoFiniteRationalOrderCore.agda|ns-rational-control' \
  scripts/profile_agda_elaboration_matrix.sh
grep -q 'NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary.agda|ns-repaired-holder' \
  scripts/profile_agda_elaboration_matrix.sh
grep -q 'BalabanPath4PhysicalVarianceDecompositionExact.agda|ym-variance-stressor' \
  scripts/profile_agda_elaboration_matrix.sh

# Keep this check deliberately small: validate the formal profiler boundary on
# the classical CS cone.  Running the NS/YM stress matrix remains a diagnostic
# action, not a prerequisite for every edit.
scripts/run_agda29_parallel_check.sh \
  DASHI/ComputerScience/AgdaProfilerObservationFibreExact.agda
