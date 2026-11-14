#!/usr/bin/env bash
# KSW 668 original source max-cut: LOCAL receipt only; CI is irrelevant.
set -euo pipefail
cd "$(dirname "$0")/.."
MODE="--math"
if [ "$#" -gt 0 ]; then MODE="$1"; fi
KSW_MOVEBANK_GPS_FILE="${KSW_MOVEBANK_GPS_FILE:-}"
KSW_ENA_ORIGINAL_RECEIPT="${KSW_ENA_ORIGINAL_RECEIPT:-}"
mkdir -p Artifacts/ksw668/local-check
LOG=Artifacts/ksw668/local-check/acceptance-command-log.tsv
printf 'kind\tcommand\tstate\n' > "$LOG"

run() {
  local kind="$1"; shift
  printf '%s\t%s\tRUN\n' "$kind" "$*" | tee -a "$LOG"
  "$@"
  printf '%s\t%s\tPASS\n' "$kind" "$*" | tee -a "$LOG"
}

echo "KSW668 local max-cut mode=$MODE"
run python python3 scripts/check_ksw668_maxcut.py
run python python3 scripts/check_ksw668_physical_maxcut.py
run python python3 scripts/check_ksw668_human_ams_original.py
run python python3 scripts/test_ksw668_primary_empirical_weld.py
run python python3 scripts/check_ksw668_maxwell_3d_jet.py
run python python3 scripts/ksw668_neutron_energy_nonextrapolation.py
run python python3 scripts/ksw668_nuclear_electron_final_states.py
run python python3 scripts/ksw668_bare_nuclear_two_body_kinematics.py
run python python3 scripts/ksw668_n14_relativistic_lab_final_state.py
run python python3 scripts/check_ksw668_spacelike_kk_projection.py
run python python3 scripts/ksw668_a1_original_rational_fourier_witness.py
run python python3 scripts/ksw668_u1_4potential_continuum.py
run python python3 scripts/ksw668_kk_vacuum_observer_solution.py
run python python3 scripts/ksw668_kk_einstein_scalar_cosmology.py
run python python3 scripts/test_ksw668_endf81_primary.py
run python python3 scripts/test_ksw668_endf81_law_integral.py
run python python3 scripts/test_ksw668_e2_bound.py
run python python3 scripts/ksw668_e2_neutron_isotope_visibility_bound.py
run python python3 scripts/test_ksw668_movebank_join.py
run python python3 scripts/ksw668_mms_burst_acquire.py
run python python3 scripts/ksw668_mms_sdc_direct.py
run python python3 scripts/ksw668_ena_reads_acquire.py

if [ "$MODE" = "--math" ]; then
  echo "Math-only local tests complete. Raw archives and Agda not accepted."
  exit 0
fi
if [ "$MODE" != "--all" ]; then
  echo "Usage: $0 --math | --all" >&2
  exit 2
fi

if [ ! -f "$HOME/.cache/dashi-ksw668/mms_sdc_original_sha.json" ]; then
  echo "BLOCKED: original raw MMS CDF receipt absent" >&2
  exit 65
fi
run raw python3 scripts/ksw668_mms_sdc_direct.py \
  --cache data/mms_original_SDC_20170617 \
  --verify "$HOME/.cache/dashi-ksw668/mms_sdc_original_sha.json"

if [ -z "$KSW_MOVEBANK_GPS_FILE" ] || [ ! -f "$KSW_MOVEBANK_GPS_FILE" ]; then
  echo "BLOCKED: original Movebank GPS CSV/ZIP absent" >&2
  exit 65
fi
run raw python3 scripts/ksw668_movebank_gps_acquire.py \
  --input "$KSW_MOVEBANK_GPS_FILE" \
  --receipt Artifacts/ksw668/local-check/movebank_sha256.json

if [ -z "$KSW_ENA_ORIGINAL_RECEIPT" ] || [ ! -f "$KSW_ENA_ORIGINAL_RECEIPT" ]; then
  echo "BLOCKED: original ENA FASTQ checksum receipt absent" >&2
  exit 65
fi
if ! command -v nix >/dev/null 2>&1 && ! command -v agda >/dev/null 2>&1; then
  echo "BLOCKED: pinned Agda toolchain not installed" >&2
  exit 66
fi

run agda bash scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Plasma/KSW668FiniteDiscriminatorsExact.agda \
  DASHI/Physics/Plasma/KSW668MHDSelectedStateTransferExact.agda \
  DASHI/Physics/Plasma/KSW668RationalThreeModeSourceExact.agda \
  DASHI/Physics/Plasma/KSW668RationalThreeModeOriginalRowsExact.agda \
  DASHI/Physics/Plasma/KSW668MaxwellLocalPoyntingExact.agda \
  DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda \
  DASHI/Physics/Plasma/KSW668IsotopeCausalResidualExact.agda \
  DASHI/Physics/Plasma/KSW668EmpiricalBoundariesExact.agda \
  DASHI/Physics/Chemistry/KSW668NuclearElectronStateLedgerExact.agda \
  DASHI/Physics/Gravity/KSW668KaluzaKleinSpacelikeFiberCausalExact.agda \
  DASHI/Physics/Gravity/KSW668FiveDimensionalEinsteinScalarFRWFriedmannExact.agda \
  DASHI/Biology/KSW668EmpiricalIsotopeMagnetoreceptionSourceExact.agda \
  DASHI/Biology/KSW668HumanCarbon14ObservedExact.agda \
  DASHI/Physics/Plasma/KSW668SourceCrosswalkExact.agda

echo "Local original raw and Agda source checks PASS; no universal physics promoted."
