#!/usr/bin/env bash
# Local-first acceptance for the V2 reluctance/permeance, polyphase and attribution cut.
# RUN_AGDA=1 is required for kernel acceptance; Python passing never means Agda passed.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
# Small dense matrices perform much faster and deterministically with single-threaded BLAS.
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
# Default gate is the complete local pytest suite. The standalone programs
# recompute sometimes-expensive synthetic sweep artifacts and are opt-in.
# A pytest PASS must not be mistaken for a full producer refresh.
if [[ "${RUN_PRODUCERS:-0}" == "1" ]]; then
  python scripts/check_v2_maxcut.py >/dev/null
  python scripts/check_reluctance_phase_symmetry_maxcut.py >/dev/null
  python scripts/check_v2_pulse_nonlinear_recovery.py >/dev/null
  python scripts/v2_pulse_restricted_global_optimum.py >/dev/null
  python scripts/v2_retarded_causal_network_maxcut.py >/dev/null
  python scripts/v2_distributed_causal_line_maxcut.py >/dev/null
  python scripts/v2_periodic_causal_motor_certificate.py >/dev/null
  python scripts/v2_nonlinear_causal_periodic_weld.py >/dev/null
  if [[ "${RUN_SLOW_PRODUCERS:-0}" == "1" ]]; then
    python scripts/check_reluctance_permeance_phase_maxcut.py >/dev/null
  else
    printf 'Full legacy SLSQP producer: NOT RUN (RUN_SLOW_PRODUCERS=1)\n'
  fi
else
  printf 'Standalone producer replay: NOT RUN (RUN_PRODUCERS=1)\n'
fi
python -m pytest -q tests/test_v2_maxcut.py tests/test_reluctance_permeance_phase_maxcut.py tests/test_reluctance_phase_symmetry_maxcut.py tests/test_v2_pulse_nonlinear_recovery.py tests/test_v2_coupled_pulse_machine_maxcut.py tests/test_v2_pulse_restricted_global_optimum.py tests/test_v2_retarded_causal_network_maxcut.py tests/test_v2_distributed_causal_line_maxcut.py tests/test_v2_periodic_causal_motor_certificate.py tests/test_v2_nonlinear_causal_periodic_weld.py
if [[ "${RUN_AGDA:-0}" == "1" ]]; then
  command -v agda >/dev/null 2>&1 || { echo 'Agda kernel requested but not installed' >&2; exit 42; }
  agda -i . DASHI/Physics/Motors/MadScience369V2FinitePowerDiscriminatorsExact.agda
  agda -i . DASHI/Physics/Motors/ReluctancePermeancePulseBoundaryExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2PulsedCoenergyRecoveryBidiExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2ClampReroutingExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2CausalFlightBoundExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2DelayQueueEnergyExact.agda
  printf 'Agda acceptance: six source modules passed on this environment\n'
else
  printf 'Agda kernel: NOT RUN (use RUN_AGDA=1 with pinned toolchain)\n'
fi
printf 'Original V2 source/FEA/torque/power/thermal gates: OPEN\n'