#!/usr/bin/env bash
# Local-first acceptance for V2 reluctance/permeance, polyphase and attribution.
# RUN_AGDA=1 required for kernel acceptance; Python passing never implies Agda passed.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
python scripts/check_v2_maxcut.py >/dev/null
python scripts/check_reluctance_permeance_phase_maxcut.py >/dev/null
python scripts/check_reluctance_phase_symmetry_maxcut.py >/dev/null
python scripts/check_v2_pulse_nonlinear_recovery.py >/dev/null
python scripts/v2_pulse_restricted_global_optimum.py >/dev/null
python scripts/v2_retarded_causal_network_maxcut.py >/dev/null
python -m pytest -q tests/test_v2_maxcut.py tests/test_reluctance_permeance_phase_maxcut.py tests/test_reluctance_phase_symmetry_maxcut.py tests/test_v2_pulse_nonlinear_recovery.py tests/test_v2_coupled_pulse_machine_maxcut.py tests/test_v2_pulse_restricted_global_optimum.py tests/test_v2_retarded_causal_network_maxcut.py
if [[ "${RUN_AGDA:-0}" == "1" ]]; then
  command -v agda >/dev/null 2>&1 || { echo 'Agda kernel requested but not installed' >&2; exit 42; }
  agda -i . DASHI/Physics/Motors/MadScience369V2FinitePowerDiscriminatorsExact.agda
  agda -i . DASHI/Physics/Motors/ReluctancePermeancePulseBoundaryExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2PulsedCoenergyRecoveryBidiExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2ClampReroutingExact.agda
  agda -i . DASHI/Physics/Motors/MadScience369V2CausalFlightBoundExact.agda
  printf 'Agda acceptance: five source modules passed on this environment\n'
else
  printf 'Agda kernel: NOT RUN (use RUN_AGDA=1 with pinned toolchain)\n'
fi
printf 'Original V2 source/FEA/torque/power/thermal gates: OPEN\n'
