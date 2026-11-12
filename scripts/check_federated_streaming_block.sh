#!/usr/bin/env bash
# Focused local verification. CPU simulator and kernel proof are separate gates.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:---kernel}"
case "$mode" in --cpu-only|--kernel) ;; *) echo "Usage: $0 [--cpu-only|--kernel]" >&2; exit 64 ;; esac
python3 scripts/federated_streaming_schedule_gate.py --self-test
if [[ "$mode" == "--cpu-only" ]]; then
  echo "Synthetic scheduling tests passed. Agda kernel NOT checked."
  exit 0
fi
command -v agda >/dev/null || {
  echo "Agda unavailable. Use the already-working Agda 2.9 parallel check environment." >&2
  exit 2
}
agda --no-libraries -i . DASHI/Reasoning/FederatedStreamingBlockRefinementFiniteExact.agda
agda --version
echo "Finite streaming / revision Agda proof accepted; original diffusion model and WAN remain OPEN."
