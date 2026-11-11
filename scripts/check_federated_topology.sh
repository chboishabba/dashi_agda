#!/usr/bin/env bash
# Run from repository root; never silently count a Python smoke as Agda acceptance.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:---kernel}"
case "$mode" in --cpu-only|--kernel) ;; *) echo 'Usage: scripts/check_federated_topology.sh [--cpu-only|--kernel]' >&2; exit 64 ;; esac
python3 scripts/federated_topology_gate.py --self-test
mkdir -p artifacts/federated_topology
python3 scripts/federated_topology_gate.py --receipt artifacts/federated_topology/finite_preflight.json >/dev/null
if [[ "$mode" == "--cpu-only" ]]; then
  echo 'CPU synthetic preflight PASS; Agda kernel, original-model parity, network and GPU still UNCHECKED.'
  exit 0
fi
if ! command -v agda >/dev/null 2>&1; then
  echo 'BLOCKED: agda is unavailable. Use the existing Nix devShell: nix develop --command bash scripts/check_federated_topology.sh --kernel' >&2
  exit 2
fi
for module in \
  DASHI/Reasoning/FederatedMinerWorkerTopologyExact.agda \
  DASHI/Reasoning/FederatedTieredMoEFiniteExact.agda \
  DASHI/Reasoning/MoEOutOfCoreStreamingFiniteExact.agda
do
  echo "Agda checking: $module"
  agda --no-libraries -i . "$module"
done
agda --version
python3 - <<'PY'
import json
import subprocess
from pathlib import Path
p=Path("artifacts/federated_topology/finite_preflight.json")
r=json.loads(p.read_text())
r["agda_kernel_checked"]=True
r["agda_version"]=subprocess.check_output(["agda","--version"],text=True).strip()
r["checked_modules"]=[
    "DASHI/Reasoning/FederatedMinerWorkerTopologyExact.agda",
    "DASHI/Reasoning/FederatedTieredMoEFiniteExact.agda",
    "DASHI/Reasoning/MoEOutOfCoreStreamingFiniteExact.agda",
]
r["release_admitted"]=False
p.write_text(json.dumps(r,indent=2,sort_keys=True)+"\n")
PY
printf '%s\n' 'FINITE KERNEL GATE PASS; original Qwen/LILA source execution, network, cryptography, GPU and deployment remain UNCHECKED.'
