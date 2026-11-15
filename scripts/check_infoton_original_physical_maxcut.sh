#!/usr/bin/env bash
# Original-physical Infoton acceptance suite (not a cosmetic CI badge).
# Run only from a complete DASHI checkout with pinned Agda and Python deps.
# Fail closed if the physical gauge donor, metrology tests or kernel is absent.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "[1/4] Original 27-state physical gauge group (conditional E6/VEV source)"
python3 scripts/check_kk_e6_post_e21_u3_photon.py

echo "[2/4] Source-matched physical thermal dispatch"
python3 scripts/datacentre_thermal_reuse_dispatch.py >/dev/null

echo "[3/4] P30/ECC and original physical metrology tests"
python3 -m unittest discover -s scripts -p 'test_infoton*.py' -v

echo "[4/4] Pinned Agda physical-adapter kernel check"
if ! command -v agda >/dev/null 2>&1; then
  echo "OPEN: Agda compiler missing; no kernel certificate issued" >&2
  exit 8
fi
version="$(agda --version)"
case "$version" in
  *2.8.0.2*) ;;
  *)
    echo "OPEN: pinned Agda 2.8.0.2 required; found $version" >&2
    exit 9
    ;;
esac
agda -i . DASHI/Quantum/InfotonOriginalPhysicalAdapterWeldExact.agda
agda -i . DASHI/Quantum/Infoton369FermiChargeBoundaryExact.agda
agda -i . DASHI/ComputerScience/InfotonP30FiniteAuditExact.agda
echo "PASS original 27-state, physical dispatch, Python suites and pinned Agda modules."
echo "NOTE: this verifies SOURCE/INTERFACE only; original P30, metered joules,"
echo "particle detector and facility water measurements remain independent OPEN gates."
