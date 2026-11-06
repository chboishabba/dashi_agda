#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Geometry/GielisBase369FiniteExact.agda
  DASHI/Geometry/GielisBase369NyquistPhase36Exact.agda
  DASHI/Geometry/GielisBase369ExistingOwnersWeldExact.agda
  DASHI/Geometry/GielisBishopPolynomialExact.agda
)
for source_file in "${sources[@]}"; do
  [[ -s "$source_file" ]] || { echo "missing Agda source: $source_file" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--unsafe|TERMINATING|NON_COVERING' "$source_file"; then
    echo "Agda trust escape rejected: $source_file" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source_file"; then
    echo "Agda hole rejected: $source_file" >&2
    exit 1
  fi
done

python scripts/gielis_base369_source_audit.py > /dev/null
python scripts/gielis_cyclotomic36_exact.py > /dev/null
python scripts/gielis_sector_spectral_certificate.py --m 9 --sectors 2048 > /dev/null
python scripts/gielis_rayleigh_spectral_bound.py > /dev/null
python scripts/gielis_raster_fd_positivity_certificate.py --m 3 --grid 41 > /dev/null
python scripts/gielis_raster_fd_positivity_certificate.py --m 6 --grid 41 > /dev/null
python scripts/gielis_raster_fd_positivity_certificate.py --m 9 --grid 41 > /dev/null
python scripts/gielis_base369_symbolic_certificates.py > /dev/null

scripts/run_agda29_parallel_check.sh --safe "${sources[@]}"

python -m pytest -q tests/test_gielis_base369_experiments.py
python scripts/gielis_base369_experiments.py --pde --optics \
  --rays 72 --segments 384 --bounces 4 --controls --torque-objective min > /dev/null
python scripts/gielis_reflection_parity.py --m 3 --epsilon .12 \
  --rays 12 --segments 384 --brackets 3072 > /dev/null
python scripts/gielis_optical_statistics.py --rays 24 --segments 128 \
  --bounces 2 --seed 369 > /dev/null
if [[ -n "${KOZYREV_PR1404_DIR:-}" ]]; then
  python scripts/gielis_kozyrev_pr1404_bridge.py \
    --legacy-dir "$KOZYREV_PR1404_DIR" --require-legacy \
    --segments 256 --rays 24 > /dev/null
else
  echo "G13 PR1404 exact-source replay NOT CHECKED: supply KOZYREV_PR1404_DIR" >&2
fi
echo "Finite/math/simulation checks passed; native physics and G13 original HTML remain OPEN"
