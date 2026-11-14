#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

for source in \
  DASHI/Wikimedia/IbrahimFiniteOrbitRevisionWeldExact.agda \
  DASHI/Wikimedia/IbrahimMultilingualHyperfabricWeldExact.agda \
  DASHI/Wikimedia/IbrahimPublishedSevenNodeFunnelExact.agda \
  DASHI/Wikimedia/IbrahimFiniteFigureBasinCertificateExact.agda \
  DASHI/Wikimedia/IbrahimITIRConsumerRepairExact.agda; do
  test -s "$source"
  if grep -En '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' "$source"; then
    echo "forbidden proof escape in $source" >&2
    exit 1
  fi
  if grep -Fq '{!!}' "$source"; then
    echo "unresolved Agda hole in $source" >&2
    exit 1
  fi
done

python3 -m compileall -q scripts/ibrahim_fln_reference_analysis.py scripts/ibrahim_fln_certificates.py tests/test_ibrahim_fln_reference_analysis.py tests/test_ibrahim_fln_certificates.py tests/test_ibrahim_fln_certificate_cli.py
python3 -m unittest discover -s tests -p 'test_ibrahim_fln*.py' -v

if [ "$(printenv IBRAHIM_SKIP_AGDA 2>/dev/null || true)" = "1" ]; then
  echo "WARNING: Python/static tests only; kernel proof status remains OPEN"
  exit 0
fi

AGDA_BIN="$(printenv AGDA_BIN 2>/dev/null || printf agda)"
command -v "$AGDA_BIN" >/dev/null || {
  echo "Agda unavailable: kernel validation REQUIRED, not waived" >&2
  exit 127
}
"$AGDA_BIN" --version
for source in \
  DASHI/Wikimedia/IbrahimFiniteOrbitRevisionWeldExact.agda \
  DASHI/Wikimedia/IbrahimMultilingualHyperfabricWeldExact.agda \
  DASHI/Wikimedia/IbrahimPublishedSevenNodeFunnelExact.agda \
  DASHI/Wikimedia/IbrahimFiniteFigureBasinCertificateExact.agda \
  DASHI/Wikimedia/IbrahimITIRConsumerRepairExact.agda; do
  "$AGDA_BIN" --safe -i . -l standard-library "$source"
done

if [ "$(printenv IBRAHIM_AGGREGATE_CHECK 2>/dev/null || true)" = "1" ]; then
  "$AGDA_BIN" --safe -i . -l standard-library DASHI/Wikimedia/Everything.agda
fi
echo "Ibrahim source and local kernel checks passed; historical corpus gates separate"
