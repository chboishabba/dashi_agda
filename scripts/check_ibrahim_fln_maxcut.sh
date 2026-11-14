#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

for source in \
  DASHI/Wikimedia/IbrahimFiniteOrbitRevisionWeldExact.agda \
  DASHI/Wikimedia/IbrahimMultilingualHyperfabricWeldExact.agda \
  DASHI/Wikimedia/IbrahimPublishedSevenNodeFunnelExact.agda \
  DASHI/Wikimedia/IbrahimGeneralFiniteCertificateKernelExact.agda \
  DASHI/Wikimedia/IbrahimFinitePigeonholeProducerExact.agda \
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

python3 -m compileall -q scripts/ibrahim_fln_reference_analysis.py scripts/ibrahim_fln_certificates.py tests/test_ibrahim_fln_reference_analysis.py tests/test_ibrahim_fln_certificates.py tests/test_ibrahim_fln_certificate_cli.py scripts/ibrahim_itir_multilingual_candidate.py tests/test_ibrahim_itir_multilingual_candidate.py scripts/ibrahim_author_parser_port.py tests/test_ibrahim_author_parser_port.py scripts/ibrahim_fln_agda_certificate_export.py tests/test_ibrahim_fln_agda_certificate_export.py tests/test_ibrahim_finite_pigeonhole_oracle.py
python3 -m unittest discover -s tests -p 'test_ibrahim*.py' -v

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
  DASHI/Wikimedia/IbrahimGeneralFiniteCertificateKernelExact.agda \
  DASHI/Wikimedia/IbrahimFinitePigeonholeProducerExact.agda \
  DASHI/Wikimedia/IbrahimFiniteFigureBasinCertificateExact.agda \
  DASHI/Wikimedia/IbrahimITIRConsumerRepairExact.agda; do
  NO_TMUX=1 ./scripts/parallel_check.sh "$source"
done

# Compile a MANIFEST-VERIFIED full seven-node manuscript graph as an
# independent, generated Agda proof carrier. The new generator's refl
# equations are checked by Agda, never trusted from Python.
GEN_FILE="DASHI/Wikimedia/GeneratedIbrahimFigureCertificateExact.agda"
trap 'rm -f "$GEN_FILE"' EXIT
python3 scripts/ibrahim_fln_agda_certificate_export.py \
  --input tests/fixtures/ibrahim_paper_figure_2_4.json \
  --manifest tests/fixtures/ibrahim_paper_figure_2_4.manifest.json \
  --module DASHI.Wikimedia.GeneratedIbrahimFigureCertificateExact \
  --output "$GEN_FILE"
NO_TMUX=1 ./scripts/parallel_check.sh "$GEN_FILE"

if [ "$(printenv IBRAHIM_AGGREGATE_CHECK 2>/dev/null || true)" = "1" ]; then
  "$AGDA_BIN" --safe -i . -l standard-library DASHI/Wikimedia/Everything.agda
fi
echo "Ibrahim source and local kernel checks passed; historical corpus gates separate"
