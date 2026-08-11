#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round40.sh

files=(
  DASHI/Physics/YangMills/BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound41CertifiedPlaquetteEnvelopeValidation.agda
)

doc=Docs/support/reference/YangMillsCertifiedPlaquetteEnvelopeRound41.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round forty-one contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda:coefficientUpperTimesCharge'
  'BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda:localizationUpperWithPadding'
  'BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda:certifiedIntervalProducesCorrelatedOwnerBudgets'
  'BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda:certifiedSelectedPlaquetteResidualUpper'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1137/1.9780898717716' \
  DASHI/Physics/YangMills/BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda
grep -q '10.1007/BF01229381' \
  DASHI/Physics/YangMills/BalabanP33CertifiedPlaquetteOwnerEnvelopeExact.agda
grep -q '55 / 18874368' "$doc"
grep -q 'positive budget padding' "$doc"
grep -q 'cannot promote itself' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound41CertifiedPlaquetteEnvelopeValidation.agda
