#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round35.sh

files=(
  DASHI/Physics/YangMills/BalabanP33WilsonAtomOwnershipExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSelectedFactorEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonPairEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalPairDeepLowerExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundVariationSelectorExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound36FiniteAtomSelectorValidation.agda
)

doc=Docs/support/reference/YangMillsFiniteAtomSelectorRound36.md
index=Docs/support/reference/YangMillsReferenceIndex.md

for file in "${files[@]}" "$doc" "$index"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty six contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanP33WilsonAtomOwnershipExact.agda:allSubsetAtomCountExact'
  'BalabanP33WilsonAtomOwnershipExact.agda:correlatedAtomCountExact'
  'BalabanP33WilsonAtomOwnershipExact.agda:deepAtomCountExact'
  'BalabanP33WilsonAtomOwnershipExact.agda:ownerCannotBeBoth'
  'BalabanP33PhysicalSelectedFactorEnvelopeExact.agda:positiveSelectedDefectNorm'
  'BalabanP33PhysicalSelectedFactorEnvelopeExact.agda:inverseSelectedDefectNorm'
  'BalabanP33PhysicalSelectedFactorEnvelopeExact.agda:placementWeightProductExact'
  'BalabanP33PhysicalSelectedFactorEnvelopeExact.agda:physicalPlacementEnvelope'
  'BalabanP33WilsonPairEnvelopeExact.agda:pair01ActualNormUpper'
  'BalabanP33WilsonPairEnvelopeExact.agda:pair23ActualNormUpper'
  'BalabanP33WilsonPairEnvelopeExact.agda:pairRemainderLower'
  'BalabanP33PhysicalPairDeepLowerExact.agda:physicalPairWilsonLower'
  'BalabanP33PhysicalPairDeepLowerExact.agda:physicalDeepWilsonRemainderLower'
  'BalabanSelectedBackgroundVariationSelectorExact.agda:SingletonExtractionWitness'
  'BalabanSelectedBackgroundVariationSelectorExact.agda:selectedBackgroundSingletonCurvatureLower'
  'BalabanSelectedBackgroundVariationSelectorExact.agda:selectedBackgroundCorrelatedWilsonLower'
  'BalabanSelectedBackgroundVariationSelectorExact.agda:selectorAndRadiusGivePhysicalWLocal'
  'BalabanSelectedBackgroundVariationSelectorExact.agda:selectedVariationalSelectorOneThirtySecond'
  'BalabanSelectedBackgroundVariationSelectorExact.agda:actualSelectedPlaquetteVariationConstructedIsFalse'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1103/PhysRevD.10.2445' DASHI/Physics/YangMills/BalabanP33WilsonPairEnvelopeExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanP33PhysicalSelectedFactorEnvelopeExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanSelectedBackgroundVariationSelectorExact.agda
grep -q '10.1007/s00220-022-04609-1' DASHI/Physics/YangMills/BalabanP33PhysicalPairDeepLowerExact.agda

grep -q 'rho/256' "$doc"
grep -q '55/18874368' "$doc"
grep -q 'actual gauge-admissible, constraint-tangent selector' "$doc"
grep -Fq '[Round 36 — finite atom closure and admissible variation selector](./YangMillsFiniteAtomSelectorRound36.md)' "$index"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound36FiniteAtomSelectorValidation.agda
