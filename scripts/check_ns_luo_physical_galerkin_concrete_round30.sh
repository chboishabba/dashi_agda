#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_physical_galerkin_flow_round30.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLerayOutputTransversalityRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNProjectedNonlinearityTransverseRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "concrete round thirty contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNLerayOutputTransversalityRound30Exact.agda:lerayOutputTransverseExact'
  'NSTriadKNLerayOutputTransversalityRound30Exact.agda:lerayIdempotentExact'
  'NSTriadKNProjectedNonlinearityTransverseRound30Exact.agda:projectedOrderedTermTransverse'
  'NSTriadKNProjectedNonlinearityTransverseRound30Exact.agda:projectedNonlinearityTransverseExact'
  'NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.agda:literalViscousQuadraticCoefficient'
  'NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.agda:literalViscousQuadraticCoefficientTransverse'
  'NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.agda:literalGalerkinPhysicalState'
  'NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda:concreteOutputCoefficientWitness'
  'NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda:concreteLiteralPhysicalGalerkinProducer'
  'NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda:concretePhysicalGalerkinVectorField'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNLerayOutputTransversalityRound30Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNProjectedNonlinearityTransverseRound30Exact.agda
grep -q 'literalViscousQuadraticCoefficient' DASHI/Physics/Closure/NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalGalerkinFlowRound30Validation.agda
