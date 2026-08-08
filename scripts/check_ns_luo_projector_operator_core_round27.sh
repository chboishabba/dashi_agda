#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_galerkin_critical_ledger_round26.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLiteralFiniteShellProjectorRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNRealityInvolutionEquivarianceRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNCentredFiveSourceProbeRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNMaximalUniformViscosityCoreRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalTriadPluckerInvariantRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoRound27FiniteCertificateGenerated.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoProjectorOperatorCoreRound27Validation.agda
  DASHI/Papers/NavierStokes/ProjectorOperatorCoreRound27.agda
  DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound27.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/architecture.puml
  docs/ns-clay-contract/projector-operator-core-round27.md
  docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
)

scripts=(
  scripts/ns_round27_projector_operator_certificate.py
)

workflow=.github/workflows/ns-luo-projector-operator-core-round27.yml

for file in "${files[@]}" "${docs[@]}" "${scripts[@]}" "$workflow"; do
  test -f "$file"
done

audit_targets=("${files[@]}" "${docs[@]}" "${scripts[@]}")

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-seven contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

projector=DASHI/Physics/Closure/NSTriadKNLiteralFiniteShellProjectorRound27Exact.agda
grep -q '10.1007/978-3-642-16830-7' "$projector"
grep -q '10.1017/CBO9780511626265' "$projector"
grep -q 'shellProjectorIdempotent' "$projector"
grep -q 'shellProjectorDisjointOutsideShell' "$projector"
grep -q 'finiteShellProjectorResolution' "$projector"
grep -q 'shellProjectorCovariant' "$projector"
grep -q 'shellProjectorCommutesWithDiagonalMultiplier' "$projector"
grep -q 'smoothLittlewoodPaleyOperatorBoundsClosed = false' "$projector"

reality=DASHI/Physics/Closure/NSTriadKNRealityInvolutionEquivarianceRound27Exact.agda
grep -q '10.1007/BF02547354' "$reality"
grep -q '10.1090/chel/343' "$reality"
grep -q 'realityInvolutionInvolutive' "$reality"
grep -q 'fourierRealityGivesFixedPoint' "$reality"
grep -q 'fixedPointGivesFourierReality' "$reality"
grep -q 'equivariantVectorFieldPreservesReality' "$reality"
grep -q 'diagonalFieldEquivariant' "$reality"
grep -q 'fullPhysicalGalerkinVectorFieldEquivarianceClosed = false' "$reality"

commutator=DASHI/Physics/Closure/NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact.agda
grep -q '10.1017/CBO9780511626265' "$commutator"
grep -q 'FourierStateCarrier' "$commutator"
grep -q 'MultiplierDualCarrier' "$commutator"
grep -q 'translationMultiplierCommutatorExact' "$commutator"
grep -q 'signedDifferenceCommutator' "$commutator"
grep -q 'finitePairingAppend' "$commutator"
grep -q 'cutoffUniformSignedOperatorTaxClosed = false' "$commutator"

probe=DASHI/Physics/Closure/NSTriadKNCentredFiveSourceProbeRound27Exact.agda
grep -q 'centredFiveSourceProbeIdentity' "$probe"
grep -q 'uniformWeightsIgnoreCentredDefect' "$probe"
grep -q 'five \* weightedSourceProbe' "$probe"

core=DASHI/Physics/Closure/NSTriadKNMaximalUniformViscosityCoreRound27Exact.agda
grep -q 'UniformViscosityCoreDecomposition' "$core"
grep -q 'candidateCoreBelowEveryOwner' "$core"
grep -q 'canonicalCoreEqualsPinnedAllocation' "$core"
grep -q 'maximalUniformCoreDominatesEveryCandidate' "$core"
grep -q 'physicalOwnerAllocationsInstantiated = false' "$core"
grep -q 'strictRationalViscosityMarginClosed = false' "$core"

plucker=DASHI/Physics/Closure/NSTriadKNPhysicalTriadPluckerInvariantRound27Exact.agda
grep -q '10.1512/iumj.1993.42.42034' "$plucker"
grep -q 'pluckerGramIdentity' "$plucker"
grep -q 'pluckerSwapPreservesSquaredArea' "$plucker"
grep -q 'PhysicalTriadPlaneInvariant' "$plucker"

integration=DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound27Exact.agda
grep -q 'Round27ExactEvidence' "$integration"
grep -q 'shellProjectorsResolveFiniteCarrier' "$integration"
grep -q 'signedTranslationMultiplierCommutator' "$integration"
grep -q 'maximalUniformViscosityCore' "$integration"
grep -q 'physicalTriadGramIdentity' "$integration"
grep -q 'uniformSignedOperatorTaxStillOpen' "$integration"
grep -q 'strictMarginStillOpen' "$integration"
grep -q 'clayPromotionStillFalse' "$integration"

paper=DASHI/Papers/NavierStokes/ProjectorOperatorCoreRound27.agda
grep -q 'canonicalProjectorOperatorCoreRound27Status' "$paper"
grep -q 'finiteProjectorOperatorCoreAdvanced' "$paper"
grep -q 'signedCommutatorAdvanced' "$paper"
grep -q 'maximalCoreAdvanced' "$paper"
grep -q 'physicalVectorFieldStillOpen' "$paper"
grep -q 'uniformOperatorTaxStillOpen' "$paper"
grep -q 'clayPromotionStillFalse' "$paper"

current=DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound27.agda
grep -q 'canonicalCurrentNSPaperTheoremInterfaceRound27' "$current"
grep -q 'sharpFiniteShellProjectorsChecked' "$current"
grep -q 'signedTranslationMultiplierCommutatorChecked' "$current"
grep -q 'maximalUniformViscosityCoreChecked' "$current"
grep -q 'cutoffUniformOperatorTaxStillOpen' "$current"
grep -q 'currentRound27ClayPromotionFalse' "$current"

grep -q '\[projector/operator/core tranche\](projector-operator-core-round27.md)' docs/ns-clay-contract/README.md
grep -q '\[Back to the Clay-contract overview\](README.md)' docs/ns-clay-contract/projector-operator-core-round27.md
grep -q 'M3 — State/dual translation–multiplier commutator' docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
grep -q 'Maximal uniform viscosity core' docs/ns-clay-contract/architecture.puml

grep -q 'agent/ns-luo-projector-operator-core-round27' "$workflow"
grep -q 'check_ns_luo_projector_operator_core_round27.sh' "$workflow"
grep -q 'ns-round27-projector-operator-core-agda' "$workflow"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

python3 scripts/ns_round27_projector_operator_certificate.py \
  --radius 2 \
  --out "$tmpdir/ns-round27-projector-operator.json" \
  --agda-out "$tmpdir/NSTriadKNLuoRound27FiniteCertificateGenerated.agda"

cmp \
  DASHI/Physics/Closure/NSTriadKNLuoRound27FiniteCertificateGenerated.agda \
  "$tmpdir/NSTriadKNLuoRound27FiniteCertificateGenerated.agda"

python3 - "$tmpdir/ns-round27-projector-operator.json" <<'PY'
import json
import sys
from pathlib import Path

payload = json.loads(Path(sys.argv[1]).read_text())
assert payload['all_checks_passed'] is True
assert payload['mode_count'] == 125
assert payload['maximum_shell'] == 1
assert payload['projector_idempotence_checks'] == 250
assert payload['projector_disjointness_checks'] == 250
assert payload['projector_resolution_checks'] == 125
assert payload['commutator_cells_checked'] == 15625
assert payload['centred_probe_cases_checked'] == 3645
assert payload['plucker_pairs_checked'] == 15625
assert payload['maximal_uniform_core'] == 7
assert payload['uniform_core_candidates_checked'] == 8
assert payload['commutator_sha256'] == '2b91bd4a22e2c02b84551a901a3e89f414f6c5b6f18fc78a1cf0d985c22e0396'
PY

cp "$tmpdir/ns-round27-projector-operator.json" ns-round27-projector-operator.json

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoProjectorOperatorCoreRound27Validation.agda
