#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

# Retain every prior Round-42 guard first.
bash scripts/check_yang_mills_clay_highest_alpha_round42.sh

validation_root="DASHI/Physics/YangMills/BalabanClayHighestAlphaRound42MasterReconciledValidation.agda"

files=(
  DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
  DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
  DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRationalInjectiveInverseExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundFiniteRationalReopeningExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugePerturbationActionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualActionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
  DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
  DASHI/Physics/YangMills/BalabanBlockAnchoredGaugeAverageCompatibilityExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedMultiplierSplitExact.agda
  DASHI/Physics/YangMills/BalabanFiniteSelectorL2DefinitenessExact.agda
  DASHI/Physics/YangMills/BalabanSelectedReducedCombinedConstraintFloorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedReducedCombinedAdjointInjectiveExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRGTotalCovarianceExact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

unsafe_regex='(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|functionExtensionality|funext'

# Direct changed-file guard.
if grep -nE "$unsafe_regex" "${files[@]}"; then
  echo "round 42 extension contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

# Transitive import guard.  The previous checker only scanned the explicit
# changed-file list.  Discover every in-repository .agda module reachable from
# the cumulative validation root and apply the same unsafe policy before Agda
# is invoked.  Missing external/stdlib modules are ignored here and remain the
# responsibility of the pinned Agda toolchain.
python3 - "$validation_root" <<'PY'
from __future__ import annotations

import pathlib
import re
import sys

root = pathlib.Path('.').resolve()
start = pathlib.Path(sys.argv[1])
import_re = re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)', re.M)
unsafe_re = re.compile(
    r'(^|\s)postulate(\s|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|'
    r'allow-unsolved-metas|--no-positivity-check|--no-termination-check|'
    r'NON_COVERING|--type-in-type|trustMe|primTrustMe|'
    r'functionExtensionality|\bfunext\b'
)

seen: set[pathlib.Path] = set()
pending = [start]
violations: list[tuple[pathlib.Path, int, str]] = []

while pending:
    path = pending.pop()
    if path in seen:
        continue
    if not path.is_file():
        continue
    seen.add(path)
    text = path.read_text(encoding='utf-8')
    for number, line in enumerate(text.splitlines(), 1):
        if unsafe_re.search(line):
            violations.append((path, number, line))
    for module in import_re.findall(text):
        candidate = pathlib.Path(*module.split('.')).with_suffix('.agda')
        if candidate.is_file() and candidate not in seen:
            pending.append(candidate)

print(f"round42 transitive Agda dependency files: {len(seen)}")
if violations:
    for path, number, line in violations:
        print(f"{path}:{number}:{line}", file=sys.stderr)
    print("unsafe construct found in transitive Round-42 validation dependency graph", file=sys.stderr)
    raise SystemExit(1)
PY

grep -q 'applyComposeRectangularExact' DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
grep -q 'rectangularAdjointExact' DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
grep -q 'transposeProductColumnMassBound' DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
grep -q 'selectedGaugeGramPerturbationAbsoluteColumnMassBound' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
grep -q 'selectedBackgroundFlatGreenPerturbationColumnOneTenthContraction' DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
grep -q 'applyKernelL1Bound' DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
grep -q 'selectedBackgroundResidualPowerL1Decay' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
grep -q 'selectedBackgroundWeightedGreenPerturbationColumnOneSixthContraction' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
grep -q 'selectedBackgroundWeightedResidualPowerL1Decay' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
grep -q 'oneSixthReopeningBound' DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
grep -q 'oneSixthHomogeneousReopeningPointwiseZero' DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
grep -q 'selectedBackgroundResidualIdentityPlusInjective' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
grep -q 'selectedBackgroundWeightedResidualReopeningSixFifths' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
grep -q 'finiteSquareInjectiveImpliesRationalInverse' DASHI/Physics/YangMills/BalabanFiniteRationalInjectiveInverseExact.agda
grep -q 'selectedResidualIdentityPlusMatrixInjective' DASHI/Physics/YangMills/BalabanSelectedBackgroundFiniteRationalReopeningExact.agda
grep -q 'selectedWeightedResidualInverseSixFifths' DASHI/Physics/YangMills/BalabanSelectedBackgroundFiniteRationalReopeningExact.agda
grep -q 'selectedGaugeGramPerturbationActsAsExplicitEA' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugePerturbationActionExact.agda
grep -q 'selectedResidualActsAsExplicitFlatGreenEA' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualActionExact.agda
grep -q 'flatGreenBackgroundFactorizationAsMatrix' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q 'selectedBackgroundGaugeGreenLeftInverse' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q 'selectedBackgroundGaugeGreenRightInverse' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q 'tiltedGreenColumnL1BelowThree' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
grep -q 'selectedBackgroundGaugeGreenExponentialDecay' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
grep -q 'rootedGaugeOrbitLift' DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
grep -q 'rootedGaugeRepresentativeUniqueInBasedOrbit' DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
grep -q 'blockAverageFixedByCoarseIdentityGauge' DASHI/Physics/YangMills/BalabanBlockAnchoredGaugeAverageCompatibilityExact.agda
grep -q 'selectedPhysicalTangentProjectorInKernel' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
grep -q 'selectedPhysicalTangentProjectorIdempotent' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
grep -q 'rawFlatRedundancyGramZero' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
grep -q 'rawCombinedFlatGramHasNoTwoSidedInverse' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
grep -q 'selectedFlatRawCombinedGramInverseImpossible' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact.agda
grep -q 'selectedCombinedReducedProjection' DASHI/Physics/YangMills/BalabanSelectedCombinedMultiplierSplitExact.agda
grep -q 'reopenReduceProjectionIdempotent' DASHI/Physics/YangMills/BalabanSelectedCombinedMultiplierSplitExact.agda
grep -q 'finiteSelectorNormZeroPointwise' DASHI/Physics/YangMills/BalabanFiniteSelectorL2DefinitenessExact.agda
grep -q 'selectedAverageFlatGaugeAdjointOrthogonal' DASHI/Physics/YangMills/BalabanSelectedReducedCombinedConstraintFloorExact.agda
grep -q 'selectedBackgroundReducedCombinedAdjointFloor' DASHI/Physics/YangMills/BalabanSelectedReducedCombinedConstraintFloorExact.agda
grep -q 'selectedReducedCombinedAdjointInjective' DASHI/Physics/YangMills/BalabanSelectedReducedCombinedAdjointInjectiveExact.agda
grep -q 'finiteRGObservableExpectationPreserved' DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda
grep -q 'finiteRGCompositeExpectationPreserved' DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda
grep -q 'finiteRGTotalCovariance' DASHI/Physics/YangMills/BalabanFiniteRGTotalCovarianceExact.agda
grep -q 'finiteRGTotalVariance' DASHI/Physics/YangMills/BalabanFiniteRGTotalCovarianceExact.agda

grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanSelectedCombinedMultiplierSplitExact.agda
grep -q '10.1007/BF01211042' DASHI/Physics/YangMills/BalabanSelectedReducedCombinedConstraintFloorExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanSelectedReducedCombinedAdjointInjectiveExact.agda
grep -q '10.1007/BF01211042' DASHI/Physics/YangMills/BalabanBlockAnchoredGaugeAverageCompatibilityExact.agda
grep -q 'math-ph/0505008' DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda
grep -q 'math-ph/0505008' DASHI/Physics/YangMills/BalabanFiniteRGTotalCovarianceExact.agda

scripts/run_agda29_parallel_check.sh "$validation_root"
