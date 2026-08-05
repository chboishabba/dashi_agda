#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanClayLowerBoundCountermodelExact.agda
  DASHI/Physics/YangMills/BalabanClayTransferGapDefectTelescopingExact.agda
  DASHI/Physics/YangMills/BalabanClayPhysicalScaleExponentExact.agda
  DASHI/Physics/YangMills/BalabanClayUniformPerronContractionExact.agda
  DASHI/Physics/YangMills/BalabanClayNormingFamilyOperatorBoundExact.agda
  DASHI/Physics/YangMills/BalabanClayTransferHamiltonianGapSeparationExact.agda
  DASHI/Physics/YangMills/BalabanClayExactOSPullbackRecombinationExact.agda
  DASHI/Physics/YangMills/BalabanClayDenseCoreSpectralGapExact.agda
  DASHI/Physics/YangMills/BalabanClayLocalNoncollapseExact.agda
  DASHI/Physics/YangMills/BalabanClayObservableGapEdgeExact.agda
  DASHI/Physics/YangMills/BalabanClaySpectralUVCompatibilityExact.agda
  DASHI/Physics/YangMills/BalabanClayMassGapGatePackageExact.agda
  DASHI/Physics/YangMills/BalabanClayMirShabirScopeAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayExternalAttemptStressTestsExact.agda
  DASHI/Physics/YangMills/BalabanP33InverseDexpReducedOperatorExact.agda
  DASHI/Physics/YangMills/BalabanP33GroupProductDistanceTelescopingExact.agda
  DASHI/Physics/YangMills/BalabanP33SecondChartRadiusCalibrationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound15Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

validation_root="DASHI/Physics/YangMills/BalabanClayHighestAlphaRound15Validation.agda"

# Build the complete repository-local import closure from module declarations,
# rather than scanning only the newly listed files.  Imports supplied by the
# Agda installation rather than the repository are reported but are outside
# this repository-local safety scan.
mapfile -t closure_files < <(
  python3 - "$validation_root" <<'PY'
from collections import deque
from pathlib import Path
import re
import sys

root_path = Path(sys.argv[1])
module_re = re.compile(r'^\s*module\s+([A-Za-z0-9_.]+)\b', re.MULTILINE)
import_re = re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)\b', re.MULTILINE)

index = {}
for path in Path('.').rglob('*.agda'):
    if any(part in {'.git', '.direnv', '_build'} for part in path.parts):
        continue
    text = path.read_text(encoding='utf-8', errors='replace')
    match = module_re.search(text)
    if match and match.group(1) not in index:
        index[match.group(1)] = path

root_text = root_path.read_text(encoding='utf-8', errors='replace')
root_match = module_re.search(root_text)
if not root_match:
    raise SystemExit(f'cannot read module declaration from {root_path}')

queue = deque([root_match.group(1)])
seen_modules = set()
seen_paths = set()
unresolved = set()

while queue:
    module = queue.popleft()
    if module in seen_modules:
        continue
    seen_modules.add(module)
    path = index.get(module)
    if path is None:
        unresolved.add(module)
        continue
    seen_paths.add(path)
    text = path.read_text(encoding='utf-8', errors='replace')
    for imported in import_re.findall(text):
        if imported not in seen_modules:
            queue.append(imported)

for module in sorted(unresolved):
    print(f'round15 import supplied outside repository index: {module}', file=sys.stderr)
for path in sorted(seen_paths, key=lambda p: str(p)):
    print(path)
PY
)

if ((${#closure_files[@]} == 0)); then
  echo "failed to construct the round-fifteen import closure" >&2
  exit 1
fi

python3 - "${closure_files[@]}" <<'PY'
from pathlib import Path
import re
import sys

postulate_pattern = re.compile(r'(^|\s)postulate(\s|$)')
unsafe_patterns = {
    'left hole': re.compile(r'\{!'),
    'right hole': re.compile(r'!\}'),
    'TERMINATING': re.compile(r'(^|\s)TERMINATING(\s|$)'),
    'NO_TERMINATION_CHECK': re.compile(r'(^|\s)NO_TERMINATION_CHECK(\s|$)'),
    'allow-unsolved-metas': re.compile(r'allow-unsolved-metas'),
    '--no-positivity-check': re.compile(r'--no-positivity-check'),
    '--no-termination-check': re.compile(r'--no-termination-check'),
    'NON_COVERING': re.compile(r'(^|\s)NON_COVERING(\s|$)'),
    '--type-in-type': re.compile(r'--type-in-type'),
    'trustMe': re.compile(r'\btrustMe\b'),
    'primTrustMe': re.compile(r'\bprimTrustMe\b'),
}

failed = False
authority_files = []
for name in sys.argv[1:]:
    path = Path(name)
    text = path.read_text(encoding='utf-8', errors='replace')
    postulates = list(postulate_pattern.finditer(text))
    if postulates:
        declared_authority = (
            path.name.endswith('Axioms.agda')
            and 'authority boundary' in text[:5000].lower()
        )
        if declared_authority:
            authority_files.append((path, len(postulates)))
        else:
            for match in postulates:
                line = text.count('\n', 0, match.start()) + 1
                print(f'{path}:{line}: undeclared postulate in validation closure', file=sys.stderr)
                failed = True
    for label, pattern in unsafe_patterns.items():
        for match in pattern.finditer(text):
            line = text.count('\n', 0, match.start()) + 1
            print(f'{path}:{line}: forbidden {label}', file=sys.stderr)
            failed = True

for path, count in authority_files:
    print(f'round15 declared authority boundary: {path} ({count} postulate block(s))', file=sys.stderr)

if failed:
    raise SystemExit(1)
PY

checks=(
  'BalabanClayLowerBoundCountermodelExact.agda:factorMismatchCountermodel'
  'BalabanClayTransferGapDefectTelescopingExact.agda:finiteDefectChainTelescopes'
  'BalabanClayTransferGapDefectTelescopingExact.agda:summabilityWithoutStrictBudgetCounterexample'
  'BalabanClayPhysicalScaleExponentExact.agda:physicalMassScaleBridge'
  'BalabanClayPhysicalScaleExponentExact.agda:latticeEnvelopeImpliesPhysicalEnvelope'
  'BalabanClayUniformPerronContractionExact.agda:noUniformDiameterBound'
  'BalabanClayNormingFamilyOperatorBoundExact.agda:oneObservableDoesNotControlOperatorNorm'
  'BalabanClayTransferHamiltonianGapSeparationExact.agda:positiveTransferGapRequiresExplicitPhysicalConversion'
  'BalabanClayExactOSPullbackRecombinationExact.agda:exactPullbackPreservesReflectionPositivity'
  'BalabanClayExactOSPullbackRecombinationExact.agda:negativePairDoesNotRecombinePositively'
  'BalabanClayDenseCoreSpectralGapExact.agda:denseLocalClusteringImpliesGap'
  'BalabanClayLocalNoncollapseExact.agda:localPositiveOSNormForcesNonzeroVector'
  'BalabanClayObservableGapEdgeExact.agda:observableGapEdgeDetection'
  'BalabanClaySpectralUVCompatibilityExact.agda:assembleSpectralUVCompatibility'
  'BalabanClayMassGapGatePackageExact.agda:assembleMandatoryClayMassGapGates'
  'BalabanClayMirShabirScopeAuditExact.agda:part2TransportReadingDoesNotSelfPromote'
  'BalabanClayExternalAttemptStressTestsExact.agda:finiteConeDiameterDoesNotGiveUniformDiameter'
  'BalabanP33InverseDexpReducedOperatorExact.agda:inverseDexpActsAsTwoSidedInverse'
  'BalabanP33GroupProductDistanceTelescopingExact.agda:productDistanceTelescoping'
  'BalabanP33SecondChartRadiusCalibrationExact.agda:secondChartEnvelopeFitsDiagonalAllocationExactly'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Source ownership must travel with every imported theorem boundary.
grep -q '10.4007/annals.2010.171.1707' \
  DASHI/Physics/YangMills/BalabanClayUniformPerronContractionExact.agda
grep -q '10.1142/S0219887826501136' \
  DASHI/Physics/YangMills/BalabanClayTransferGapDefectTelescopingExact.agda
grep -q '10.1007/BF01645738' \
  DASHI/Physics/YangMills/BalabanClayExactOSPullbackRecombinationExact.agda
grep -q '10.1103/PhysRevLett.30.1343' \
  DASHI/Physics/YangMills/BalabanClaySpectralUVCompatibilityExact.agda
grep -q '10.1002/prop.70097' \
  DASHI/Physics/YangMills/BalabanClayMirShabirScopeAuditExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33InverseDexpReducedOperatorExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33GroupProductDistanceTelescopingExact.agda

scripts/run_agda29_parallel_check.sh \
  "$validation_root"
