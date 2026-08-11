#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# Run the full Round-38 tranche first; the cumulative validation root imports
# the owner-network module, so the Agda invocation below is not a disconnected
# receipt.
bash scripts/check_ns_residual_transport_owner_flow_round38.sh

files=(
  DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|\?|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

grep -q 'globalCancellationStepSavingExact' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
grep -q 'pathTaxSavingExact' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
grep -q 'pathTransferTotalNonnegative' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
grep -q 'pathCannotIncreasePositiveTax' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
grep -q 'physicalNineOwnerCancellationPathConstructed = false' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationNetworkRound38Exact.agda

echo "Round38 owner cancellation network checks passed"
