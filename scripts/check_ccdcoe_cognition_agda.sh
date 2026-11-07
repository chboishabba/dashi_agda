#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

modules=(
  DASHI/Cognition/CCDCOEMultiplexGraphCutCoreExact.agda
  DASHI/Cognition/CCDCOECognitiveMultiplexInvariantExact.agda
  DASHI/Cognition/CCDCOEFiveLayerCertifiedCutExact.agda
  DASHI/Cognition/CCDCOEQueryPNFEvidenceBridgeExact.agda
  DASHI/Cognition/CCDCOEPersonalHolonomyBoundaryExact.agda
  DASHI/Cognition/CCDCOECognitiveMultiplexInvariantRegression.agda
  DASHI/Cognition/CCDCOEMaxCutRegressionExact.agda
  DASHI/Cognition/CCDCOEP3TypedIntersectionalAxisExact.agda
  DASHI/Cognition/CCDCOEP3SituatedHistoryPNFExact.agda
  DASHI/Cognition/CCDCOEP3CausalTrialecticInteractionExact.agda
  DASHI/Cognition/CCDCOEP3SourcePowerEvidenceWeldExact.agda
  DASHI/Cognition/CCDCOEP3CausalTrialecticRegressionExact.agda
  DASHI/Cognition/CCDCOEP3ClimateGenealogyCaseExact.agda
  DASHI/Cognition/CCDCOEP3API1998PrimaryPlanExact.agda
  DASHI/Cognition/CCDCOEP3ClimateContestedAttributionExact.agda
  DASHI/Cognition/CCDCOEP3ClimateObservedActivityAndCorpusExact.agda
)
for file in "${modules[@]}"; do
  test -s "$file" || { echo "Missing owner: $file" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|[{][!]|[!][}]|TERMINATING|NO_TERMINATION_CHECK|--allow-unsolved-metas' "$file"; then
    echo "Rejected postulate/meta/termination bypass: $file" >&2
    exit 1
  fi
done

python3 scripts/check_ccdcoe_cognitive_multiplex.py
python3 scripts/check_ccdcoe_p3_causal_trialectic.py
python3 scripts/check_ccdcoe_p3_climate_case.py

# The repo's canonical Agda 2.9 parallel checker owns compiler resolution,
# cache, resource guards and exact-head kernel receipts. No direct nix call.
# Its nonzero exit remains fatal. The source --safe option on the generic
# graph owner is enforced by Agda when this target is checked.
test -f scripts/run_agda29_parallel_check.sh || {
  echo "Canonical parallel_checker wrapper is missing; kernel verification OPEN" >&2
  exit 2
}

bash scripts/run_agda29_parallel_check.sh \
  "${modules[@]}" \
  DASHI/Cognition/Everything.agda

echo "CCDCOE max-cut: canonical parallel_checker accepted all focused owners and cognition aggregate"
