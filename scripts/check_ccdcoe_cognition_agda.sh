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
  DASHI/Cognition/CCDCOEP3CausalTrialecticInteractionExact.agda
  DASHI/Cognition/CCDCOEP3SourcePowerEvidenceWeldExact.agda
  DASHI/Cognition/CCDCOEP3CausalTrialecticRegressionExact.agda
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

# A real Agda executable is mandatory. Never substitute source scanning or
# Python enumeration for kernel verification.
command -v agda >/dev/null || {
  echo "Agda unavailable: structural tests pass, kernel verification OPEN" >&2
  exit 2
}

agda --safe -i . DASHI/Cognition/CCDCOEMultiplexGraphCutCoreExact.agda
for file in "${modules[@]}"; do
  agda -i . "$file"
done
agda -i . DASHI/Cognition/Everything.agda

echo "CCDCOE max-cut: all focused Agda owners and cognition aggregate accepted"
