#!/usr/bin/env bash
set -euo pipefail

repo_root="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
cd "$repo_root"

files=(
  DASHI/Cognition/PNF/SensibLawDirectionalEvidenceApplicabilityBridgeExact.agda
  DASHI/Cognition/PNF/SensibLawBrightonS185DirectionalApplicabilityRegressionExact.agda
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
  DASHI/Cognition/PNF/SensibLawBrightonProfessionalAdviceLineageExact.agda
  DASHI/Cognition/PNF/SensibLawBrightonProfessionalAdviceLineageValidation.agda
  DASHI/Cognition/PNF/SensibLawGriffithsDirectionalSupportAuthorityRegressionExact.agda
  DASHI/Interop/SensibLawGriffithsDirectionalSupportAuthorityRegressionValidation.agda
  DASHI/Interop/SensibLawNatSourceDiscoveryExact.agda
  DASHI/Interop/SensibLawNatSourceDiscoveryValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -nE '\{!|!\}|\bpostulate\b|\bTODO\b|\bFIXME\b|--allow-unsolved-metas|--allow-incomplete-matches' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

# The focused validation owner is intentionally required to expose the source
# payment boundary explicitly, not just the older applicability/violation flags.
grep -q 'exactSourceResidualRequired = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
grep -q 'exactTargetClaimBindingRequired = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
grep -q 'exactSourceArtifactReceiptRequired = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
grep -q 'supportedDispositionRequired = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
grep -q 'canonicalSourceAdmissionRequired = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
grep -q 'positiveSupportPaidByCanonicalAdmission = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda
grep -q 'positiveTritPaidByCanonicalAdmission = refl' \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda

grep -q 'professionalAdviceSeparateFromStatutoryBreachExact = refl' \
  DASHI/Cognition/PNF/SensibLawBrightonProfessionalAdviceLineageValidation.agda

grep -q 'presentCustodialMandateResidual' \
  DASHI/Cognition/PNF/SensibLawGriffithsDirectionalSupportAuthorityRegressionExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Interop/SensibLawDirectionalEvidenceApplicabilityBridgeValidation.agda \
  DASHI/Interop/SensibLawBrightonS185DirectionalApplicabilityRegressionValidation.agda \
  DASHI/Cognition/PNF/SensibLawBrightonProfessionalAdviceLineageValidation.agda \
  DASHI/Interop/SensibLawGriffithsDirectionalSupportAuthorityRegressionValidation.agda \
  DASHI/Interop/SensibLawNatSourceDiscoveryValidation.agda
