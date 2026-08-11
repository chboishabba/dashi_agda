#!/usr/bin/env bash
set -euo pipefail

repo_root="${DASHI_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
cd "$repo_root"

files=(
  DASHI/Cognition/PNF/BoundedExecutionCarrier.agda
  DASHI/Cognition/PNF/ReopenableEvidenceFibre.agda
  DASHI/Cognition/PNF/ParserArgumentSupportGluing.agda
  DASHI/Cognition/PNF/EvidenceHorizon369.agda
  DASHI/Cognition/PNF/LexicalRetrievalProjection.agda
  DASHI/Cognition/PNF/SemanticSamplingLookupGeometry.agda
  DASHI/Cognition/PNF/TemporalRoleWorldAlignment.agda
  DASHI/Cognition/PNF/IdentityProofUtility.agda
  DASHI/Cognition/PNF/EvidenceClassificationEdge.agda
  DASHI/Cognition/PNF/InductiveDemandPreference.agda
  DASHI/Cognition/PNF/NumericOccurrenceFibre.agda
  DASHI/Cognition/PNF/PNFEvidenceHyperformalism.agda
  DASHI/Cognition/PNF/DirectDemandLookup.agda
  DASHI/Cognition/PNF/NumericPNFHyperfabricEverything.agda
)

for file in "${files[@]}"; do
  test -f "$file" || { echo "missing required file: $file" >&2; exit 1; }
done

# Fail closed on the trust escapes used by the other DASHI validation tranches.
if grep -nE '(postulate|\{!|!\}|\?($|[^A-Za-z0-9_])|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|--allow-unsolved-metas|--type-in-type|--with-K)' "${files[@]}"; then
  echo "unsafe or unfinished Agda construct found in ITIR reopenable-evidence tranche" >&2
  exit 1
fi

required_markers=(
  'executionOverflowHasNoSemanticPermission'
  'reopenExact'
  'supportAloneCannotCreateIdentity'
  'h9PresenceAloneCannotPromoteWorldIdentity'
  'regexHasNoSemanticAuthority'
  'queryCommutationIsClassicalNyquistTheoremIsFalse'
  'externalCandidateAloneCannotPromoteWorldIdentity'
  'identityProofDoesNotImplyFactorApplicability'
  'candidateClassificationCannotPromoteIdentity'
  'inductivePreferenceCannotProjectScalarIdentity'
  'sharedSurfaceDoesNotIdentifyOccurrences'
  'finiteReferenceDoesNotPromoteUniversalPQJ'
  'expectedConstantEqualityClaimRequiresContract'
)

for marker in "${required_markers[@]}"; do
  if ! grep -Rqs --include='*.agda' "$marker" DASHI/Cognition/PNF; then
    echo "missing required theorem/boundary marker: $marker" >&2
    exit 1
  fi
done

export AGDA_FLAKE="${AGDA_FLAKE:-github:agda/agda/86a1179c1f886da773dc53be920bcca5d876884e#debug.bin}"
export AGDA_JOBS="${AGDA_JOBS:-2}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/NumericPNFHyperfabricEverything.agda
