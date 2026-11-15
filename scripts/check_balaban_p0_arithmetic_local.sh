#!/usr/bin/env bash
# Authoritative LOCAL Agda check; CI is deliberately not required.
# Run from a Nix shell exposing the repository's pinned Agda/stdlib.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v agda >/dev/null 2>&1; then
  printf '%s\n' "BLOCKED: local agda executable not found; source-written != kernel-accepted" >&2
  exit 2
fi
agda --version

# Kernel check in dependency order; stop at FIRST precise type error.
modules=(
  BalabanLiteralEightCornerReassociationExact
  BalabanLiteralHullScalarExtremaExact
  BalabanLiteralLeftNestedHullExtremaExact
  BalabanLiteralRightNestedHullExtremaExact
  BalabanLiteralNestedHullAssociativityCutExact
  BalabanLiteralNestedHullAssociativityClosedExact
  BalabanLiteralProofIrrelevantIntervalBackendExact
  BalabanLiteralPositiveDivisionNumeratorCongruenceExact
  BalabanLiteralTotalRationalBackendExact
  BalabanLiteralSelectedTotalExpressionTypedDerivationExact
  BalabanLiteralRecursivePositiveDivisionCompilerExact
  BalabanLiteralBishopPositiveExpressionCompilerExact
  BalabanLiteralRecursiveDivisionPositiveNegativeControlExact
  BalabanLiteralRankAwareDenominatorRationalBoundsExact
  BalabanLiteralOriginalGridDenominatorMaskExact
  BalabanLiteralSevenGeneratorScalarAtomCertificatesExact
  BalabanCMP109TensorCovarianceScalarBoundaryExact
)
for name in "${modules[@]}"; do
  path="DASHI/Physics/YangMills/${name}.agda"
  printf '\n=== Agda local: %s ===\n' "$path"
  agda -i . -l standard-library "$path"
done
printf '%s\n' "LOCAL KERNEL PASS: new arithmetic/semantics modules only."
printf '%s\n' "Physical Wilson/ghost/Haar source, B4 covariance and quadrature receipts require independent admission."
