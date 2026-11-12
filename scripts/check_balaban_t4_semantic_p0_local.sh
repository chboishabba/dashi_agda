#!/usr/bin/env bash
# Local original-source Bałaban T4 semantic P0 validation.
# Agda remains authoritative. This does not rely on CI.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_balaban_t4_semantic_p0_exact.py
python3 scripts/check_balaban_t4_refined_wilson_exact.py
python3 scripts/check_balaban_t4_auxiliary_unit_brillouin.py

if ! command -v agda >/dev/null 2>&1; then
  echo 'BLOCKED: agda unavailable; rational smoke is NOT kernel acceptance.' >&2
  exit 2
fi

agda --version
for module in \
  DASHI/Physics/YangMills/BalabanClayT4LiteralSemanticSevenGeneratorTransportExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4SemanticFourRepresentativeQuadratureExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4OuterRankTwoPerAxisExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4OriginalEvaluatorFourOrbitEndpointSumsExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4LiteralFourOrbitErrorBudgetFoldExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4RefinedSineSquareRegularBoxesExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4RefinedWilsonSevenGeneratorExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4NaiveNormalizedSineSquareCounterexampleExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4LiteralScalarSyntaxContradictionExact.agda \
  DASHI/Physics/YangMills/BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact.agda
do
  echo "Checking literal-source Agda module: $module"
  agda -i . -l standard-library "$module"
done

echo 'AGDA KERNEL PASS for all twelve local semantic/refined P0 cut modules; source physical atoms, seven scalar equalities, physical denominator and quadrature receipts remain OPEN.'
