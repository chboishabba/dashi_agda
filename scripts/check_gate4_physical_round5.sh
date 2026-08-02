#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

bash "$SCRIPT_DIR/check_gate4_physical_round4.sh"

FILES=(
  DASHI/Foundations/BishopElementaryTailEvidenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109RadiusOneSplitFibreExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109RadiusOneRepositoryTorusExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109RadiusOneWeightExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109MinimalContourFamilyExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109MinimalAveragedContourExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4CMP109MinimalEquation012Exact.agda
  DASHI/Physics/YangMills/BalabanClayGate4AlternatingTaylorEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SU2HalfRadiusFromSignedTailsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BishopSU2HalfRadiusInstantiationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SeriesLipschitzAssemblyExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4NewtonFourChannelQuarterExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4HalfContractionInvariantBallExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BalabanGaugeFixingProposition5Exact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeFixingProposition5ToHalfBallExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BackgroundFieldVariationalTheoremExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4RationalWilsonQuadraticSecondDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4QuadraticCompositionSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ConstraintProjectionSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalFunctionalSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4SandwichOperatorToFormBoundExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveSandwichChannelAssemblyExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4WilsonPlaquetteBadCubeBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4GaugeCubicTaylorRemainderSumExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4WeakeningProductSupportExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4ConnectedTreeDecayExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4BackgroundPropagatorDecayTheoremsExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DecayStepToDyadicShellExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DyadicGeometricRootedSummabilityExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4DyadicRandomWalkTailExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4FiveActivityTenthToHalfExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound5SourceTheoremLedger.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound5IntegratedExact.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound5Ledger.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound5Receipt.agda
  DASHI/Physics/YangMills/BalabanClayGate4PhysicalClosureRound5Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerPhysicalClosureRound5Advance.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSevenGroupAdvance.agda
)

for relative in "${FILES[@]}"; do
  file="$ROOT_DIR/$relative"
  [[ -f "$file" ]] || {
    echo "missing Gate-4 round-five file: $relative" >&2
    exit 1
  }

  if grep -nE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+[^[:space:]]*/' "$file"; then
    echo "malformed slash-separated Agda import in $relative" >&2
    exit 1
  fi

  if grep -nE '=[[:space:]]*(quarantined|verifiedLiterature)[[:space:]]*$' "$file"; then
    echo "obsolete ProofLevel constructor in $relative" >&2
    exit 1
  fi

  if grep -nE '\{!|!\}' "$file"; then
    echo "explicit Agda hole in $relative" >&2
    exit 1
  fi

  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)' "$file"; then
    echo "postulate introduced in $relative" >&2
    exit 1
  fi
done

exec "$SCRIPT_DIR/run_agda29_parallel_check.sh" "${FILES[@]}"
