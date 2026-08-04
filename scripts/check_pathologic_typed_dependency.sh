#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bash scripts/check_kant_lacan_extension.sh

files=(
  DASHI/Core/TypedDependencyCore.agda
  DASHI/Foundations/MarkedUnitExtensionCore.agda
  DASHI/Foundations/JPlusOneMarkedUnitExtension.agda
  DASHI/Reasoning/TypedHyperfabricCore.agda
  DASHI/Reasoning/RSITypedDependencyHyperfabric.agda
  DASHI/Reasoning/SinthomeTypedStabilisation.agda
  DASHI/Reasoning/SinthomeFiniteWitness.agda
  DASHI/Reasoning/PNFTypedDependencyAdapters.agda
  DASHI/Reasoning/SFMVerificationDependency.agda
  DASHI/Reasoning/TypedDependencyUpgradeAtlas.agda
  DASHI/Reasoning/PathologicConstraintSystem.agda
  DASHI/Reasoning/PathologicPerspectiveHyperfabric.agda
  DASHI/Reasoning/PathologicTheatreMetaRuntime.agda
  DASHI/Reasoning/PathologicSourceAtlas.agda
  DASHI/Reasoning/PathologicRegression.agda
  DASHI/Reasoning/PathologicEverything.agda
  DASHI/EverythingPathologicTypedDependencyExtension.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "Pathologic/typed-dependency tranche contains an explicit postulate or hole" >&2
  exit 1
fi

# Typed dependency and hyperfabric upgrades.
grep -q 'record DependencyWitness' DASHI/Core/TypedDependencyCore.agda
grep -q 'record AdmissibleAction' DASHI/Core/TypedDependencyCore.agda
grep -q 'record IrreducibleTernaryDependency' DASHI/Core/TypedDependencyCore.agda
grep -q 'booleanProjectionReconstructsWitness = false' DASHI/Core/TypedDependencyCore.agda
grep -q 'record GlobalSection' DASHI/Reasoning/TypedHyperfabricCore.agda
grep -q 'globalSectionRequiresCompatibilityWitness = true' DASHI/Reasoning/TypedHyperfabricCore.agda
grep -q 'canonicalIrreducibleRSIDependency' DASHI/Reasoning/RSITypedDependencyHyperfabric.agda
grep -q 'topologicalBorromeanLinkProved = false' DASHI/Reasoning/RSITypedDependencyHyperfabric.agda
grep -q 'notEquivalentToErasure' DASHI/Reasoning/SinthomeTypedStabilisation.agda
grep -q 'minimalityAutomaticallyAvailable = false' DASHI/Reasoning/SinthomeTypedStabilisation.agda
grep -q 'canonicalFiniteSinthome' DASHI/Reasoning/SinthomeFiniteWitness.agda
grep -q 'finiteSinthomeNotErasure' DASHI/Reasoning/SinthomeFiniteWitness.agda
grep -q 'memoryUpdatePreservesEvent' DASHI/Reasoning/PNFTypedDependencyAdapters.agda
grep -q 'record TypedClosureGluing' DASHI/Reasoning/PNFTypedDependencyAdapters.agda
grep -q 'availabilityBooleanReconstructsSection = false' DASHI/Reasoning/PNFTypedDependencyAdapters.agda
grep -q 'record CheckedReceipt' DASHI/Reasoning/SFMVerificationDependency.agda
grep -q 'record CheckedTheoremCard' DASHI/Reasoning/SFMVerificationDependency.agda
grep -q 'targetVerifiedBooleanReconstructsReceipt = false' DASHI/Reasoning/SFMVerificationDependency.agda

# Marked unit extension and the corrected hyphen reading.
grep -q 'predecessorSubtractionRequired = false' DASHI/Foundations/MarkedUnitExtensionCore.agda
grep -q 'previousSubfibreHyphenParsedAsSubtraction = false' DASHI/Foundations/JPlusOneMarkedUnitExtension.agda
grep -q 'moonshineInternal196882SubrepresentationClaimed = false' DASHI/Foundations/JPlusOneMarkedUnitExtension.agda
grep -q 'stageAndMoonshineSharePlusOneShape' DASHI/Foundations/JPlusOneMarkedUnitExtension.agda

# Pathologic constraint, perspective and theatre surfaces.
grep -q 'record ActionDependency' DASHI/Reasoning/PathologicConstraintSystem.agda
grep -q 'dayTwoPriceMultiplierIsTen' DASHI/Reasoning/PathologicConstraintSystem.agda
grep -q 'everyUnpleasantMechanicIsIntentional = false' DASHI/Reasoning/PathologicConstraintSystem.agda
grep -q 'everyTechnicalDefectIsArtisticallyNecessary = false' DASHI/Reasoning/PathologicConstraintSystem.agda
grep -q 'data PerspectiveEvidence' DASHI/Reasoning/PathologicPerspectiveHyperfabric.agda
grep -q 'noCanonicalViewFromNowhere' DASHI/Reasoning/PathologicPerspectiveHyperfabric.agda
grep -q 'day12MapsToStage12' DASHI/Reasoning/PathologicPerspectiveHyperfabric.agda
grep -q 'comparisonIsNoTypedMeet' DASHI/Reasoning/PathologicPerspectiveHyperfabric.agda
grep -q 'record MutualPlayDependency' DASHI/Reasoning/PathologicTheatreMetaRuntime.agda
grep -q 'traceAfterReveal = causalTraceRetained' DASHI/Reasoning/PathologicTheatreMetaRuntime.agda
grep -q 'fictionalityImpliesMeaninglessness = false' DASHI/Reasoning/PathologicTheatreMetaRuntime.agda

# Upgrade atlas must state what is and is not migrated.
grep -q 'allLegacySitesAlreadyMigrated = false' DASHI/Reasoning/TypedDependencyUpgradeAtlas.agda
grep -q 'pathologicUpgrade' DASHI/Reasoning/TypedDependencyUpgradeAtlas.agda
grep -q 'verificationUpgrade' DASHI/Reasoning/TypedDependencyUpgradeAtlas.agda

# Attribution requirements.
grep -q 'Harris Brewis (hbomberguy)' DASHI/Reasoning/PathologicSourceAtlas.agda
grep -q '10.26503/todigra.v3i1.64' DASHI/Reasoning/PathologicSourceAtlas.agda
grep -q '10.1016/j.ruslit.2022.11.004' DASHI/Reasoning/PathologicSourceAtlas.agda
grep -q '10.48550/arXiv.2309.17116' DASHI/Reasoning/PathologicSourceAtlas.agda
grep -q '10.1080/14794713.2025.2555035' DASHI/Reasoning/PathologicSourceAtlas.agda
grep -q '10.5281/zenodo.17483228' DASHI/Reasoning/PathologicSourceAtlas.agda

scripts/run_agda29_parallel_check.sh DASHI/EverythingPathologicTypedDependencyExtension.agda
