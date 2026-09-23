#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Moonshine/JInvariant369ConsolidatedNextStageExact.agda
JOINT=DASHI/Moonshine/JInvariant369JointFibredObserverExact.agda
SSP=DASHI/Moonshine/JInvariant369SSPLevelDihedralIntertwinerExact.agda
BIF=DASHI/Moonshine/JInvariant369JointFibreBifiltrationExact.agda
STAGE=DASHI/Foundations/StageTwelveGrothendieckRelationHyperformExact.agda
QUAL=DASHI/Moonshine/JInvariant369ZeroToThirteenTetralemmaQualificationExact.agda
ZETA=DASHI/Moonshine/JInvariant369Zeta6561MonsterCrosswalkExact.agda
TEN17=DASHI/Moonshine/JInvariant369TenRankSeventeenHyperformalismExact.agda

for file in "$OWNER" "$JOINT" "$SSP" "$BIF" "$STAGE" "$QUAL" "$ZETA" "$TEN17"; do
  [[ -f "$file" ]] || { echo "missing required source: $file" >&2; exit 1; }
done

grep -q 'record Consolidated369State' "$OWNER"
grep -q 'SignedLevel3Coherent' "$OWNER"
grep -q 'translateConsolidated' "$OWNER"
grep -q 'reflectConsolidatedFibreOnly' "$OWNER"
grep -q 'consolidatedLevelCannotFactorThroughBase' "$OWNER"
grep -q 'consolidatedMagnitudeCannotFactor' "$OWNER"
grep -q 'consolidatedMagnitudeRepair' "$OWNER"
grep -q 'noMagnitudePreservingSignedCycleLift' "$OWNER"
grep -q 'canonicalConsolidated369NextStageBoundary' "$OWNER"

grep -q 'canonicalJoint369DihedralLaw' "$JOINT"
grep -q 'sspCycleIntertwinesLevel3Translation' "$SSP"
grep -q 'sspAntipodeIntertwinesLevel3Inversion' "$SSP"
grep -q 'coarseningCommutesWithTranslation' "$BIF"
grep -q 'canonicalStageTwelveSiteSheafReceipt' "$STAGE"
grep -q 'rank12Address110' "$QUAL"
grep -q 'rank13Address111' "$QUAL"
grep -q 'stage4CarriesTetralemmaInterpolationRole' "$QUAL"
grep -q 'stage12OpensRelationAtScale' "$QUAL"
grep -q 'tetralemmaPreservesUnderlying27Carrier' "$QUAL"
grep -q 'sixfoldRetainsTetralemmaQualifiedCarrier' "$QUAL"
grep -q 'qualificationDoesNotRewriteConsolidatedState' "$QUAL"
grep -q 'rank13DoesNotInventStage13Semantics' "$QUAL"
grep -q 'sixFiveSixOneAsOnePlusSixFiveSixZero' "$ZETA"
grep -q 'regularMultiplicityIs65610' "$ZETA"
grep -q 'monster196883IsThreeTimes65610Plus53' "$ZETA"
grep -q 'atlasMonster6561Source' "$ZETA"
grep -q 'cyclotomicZetaDoesNotEqualRiemannZeta' "$ZETA"
grep -q 'd4FlipIntertwinesMacroComplement' "$TEN17"
grep -q 'rank14IsFirstAfterThreeBalancedDigitCapacity' "$TEN17"
grep -q 'rank14BalancedFourDigitWitness' "$TEN17"
grep -q 'rank17BalancedFourDigitWitness' "$TEN17"
grep -q 'rankPantsRoundTrip' "$TEN17"
grep -q 'stageTwelveRelationCountIs144' "$TEN17"
grep -q 'atlasProperImageDepthIsFourteen' "$TEN17"
grep -q 'atlasMaximalDepthIsSeventeen' "$TEN17"
grep -q 'signedMagnitudeStillDoesNotFactorThroughCoarseC3' "$TEN17"
grep -q 'decimalNotationDoesNotExplainTen' "$TEN17"

echo "J/369 consolidated next-stage static guards passed."

scripts/run_agda29_parallel_check.sh "$OWNER" "$QUAL" "$ZETA" "$TEN17"
