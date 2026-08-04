#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

new_files=(
  DASHI/Foundations/StageAtlasZeroToTwelve.agda
  DASHI/Foundations/StageZeroToTwelveTransitionCore.agda
  DASHI/Foundations/JPlusOneScaleBridge.agda
  DASHI/Foundations/StageCantorScaleRecursion.agda
  DASHI/Reasoning/KantCriticalCompiler.agda
  DASHI/Reasoning/KantAntinomyCore.agda
  DASHI/Reasoning/KantPNFBridge.agda
  DASHI/Reasoning/KantCopjecSexuationBridge.agda
  DASHI/Reasoning/KantZizekTranscendentalIllusionBridge.agda
  DASHI/Cognition/PNF/KantApperceptionLearningBridge.agda
  DASHI/Reasoning/LacanSignifierSubjectCore.agda
  DASHI/Reasoning/LacanDiscourseMatheme.agda
  DASHI/Reasoning/LacanCapitalistDiscourseMutation.agda
  DASHI/Reasoning/LacanFantasyDriveCore.agda
  DASHI/Reasoning/LacanRegisterSinthomeHyperfabric.agda
  DASHI/Reasoning/LacanPNFBridge.agda
  DASHI/Reasoning/LacanZizekIdeologyBridge.agda
  DASHI/Reasoning/KantLacanZizekRuntime.agda
  DASHI/Reasoning/StageZeroToTwelveKantLacanZizekBridge.agda
  DASHI/Reasoning/KantLacanSourceAtlas.agda
  DASHI/Reasoning/KantLacanRegression.agda
  DASHI/Reasoning/KantLacanEverything.agda
  DASHI/EverythingKantLacanPNFExtension.agda
)

for file in "${new_files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${new_files[@]}"; then
  echo "Kant/Lacan extension contains an explicit postulate or hole" >&2
  exit 1
fi

grep -q 'stage12ReachedByNumeralAlone = false' DASHI/Foundations/StageZeroToTwelveTransitionCore.agda
grep -q 'existingDecimalAddressCarrierReused = true' DASHI/Foundations/JPlusOneScaleBridge.agda
grep -q 'stageElevenEqualsAlephOne = false' DASHI/Foundations/StageCantorScaleRecursion.agda
grep -q 'reflectiveJudgmentDirectlyPromotes = false' DASHI/Reasoning/KantCriticalCompiler.agda
grep -q 'mathematicalAndDynamicalResolutionsDistinguished = true' DASHI/Reasoning/KantAntinomyCore.agda
grep -q 'directBridgeAvailable = true' DASHI/Reasoning/KantZizekTranscendentalIllusionBridge.agda
grep -q 'regulativeIdealProvesBigOtherExists = false' DASHI/Reasoning/KantZizekTranscendentalIllusionBridge.agda
grep -q 'rotateFourTimesIsIdentity' DASHI/Reasoning/LacanDiscourseMatheme.agda
grep -q 'standardFourCyclePreservedClaimed = false' DASHI/Reasoning/LacanCapitalistDiscourseMutation.agda
grep -q 'borromeanTopologicalLinkProved = false' DASHI/Reasoning/LacanRegisterSinthomeHyperfabric.agda
grep -q 'stageTwelveEqualsSuccessfulAnalysis = false' DASHI/Reasoning/StageZeroToTwelveKantLacanZizekBridge.agda

grep -q '10.1017/CBO9780511804649' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.3389/fpsyg.2016.01948' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.1112/blms/11.3.308' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.1007/BF01232032' DASHI/Reasoning/KantLacanSourceAtlas.agda

bash scripts/check_zizek_pnf_formalism.sh
