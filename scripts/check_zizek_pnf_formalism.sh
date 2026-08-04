#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Foundations/CantorDiagonalCore.agda
  DASHI/Combinatorics/MemeDiagonal.agda
  DASHI/Reasoning/ExceptionalAndNonAllClosure.agda
  DASHI/Geometry/TwistedCycleOrientationCover.agda
  DASHI/Reasoning/ParallaxHolonomyBridge.agda
  DASHI/Reasoning/SurplusChannelCore.agda
  DASHI/Reasoning/FaithfulRepetitionCore.agda
  DASHI/Reasoning/SFMVerifiedClaimPresentation.agda
  DASHI/Reasoning/TypedMemeCompiler.agda
  DASHI/Dynamics/LogisticDecimalPNFBridge.agda
  DASHI/Dynamics/PNFOperatorLocalityResolution.agda
  DASHI/Reasoning/PNFZizekOperator.agda
  DASHI/Reasoning/ZizekPNFSourceAtlas.agda
  DASHI/Reasoning/ZizekPNFRegression.agda
  DASHI/Reasoning/ZizekPNFEverything.agda
  DASHI/EverythingZizekPNFExtension.agda

  DASHI/Foundations/StageAtlasZeroToTwelve.agda
  DASHI/Foundations/JPlusOneScaleBridge.agda
  DASHI/Foundations/StageCantorScaleRecursion.agda
  DASHI/Reasoning/KantCriticalCompiler.agda
  DASHI/Reasoning/KantAntinomyCore.agda
  DASHI/Reasoning/KantPNFBridge.agda
  DASHI/Cognition/PNF/KantApperceptionLearningBridge.agda
  DASHI/Reasoning/KantCopjecSexuationBridge.agda
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

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "Kant/Lacan/Zizek/PNF tranche contains an explicit postulate or hole" >&2
  exit 1
fi

# Existing constructive mathematics and fail-closed boundaries.
grep -q 'cantorNotSurjective' DASHI/Foundations/CantorDiagonalCore.agda
grep -q 'neoNotEnumerated' DASHI/Combinatorics/MemeDiagonal.agda
grep -q 'noGlobalOrientationSection' DASHI/Geometry/TwistedCycleOrientationCover.agda
grep -q 'mobiusTransportFlipsOrientationSign' DASHI/Reasoning/ParallaxHolonomyBridge.agda
grep -q 'everyNonAllFieldIsPowerSetClaimed = false' DASHI/Reasoning/ExceptionalAndNonAllClosure.agda
grep -q 'strictCardinalityIncreaseClaimed' DASHI/Reasoning/SurplusChannelCore.agda

# Product-lane locality and irreversible resolution remain separately scoped.
grep -q 'disjointCoordinateUpdatesCommute' DASHI/Dynamics/PNFOperatorLocalityResolution.agda
grep -q 'nontrivialIdempotentProjectionNotInvolutive' DASHI/Dynamics/PNFOperatorLocalityResolution.agda
grep -q 'commutationImpliesMetricOrthogonality = false' DASHI/Dynamics/PNFOperatorLocalityResolution.agda
grep -q 'commutationImpliesSpectralIndependence = false' DASHI/Dynamics/PNFOperatorLocalityResolution.agda

# PNF, learning, trauma and hyperfabric integration must remain non-diagnostic.
grep -q 'record RelationalLearningTraumaHyperfabric' DASHI/Reasoning/PNFZizekOperator.agda
grep -q 'residualAutomaticallyProvesTrauma = false' DASHI/Reasoning/PNFZizekOperator.agda
grep -q 'stage9IsDefinitionallyCapitalism = false' DASHI/Reasoning/PNFZizekOperator.agda
grep -q 'stage11IsDefinitionallyMonster = false' DASHI/Reasoning/PNFZizekOperator.agda

# Kantian compiler and antinomy distinctions.
grep -q 'data KantCategory' DASHI/Reasoning/KantCriticalCompiler.agda
grep -q 'formallyValidEquivocationResult' DASHI/Reasoning/KantCriticalCompiler.agda
grep -q 'reflectiveJudgmentDirectlyPromotes = false' DASHI/Reasoning/KantCriticalCompiler.agda
grep -q 'mathematicalAndDynamicalResolutionsDistinguished = true' DASHI/Reasoning/KantAntinomyCore.agda
grep -q 'contradictionEqualsNoMeet = false' DASHI/Reasoning/KantPNFBridge.agda
grep -q 'failedSynthesisAutomaticallyMeansTrauma = false' DASHI/Cognition/PNF/KantApperceptionLearningBridge.agda

# Lacanian exact algebra and governed bridges.
grep -q 'rotateFourTimesIsIdentity' DASHI/Reasoning/LacanDiscourseMatheme.agda
grep -q 'rotate masterDiscourse = hystericDiscourse' DASHI/Reasoning/LacanDiscourseMatheme.agda
grep -q 'standardFourCyclePreservedClaimed = false' DASHI/Reasoning/LacanCapitalistDiscourseMutation.agda
grep -q 'supposedAuthorityIsNotVerified' DASHI/Reasoning/LacanSignifierSubjectCore.agda
grep -q 'driveEqualsDynamicalFixedPoint = false' DASHI/Reasoning/LacanFantasyDriveCore.agda
grep -q 'borromeanTopologicalLinkProved = false' DASHI/Reasoning/LacanRegisterSinthomeHyperfabric.agda
grep -q 'noMeetDefinitionallyReal = false' DASHI/Reasoning/LacanPNFBridge.agda
grep -q 'discoursePlacementProvesPoliticalEconomy = false' DASHI/Reasoning/LacanZizekIdeologyBridge.agda

# Stage 0..12, j-basis and Cantor recursion.
grep -q 'stage12OpensRelationAtNewScale' DASHI/Foundations/StageAtlasZeroToTwelve.agda
grep -q 'elevenJIsTenJPlusJ' DASHI/Foundations/JPlusOneScaleBridge.agda
grep -q 'twelveJIsTenJPlusTwoJ' DASHI/Foundations/JPlusOneScaleBridge.agda
grep -q 'moonshineCoefficientIsRepresentationPlusOne' DASHI/Foundations/JPlusOneScaleBridge.agda
grep -q 'modularJEqualsLocalJUnitClaimed = false' DASHI/Foundations/JPlusOneScaleBridge.agda
grep -q 'stageElevenEqualsAlephOne = false' DASHI/Foundations/StageCantorScaleRecursion.agda
grep -q 'record Stage012InterpretiveRow' DASHI/Reasoning/StageZeroToTwelveKantLacanZizekBridge.agda
grep -q 'stageTwelveEqualsSuccessfulAnalysis = false' DASHI/Reasoning/StageZeroToTwelveKantLacanZizekBridge.agda

# Decimal chart crossing must separate exact onset, rounded rational and stage lens.
grep -q 'three57NumeratorFactorisation' DASHI/Dynamics/LogisticDecimalPNFBridge.agda
grep -q 'exactOnsetEqualTo357Over100 = false' DASHI/Dynamics/LogisticDecimalPNFBridge.agda
grep -q 'stageLensCandidateOnly = true' DASHI/Dynamics/LogisticDecimalPNFBridge.agda

# SFM and meme presentation must keep authority visible.
grep -q 'record VerifiedMultiViewIntegrity' DASHI/Reasoning/SFMVerifiedClaimPresentation.agda
grep -q 'noRepresentationOutrunsSource = true' DASHI/Reasoning/SFMVerifiedClaimPresentation.agda
grep -q 'mythCanProve = false' DASHI/Reasoning/TypedMemeCompiler.agda

# Attribution requirements.
grep -q 'James Michael DuPont' DASHI/Reasoning/ZizekPNFSourceAtlas.agda
grep -q '10.1007/BF01020332' DASHI/Reasoning/ZizekPNFSourceAtlas.agda
grep -q '10.1016/S0303-2647(98)00035-5' DASHI/Reasoning/ZizekPNFSourceAtlas.agda
grep -q '10.7554/eLife.25224' DASHI/Reasoning/ZizekPNFSourceAtlas.agda
grep -q '10.1017/CBO9780511804649' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.1017/CBO9780511804656' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.3389/fpsyg.2016.01948' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.1112/blms/11.3.308' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.1007/BF01232032' DASHI/Reasoning/KantLacanSourceAtlas.agda
grep -q '10.1007/978-3-319-47533-2' DASHI/Reasoning/KantLacanSourceAtlas.agda

scripts/run_agda29_parallel_check.sh DASHI/EverythingKantLacanPNFExtension.agda
