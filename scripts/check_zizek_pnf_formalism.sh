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
  DASHI/Reasoning/PNFZizekOperator.agda
  DASHI/Reasoning/ZizekPNFSourceAtlas.agda
  DASHI/Reasoning/ZizekPNFRegression.agda
  DASHI/Reasoning/ZizekPNFEverything.agda
  DASHI/EverythingZizekPNFExtension.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "Zizek/PNF tranche contains an explicit postulate or hole" >&2
  exit 1
fi

# Exact mathematics and fail-closed boundaries.
grep -q 'cantorNotSurjective' DASHI/Foundations/CantorDiagonalCore.agda
grep -q 'neoNotEnumerated' DASHI/Combinatorics/MemeDiagonal.agda
grep -q 'noGlobalOrientationSection' DASHI/Geometry/TwistedCycleOrientationCover.agda
grep -q 'mobiusTransportFlipsOrientationSign' DASHI/Reasoning/ParallaxHolonomyBridge.agda
grep -q 'everyNonAllFieldIsPowerSetClaimed = false' DASHI/Reasoning/ExceptionalAndNonAllClosure.agda
grep -q 'strictCardinalityIncreaseClaimed' DASHI/Reasoning/SurplusChannelCore.agda

# PNF, learning, trauma and hyperfabric integration must remain non-diagnostic.
grep -q 'record RelationalLearningTraumaHyperfabric' DASHI/Reasoning/PNFZizekOperator.agda
grep -q 'residualAutomaticallyProvesTrauma = false' DASHI/Reasoning/PNFZizekOperator.agda
grep -q 'stage9IsDefinitionallyCapitalism = false' DASHI/Reasoning/PNFZizekOperator.agda
grep -q 'stage11IsDefinitionallyMonster = false' DASHI/Reasoning/PNFZizekOperator.agda

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

scripts/run_agda29_parallel_check.sh DASHI/EverythingZizekPNFExtension.agda
