#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ProofCarryingFiniteSumEnclosureExact.agda
  DASHI/Analysis/RiemannG2LiteralComplementDirectTargetExact.agda
  DASHI/Analysis/RiemannG2FinalNearLiteralKernelExact.agda
  DASHI/Analysis/RiemannG2ConcreteCertificateFinalScalarBridgeExact.agda
  DASHI/Analysis/RiemannG2ConcreteScalarExecutionFrontierExact.agda
  DASHI/Analysis/RiemannG2FinalCarrierFiniteSumCertificateExact.agda
  DASHI/Analysis/RiemannG2DirectClusterResponseContradictionExact.agda
  DASHI/Analysis/RiemannG2CertifiedNearUpperClusterResponseCompilerExact.agda
  DASHI/Analysis/RiemannG2CertifiedClusterLowerEnvelopeCompilerExact.agda
  DASHI/Analysis/RiemannG2FinalPoleNearObserverRefinementExact.agda
  DASHI/Analysis/RiemannG2LiteralPhaseDirectClusterResponseExact.agda
  DASHI/Analysis/RiemannG2MinimalStrictResponseConsumerExact.agda
  DASHI/Analysis/RiemannG2UniformLiteralPhaseHighProducerExact.agda
  DASHI/Analysis/RiemannG2UniformHighContradictionExact.agda
  DASHI/Analysis/RiemannG2UniformCertifiedNearUpperHighProducerExact.agda
  DASHI/Analysis/RiemannPlattTrudgianCanonicalLowRegionExact.agda
  DASHI/Analysis/RiemannCriticalLineStabilityRefinementExact.agda
  DASHI/Analysis/RiemannAnalyticCoordinateTerminalRefinementExact.agda
  DASHI/Analysis/RiemannG2ConstructiveNegativeRHCompletionExact.agda
  DASHI/Analysis/RiemannG2ClayTerminalOneLeafCutExact.agda
  DASHI/Analysis/RiemannG2ClayTerminalGenericHighCoordinateExact.agda
  DASHI/Analysis/RiemannG2CurrentDirectOneLeafFrontierExact.agda
  DASHI/Analysis/RiemannG2CurrentGenericHighFrontierRefinementExact.agda
  DASHI/Analysis/RiemannG2GenericHighCertifiedFollowupReadmeExact.agda
  DASHI/Analysis/RiemannG2FinalCutIntrospectionExact.agda
  DASHI/Analysis/Everything.agda
)

for f in "${FILES[@]}"; do
  test -f "$f"
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

R1="DASHI/Analysis/RiemannG2FinalNearLiteralKernelExact.agda"

# Existing fail-closed R1 archaeology surface.
grep -q 'genericTargetGapCosineLawClosed' "$R1"
grep -q 'reflectionPairLiteralFormulaSourceOwned' "$R1"
grep -q 'actualUniversalPoleQuotientPhaseRealizationInhabited' "$R1"
grep -q 'checkedNearScalarBridgeInhabited' "$R1"
grep -q 'statusReceiptPaysR1Equality' "$R1"
grep -q 'actualUniversalPoleQuotientPhaseRealizationInhabitedIsFalse' "$R1"
grep -q 'checkedNearScalarBridgeInhabitedIsFalse' "$R1"
grep -q 'statusReceiptPaysR1EqualityIsFalse' "$R1"

# R1a/R1b must be separately inhabitable theorem obligations.
grep -q 'FinalNearCheckedScalarAttachment' "$R1"
grep -q 'CheckedScalarLiteralFoldIdentification' "$R1"
grep -q 'compileFinalNearCheckedScalarBridge' "$R1"
grep -q 'compileFinalNearRepresentationEqualityFromSplit' "$R1"

# R1b is itself two source-shaped payments: the checked scalar must first be
# identified with the literal reflection-pair scalar on the final pole-quotient
# carrier, and only then must that SAME scalar be identified with the finite fold.
grep -q 'CheckedScalarLiteralReflectionPairIdentification' "$R1"
grep -q 'LiteralReflectionPairFiniteFoldIdentification' "$R1"
grep -q 'compileCheckedScalarLiteralFoldIdentificationFromReflectionPairSplit' "$R1"
grep -q 'r1b1CheckedScalarReflectionPairIdentificationInhabited' "$R1"
grep -q 'r1b1CheckedScalarReflectionPairIdentificationInhabitedIsFalse' "$R1"
grep -q 'r1b2ReflectionPairFiniteFoldIdentificationInhabited' "$R1"
grep -q 'r1b2ReflectionPairFiniteFoldIdentificationInhabitedIsFalse' "$R1"

# Source/status audit must fail-close every independently payable representation
# edge. A future recovery may pay R1a, R1b1, or R1b2 separately.
grep -q 'r1aCheckedScalarAttachmentInhabited' "$R1"
grep -q 'r1aCheckedScalarAttachmentInhabitedIsFalse' "$R1"
grep -q 'r1bLiteralFoldIdentificationInhabited' "$R1"
grep -q 'r1bLiteralFoldIdentificationInhabitedIsFalse' "$R1"

if command -v agda >/dev/null 2>&1; then
  echo "Agda: $(agda --version)"
  for f in "${FILES[@]}"; do
    echo "==> agda $f"
    agda "$f"
  done
else
  echo "agda executable not present; trust scan only" >&2
fi
