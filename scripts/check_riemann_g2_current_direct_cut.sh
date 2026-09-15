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

# R1 archaeology regression: keep the representation wall split into theorem-
# bearing same-object obligations.  Generic phase algebra/source-status receipts
# must not be mistaken for the actual pole-quotient realization or checked-scalar
# transport.
R1="DASHI/Analysis/RiemannG2FinalNearLiteralKernelExact.agda"
grep -q 'genericTargetGapCosineLawClosed' "$R1"
grep -q 'reflectionPairLiteralFormulaSourceOwned' "$R1"
grep -q 'actualUniversalPoleQuotientPhaseRealizationInhabited' "$R1"
grep -q 'checkedNearScalarBridgeInhabited' "$R1"
grep -q 'statusReceiptPaysR1Equality' "$R1"
grep -q 'actualUniversalPoleQuotientPhaseRealizationInhabitedIsFalse' "$R1"
grep -q 'checkedNearScalarBridgeInhabitedIsFalse' "$R1"
grep -q 'statusReceiptPaysR1EqualityIsFalse' "$R1"

# Pareto refinement: the two theorem-bearing R1 acquisition debts must be
# independently inhabitable.  R1a attaches the final Agda near response to the
# checked/imported scalar; R1b identifies that same scalar with the literal fold.
# The existing bundled bridge must remain compiler output from those two parts.
grep -q 'FinalNearCheckedScalarAttachment' "$R1"
grep -q 'CheckedScalarLiteralFoldIdentification' "$R1"
grep -q 'compileFinalNearCheckedScalarBridge' "$R1"
grep -q 'compileFinalNearRepresentationEqualityFromSplit' "$R1"

if command -v agda >/dev/null 2>&1; then
  echo "Agda: $(agda --version)"
  for f in "${FILES[@]}"; do
    echo "==> agda $f"
    agda "$f"
  done
else
  echo "agda executable not present; trust scan only" >&2
fi
