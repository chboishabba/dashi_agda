#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/TwoChannelAllowanceCompositionExact.agda
  DASHI/Core/ProofCarryingFiniteSumEnclosureExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientOffCoreAllowanceBridgeExact.agda
  DASHI/Analysis/RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact.agda
  DASHI/Analysis/RiemannG2CertifiedFiniteNearEvaluationCompilerExact.agda
  DASHI/Analysis/RiemannG2MinimalNearBudgetFinalOffSlackCompilerExact.agda
  DASHI/Analysis/RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientOffChosenCutoffCompilerExact.agda
  DASHI/Analysis/RiemannG2WindowBudgetToTransportedNearUpperExact.agda
  DASHI/Analysis/RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact.agda
  DASHI/Analysis/RiemannG2TransportedChosenCutoffDirectCombinedAllowanceExact.agda
  DASHI/Analysis/RiemannG2WindowBudgetDirectCombinedOffAllowanceCompilerExact.agda
  DASHI/Analysis/RiemannG2TransportedDirectCombinedOffAnalyticCoreExact.agda
  DASHI/Analysis/RiemannG2WindowBudgetDirectCombinedOffAnalyticCoreExact.agda
  DASHI/Analysis/RiemannG2CertifiedFiniteNearDirectCombinedOffAnalyticCoreExact.agda
  DASHI/Analysis/RiemannG2FinalOffMinimalCutRegression.agda
  DASHI/Analysis/RiemannG2FreshSameTaperGammaEnvelopeCompilerExact.agda
  DASHI/Analysis/RiemannG2FreshSameTaperGammaEnvelopeRegression.agda
  DASHI/Analysis/RiemannG2FreshGammaEnvelopeAnalyticCoreExact.agda
  DASHI/Analysis/RiemannG2BudgetNormalizedAnalyticCoresExact.agda
  DASHI/Analysis/RiemannG2BudgetNormalizedFinalOrderTransportExact.agda
  DASHI/Analysis/RiemannG2UniformBudgetNormalizedHighProducerExact.agda
  DASHI/Analysis/RiemannG2LiteralResponseNormalizedAnalyticCoresExact.agda
  DASHI/Analysis/RiemannG2IndependentComplementMarginFinalExact.agda
  DASHI/Analysis/RiemannG2UniformIndependentComplementHighProducerExact.agda
  DASHI/Analysis/RiemannG2FinalSplitComplementOrderTransportCompilerExact.agda
  DASHI/Analysis/RiemannG2FinalPoleQuotientMinimalAnalyticCutExact.agda
  DASHI/Analysis/RiemannG2FinalPoleQuotientTwoPaymentCutExact.agda
  DASHI/Analysis/RiemannG2FinalPoleQuotientTwoPaymentCutRegression.agda
  DASHI/Analysis/RiemannG2FinalPoleQuotientAnalyticCoreExact.agda
  DASHI/Analysis/RiemannG2FinalPoleQuotientAnalyticCoreRegression.agda
  DASHI/Analysis/RiemannAristotleSharedCertificateREADME.agda
)

for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  for f in "${FILES[@]}"; do
    agda "$f"
  done
else
  echo "agda executable not present; trust scan only" >&2
fi
