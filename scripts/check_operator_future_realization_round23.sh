#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_quantitative_future_geometry_round22.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Cognition/PNF/FutureSufficientInvariantSubspaceExact.agda
  DASHI/Cognition/PNF/FourierCommittorOperatorUnificationExact.agda
  DASHI/Cognition/PNF/SpectralResidualFutureDistortionExact.agda
  DASHI/Cognition/PNF/ControlledFutureSpectralRepresentationExact.agda
  DASHI/Cognition/PNF/GrokkingInvariantSubspaceSelectionExact.agda
  DASHI/Cognition/PNF/CanonicalFutureMinimalDynamicalRealizationExact.agda
  DASHI/Cognition/PNF/CanonicalFutureObservableAlgebraExact.agda
  DASHI/Cognition/PNF/FutureQuotientInvariantRealizationCompilerExact.agda
  DASHI/Cognition/PNF/OrientedZeroMinimalDynamicalRealizationExact.agda
  DASHI/EverythingOperatorFutureRealizationRound23.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -vE '^[[:space:]]*--' "$f" \
      | grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!!\}|--allow-unsolved-metas|primTrustMe'; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

# Invariant representation -> future safety.
grep -q 'runEncodingIntertwines' DASHI/Cognition/PNF/FutureSufficientInvariantSubspaceExact.agda
grep -q 'latentKernelImpliesTraceObservationEquality' DASHI/Cognition/PNF/FutureSufficientInvariantSubspaceExact.agda
grep -q 'invariantSufficientKernelIsFutureSafe' DASHI/Cognition/PNF/FutureSufficientInvariantSubspaceExact.agda
grep -q 'invariantRepresentationIsFutureLanguageSafeProjection' DASHI/Cognition/PNF/FutureSufficientInvariantSubspaceExact.agda

# Fourier/committor operator adaptation.
grep -q 'fourierCharacterIsOperatorAdapted' DASHI/Cognition/PNF/FourierCommittorOperatorUnificationExact.agda
grep -q 'committorIsOperatorAdapted' DASHI/Cognition/PNF/FourierCommittorOperatorUnificationExact.agda
grep -q '10.1021/j100540a008' DASHI/Cognition/PNF/FourierCommittorOperatorUnificationExact.agda

# Spectral residual future bound and controlled latent dynamics.
grep -q 'residualTraceNonIncreasing' DASHI/Cognition/PNF/SpectralResidualFutureDistortionExact.agda
grep -q 'futureDistortionBoundedByInitialResidual' DASHI/Cognition/PNF/SpectralResidualFutureDistortionExact.agda
grep -q 'certifiedModeDropControlsEveryFutureTrace' DASHI/Cognition/PNF/SpectralResidualFutureDistortionExact.agda
grep -q 'controlledTraceIntertwines' DASHI/Cognition/PNF/ControlledFutureSpectralRepresentationExact.agda
grep -q 'latentTargetAfterTraceImpliesFineTarget' DASHI/Cognition/PNF/ControlledFutureSpectralRepresentationExact.agda

# Grokking model selection by invariant task geometry.
grep -q 'candidateFitsTraining' DASHI/Cognition/PNF/GrokkingInvariantSubspaceSelectionExact.agda
grep -q 'characterIsMinimumDefectTrainingFit' DASHI/Cognition/PNF/GrokkingInvariantSubspaceSelectionExact.agda
grep -q 'zeroDefectSelectsCharacter' DASHI/Cognition/PNF/GrokkingInvariantSubspaceSelectionExact.agda

# Canonical quotient dynamics and quotient-order minimality.
grep -q 'futureEquivalentStepCongruence' DASHI/Cognition/PNF/CanonicalFutureMinimalDynamicalRealizationExact.agda
grep -q 'compileCanonicalQuotientDynamics' DASHI/Cognition/PNF/CanonicalFutureMinimalDynamicalRealizationExact.agda
grep -q 'canonicalEncodingCommutesWithTrace' DASHI/Cognition/PNF/CanonicalFutureMinimalDynamicalRealizationExact.agda
grep -q 'canonicalQuotientFactorsEverySectionedSafeRepresentation' DASHI/Cognition/PNF/CanonicalFutureMinimalDynamicalRealizationExact.agda
grep -q 'invariantRepresentationFactorsOntoCanonicalQuotient' DASHI/Cognition/PNF/CanonicalFutureMinimalDynamicalRealizationExact.agda

# Canonical future observable algebra / Koopman-like closure.
grep -q 'observableFactorsThroughCanonicalQuotient' DASHI/Cognition/PNF/CanonicalFutureObservableAlgebraExact.agda
grep -q 'liftAfterDescendRecoversFineObservable' DASHI/Cognition/PNF/CanonicalFutureObservableAlgebraExact.agda
grep -q 'descendAfterLiftRecoversQuotientObservable' DASHI/Cognition/PNF/CanonicalFutureObservableAlgebraExact.agda
grep -q 'actionPullback' DASHI/Cognition/PNF/CanonicalFutureObservableAlgebraExact.agda
grep -q 'finePullbackFactorsThroughQuotientPullback' DASHI/Cognition/PNF/CanonicalFutureObservableAlgebraExact.agda

# Finite compiler composition and oriented-zero regression.
grep -q 'compileInvariantFutureRealization' DASHI/Cognition/PNF/FutureQuotientInvariantRealizationCompilerExact.agda
grep -q 'stableRelationIffPresentedClass' DASHI/Cognition/PNF/FutureQuotientInvariantRealizationCompilerExact.agda
grep -q 'compiledStableDepthIsBounded' DASHI/Cognition/PNF/FutureQuotientInvariantRealizationCompilerExact.agda
grep -q 'waveQuotientStepIsFineStep' DASHI/Cognition/PNF/OrientedZeroMinimalDynamicalRealizationExact.agda
grep -q 'compiledWaveStillFindsDepthOne' DASHI/Cognition/PNF/OrientedZeroMinimalDynamicalRealizationExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingOperatorFutureRealizationRound23.agda
else
  echo "agda unavailable: structural/fail-closed round-23 scan completed; no kernel-clean claim"
fi
