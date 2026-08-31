#!/usr/bin/env bash
set -euo pipefail

ROOT="DASHI/Math2026ClaimAuditValidation.agda"
FILES=(
  DASHI/Analysis/DeBruijnNewman2026ClaimAuditExact.agda
  DASHI/Analysis/DeBruijnNewman2026SourceWeldExact.agda
  DASHI/Analysis/DeBruijnNewmanRiemannG2BridgeAuditExact.agda
  DASHI/Analysis/DeBruijnNewmanRiemannG2RiemannSiegelBridgeExact.agda
  DASHI/Analysis/RiemannG2ExplicitFormulaBridgeAuditExact.agda
  DASHI/Analysis/RiemannG2LiteralSpectralZeroWeldExact.agda
  DASHI/Analysis/RiemannG2BidiCutReconciliationExact.agda
  DASHI/Mathematics/NumberTheory/PrimeGap2026ClaimAuditExact.agda
  DASHI/Mathematics/NumberTheory/PrimeGap2026SourceAcquisitionExact.agda
  DASHI/Mathematics/NumberTheory/DiophantineTupleDPrimeSquare2026ClaimAuditExact.agda
  DASHI/Mathematics/NumberTheory/PrimePowerDiophantineTuple2026SourceExact.agda
  DASHI/Core/ExternalAutoformalizationProvenanceExact.agda
  DASHI/Core/SourceExactFrontierBidiCrossPollination2026.agda
  DASHI/Core/FrontierRelationStrengthBidiExact.agda
  DASHI/Core/FiniteCertificateConsumerBridgeExact.agda
  DASHI/Physics/YangMills/BalabanActiveSourceDiscriminator2026Exact.agda
  DASHI/Physics/Closure/NSCriticalConeAristotleRouteHypergraph2026Exact.agda
  "$ROOT"
)

if grep -nE '\b(postulate|{-# OPTIONS --allow-unsolved-metas #-}|\?|{!!})\b' "${FILES[@]}"; then
  echo "unsafe or incomplete proof surface found" >&2
  exit 1
fi

if command -v agda >/dev/null 2>&1; then
  agda -i . "$ROOT"
else
  echo "agda not available; trust scan only"
fi
