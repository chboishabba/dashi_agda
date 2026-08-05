#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEvenKernelCenteredTaylorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCenteredCommutatorBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCyclicTriadEnergyCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCancellationAbsoluteValueNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteAlignmentGramExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTraceFreeStretchCompressionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteMobiusOrientationObstructionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyCriticalScalingGapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteZenoCascadeBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalFarNearSplitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicHeatDampingExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyControlledFarTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteExponentialPolynomialAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNearWindowHalfKernelExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNearCenteredCommutatorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoMitrovicDiagnosticIterationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSparseWeightAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeakStrongUniquenessExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTerminalGeometryRound6Validation.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePhysicalSection4BudgetDerivationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSmoothHardMultiplierFactorExact.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoTerminalGeometryRound6Validation.agda
