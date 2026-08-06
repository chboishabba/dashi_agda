#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# The round-six root is cumulative.  Validate and scan the complete repaired
# round-five tranche before checking the new terminal-geometry mathematics.
bash scripts/check_ns_luo_hard_math_round5.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEvenKernelCenteredTaylorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCenteredCommutatorBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCyclicTriadEnergyCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCancellationAbsoluteValueNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteAlignmentGramExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTraceFreeStretchCompressionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteStrainTransverseDecompositionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteMobiusOrientationObstructionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyCriticalScalingGapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteZenoCascadeBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCascadeEventCostExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalFarNearSplitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicHeatDampingExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicHeatKernelYoungExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyControlledFarTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteExponentialPolynomialAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNearWindowHalfKernelExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNearCenteredCommutatorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalFarNearBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoMitrovicDiagnosticIterationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSparseWeightAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeakStrongUniquenessExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTerminalGeometryRound6Validation.agda

  # Round-five files repaired on this head after static review.
  DASHI/Physics/Closure/NSTriadKNLuoFinitePhysicalSection4BudgetDerivationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSmoothHardMultiplierFactorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJ2HighHighGapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJ12CommutatorDerivativeGainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteProjectedShellEquation42Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourResidueBlockDecayExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ11HalfRangeDerivedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ12FiveShellExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ12CriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ1CriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ2CriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceSection4NonlinearExact.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoTerminalGeometryRound6Validation.agda
