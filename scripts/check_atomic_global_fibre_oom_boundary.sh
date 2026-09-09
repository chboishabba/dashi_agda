#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CORE="DASHI/Core/AtomicGlobalFibreLiftExact.agda"
ALG="DASHI/Physics/YangMills/BalabanOpaqueGlobalAlgebraExact.agda"
VAR="DASHI/Physics/YangMills/BalabanPath4PhysicalVarianceDecompositionExact.agda"
POINCARE="DASHI/Physics/YangMills/BalabanPath4PhysicalComponentPoincareExact.agda"
PREP="DASHI/ComputerScience/AgdaProofDebtFibrePreparationExact.agda"
REL="DASHI/Physics/YangMills/BalabanFiniteSumRelationFibreLiftExact.agda"

for file in "$CORE" "$ALG" "$VAR" "$POINCARE" "$PREP" "$REL"; do
  test -f "$file" || { echo "missing boundary file: $file" >&2; exit 2; }
done

# The algebra leaf must remain carrier-free.  It is allowed to know only the
# scalar algebra required for already-observed coordinates.
if grep -E '^open import DASHI\.Physics\.YangMills\.|^import DASHI\.Physics\.YangMills\.' "$ALG"; then
  echo "opaque algebra leaf imports Yang-Mills physical semantics" >&2
  exit 1
fi
if grep -E 'PhysicalBlock|SiteField|martingale|globalBlockInner|sumRational|Fourier|lattice' "$ALG" | grep -v '^--'; then
  echo "opaque algebra leaf mentions a physical/global constructor" >&2
  exit 1
fi

# The repaired physical/global consumers may instantiate pre-proved algebra,
# but may not invoke reflection-based ring normalization themselves.
for file in "$VAR" "$POINCARE"; do
  if grep -E 'Data\.Rational\.Tactic\.RingSolver|ℚRing\.solve|solve-∀' "$file"; then
    echo "physical consumer reopened RingSolver normalization: $file" >&2
    exit 1
  fi
done

# Equality and arbitrary-relation lifts are both canonical Core APIs.
grep -q '^record FibreObserverLift' "$CORE"
grep -q '^record FibreRelationLift' "$CORE"
grep -q '^atomicFamilyToGlobal :' "$CORE"
grep -q '^atomicRelationFamilyToGlobal :' "$CORE"
grep -q 'solverMayNormalizeThroughFibreBoundary : Bool' "$CORE"
grep -q 'atomic-global-fibre-boundary false true true false true false' "$CORE"

# The global norm is a genuine equality-preserving fibre observer.
grep -q '^globalNormObserverLift : FibreLift.FibreObserverLift globalNormSq' "$VAR"
grep -q 'FibreLift.atomicFamilyToGlobal globalNormObserverLift' "$VAR"
grep -q '^crossTotalZero :' "$VAR"
grep -q 'OpaqueAlgebra.sixTermSumZero' "$VAR"
grep -q 'OpaqueAlgebra.dropScaledZero' "$VAR"
grep -q 'OpaqueAlgebra.scaleFourSum' "$POINCARE"

# The real inequality consumer is registered through the generic relation API.
grep -q 'FibreLift.FibreRelationLift _≤_ _≤_ (sumObserver values)' "$REL"
grep -q 'FibreLift.atomicRelationFamilyToGlobal' "$REL"

# Proof-debt ownership is preserved: profiling may refine runLocalAgda but may
# not reopen external or mathematical routes as local certification work.
grep -q 'prepareLocalAgda Debt.runLocalAgda observation' "$PREP"
grep -q 'liftThroughFibreBeforeCheck' "$PREP"
grep -q 'externalLeanRemainsExternal' "$PREP"
grep -q 'aristotleRemainsExternal' "$PREP"
grep -q 'novelMathematicsRemainsMathematics' "$PREP"
grep -q 'relationPreservationReceiptStillRequired : Bool' "$PREP"

# Repo-wide diagnostic classification remains available, but is non-strict by
# default because legacy syntax alone is not proof of an OOM defect.
bash scripts/audit_agda_solver_fibre_boundaries.sh >/dev/null

# Lightweight kernel surface only.  Deep consumers are profiled separately so
# this guard does not itself recreate the OOM path.
scripts/run_agda29_parallel_check.sh \
  "$CORE" \
  "$ALG" \
  "$PREP"
