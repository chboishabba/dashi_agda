#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CORE="DASHI/Core/AtomicGlobalFibreLiftExact.agda"
ALG="DASHI/Physics/YangMills/BalabanOpaqueGlobalAlgebraExact.agda"
VAR="DASHI/Physics/YangMills/BalabanPath4PhysicalVarianceDecompositionExact.agda"
POINCARE="DASHI/Physics/YangMills/BalabanPath4PhysicalComponentPoincareExact.agda"
PREP="DASHI/ComputerScience/AgdaProofDebtFibrePreparationExact.agda"
ORDER="DASHI/Physics/YangMills/BalabanFiniteRationalOrderCoreExact.agda"
REL="DASHI/Physics/YangMills/BalabanFiniteSumRelationFibreLiftExact.agda"
PATH13LIFT="DASHI/Physics/YangMills/BalabanPath13ZeroMeanFibrePoincareLiftExact.agda"
PATH13GLOBAL="DASHI/Physics/YangMills/BalabanPath13FourAxisPhysicalPoincareExact.agda"
PATH13DIRECTION="DASHI/Physics/YangMills/BalabanPath13DirectionalEnergyContractionExact.agda"
BOND="DASHI/Physics/YangMills/BalabanPath4BondHodgeCoercivityExact.agda"
THREE="DASHI/Physics/YangMills/BalabanP33ThreeComponentCoercivityExact.agda"
GREEN="DASHI/Physics/YangMills/BalabanPath4SU2ConfiguredGreenNormExact.agda"

for file in "$CORE" "$ALG" "$VAR" "$POINCARE" "$PREP" "$ORDER" "$REL" "$PATH13LIFT" "$PATH13GLOBAL" "$PATH13DIRECTION" "$BOND" "$THREE" "$GREEN"; do
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
for file in "$VAR" "$POINCARE" "$GREEN"; do
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

# Finite-sum order ownership must be acyclic:
# scalar recursive theorem -> relation observer -> physical consumer.
grep -q '^sumRationalMonotone :' "$ORDER"
grep -q 'OrderCore.sumRationalMonotone' "$REL"
grep -q 'FibreLift.FibreRelationLift _≤_ _≤_ (sumObserver values)' "$REL"
grep -q 'FibreLift.atomicRelationFamilyToGlobal' "$REL"
if grep -q 'BalabanPath4DirectionalEnergyContractionExact' "$REL"; then
  echo "finite-sum relation lift depends upward on its physical consumer" >&2
  exit 1
fi

# Path13 aggregation is a true consumer of the generic <= fibre observer.
grep -q '^sumZeroMeanFibrePoincareViaFibre :' "$PATH13LIFT"
grep -q 'SumLift.sumRationalMonotoneViaFibre' "$PATH13LIFT"
grep -q 'Fibre13.zeroMeanPhysicalFibrePoincare13' "$PATH13LIFT"
if grep -q 'BalabanPath13FourAxisPhysicalPoincareExact' "$PATH13LIFT"; then
  echo "Path13 fibre lift depends upward on the global four-axis consumer" >&2
  exit 1
fi
if grep -Eq '^sumZeroMeanFibrePoincareViaFibre.*\(.*∷.*\)|sumZeroMeanFibrePoincareViaFibre.*=.*sumZeroMeanFibrePoincareViaFibre' "$PATH13LIFT"; then
  echo "Path13 fibre aggregation regressed to local recursive replay" >&2
  exit 1
fi

# The global Path13 consumer must use the stronger all-transverse zero-mean
# premise directly.  Do not reconstruct the old membership-indexed recursion.
grep -q 'FibreLift13.sumZeroMeanFibrePoincareViaFibre' "$PATH13GLOBAL"
if grep -q '^sumZeroMeanFibrePoincare :' "$PATH13GLOBAL"; then
  echo "global Path13 consumer reintroduced a local aggregate theorem" >&2
  exit 1
fi
grep -q 'OpaqueAlgebra.scaleFourSum' "$PATH13GLOBAL"
if grep -A45 '^martingalePoincareBeforeEnergyContraction :' "$PATH13GLOBAL" | grep -q 'ℚRing\.solve\|solve-∀'; then
  echo "Path13 post-variance consumer reopened RingSolver" >&2
  exit 1
fi
# One local solver family remains legitimate: the pointwise centering identity.
grep -A18 '^axisCenteringEdgeDifferenceExact :' "$PATH13GLOBAL" | grep -q 'ℚRing.solve-∀'

# Directional Path13 contraction must lift the predecessor-indexed <= family
# through the canonical observer rather than recurse over the predecessor list.
grep -q 'BalabanFiniteSumRelationFibreLiftExact as SumLift' "$PATH13DIRECTION"
grep -q '^sumRationalMonotone = SumLift.sumRationalMonotoneViaFibre' "$PATH13DIRECTION"
if grep -Eq '^sumRationalMonotone \[\]|^sumRationalMonotone \(.*∷.*\)' "$PATH13DIRECTION"; then
  echo "Path13 directional contraction regressed to local sum recursion" >&2
  exit 1
fi

# Migrated consumers must use the relation observer rather than importing the
# large directional-energy module solely for its old list helper.
for file in "$BOND" "$THREE" "$GREEN"; do
  grep -q 'BalabanFiniteSumRelationFibreLiftExact' "$file"
  grep -q 'sumRationalMonotoneViaFibre' "$file"
  if grep -q 'BalabanPath4DirectionalEnergyContractionExact' "$file"; then
    echo "migrated consumer regressed to heavy directional helper import: $file" >&2
    exit 1
  fi
done

grep -q 'OpaqueAlgebra.scaleThreeSum' "$GREEN"

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

# Lightweight kernel surface only.  Deep physical consumers remain targeted
# profiler/check roots so this guard cannot recreate the OOM path itself.
scripts/run_agda29_parallel_check.sh \
  "$CORE" \
  "$ALG" \
  "$PREP"
