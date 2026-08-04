#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# Keep this tranche independently checkable on memory-constrained machines.
# In particular, do not route the lightweight P06 leaf through the generated
# cyclotomic DFT regression dependency graph.
export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanBishopConcreteFactorialCoefficientDischargeExact.agda
  DASHI/Physics/YangMills/BalabanBishopConcreteSineCosineTermParityExact.agda
  DASHI/Physics/YangMills/BalabanBishopConcreteSeriesConvergenceTransportExact.agda
  DASHI/Physics/YangMills/BalabanBishopAlternatingBracketFromMonotoneLimitsExact.agda
  DASHI/Physics/YangMills/BalabanStepVFiniteGeometricInductionExact.agda
  DASHI/Physics/YangMills/BalabanStepVBishopFiniteGeometricExact.agda
  DASHI/Physics/YangMills/BalabanStepVPolynomialWeightedDominationExact.agda
  DASHI/Physics/YangMills/BalabanP06PhysicalModelLeafLightweightExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound10ExactCutset.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound10SourceAudit.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Ledger.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Receipt.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound10LightValidation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSubmissionRound10Advance.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "round-ten tranche contains an explicit postulate or hole" >&2
  exit 1
fi

# Concrete Bishop arithmetic, term parity, and convergence transport.
grep -q 'oddInverseFactorialStep' \
  DASHI/Physics/YangMills/BalabanBishopConcreteFactorialCoefficientDischargeExact.agda
grep -q 'evenInverseFactorialStep' \
  DASHI/Physics/YangMills/BalabanBishopConcreteFactorialCoefficientDischargeExact.agda
grep -q 'concreteFactorialCoefficientStepBounds' \
  DASHI/Physics/YangMills/BalabanBishopConcreteFactorialCoefficientDischargeExact.agda
grep -q 'oddPowerNegation' \
  DASHI/Physics/YangMills/BalabanBishopConcreteSineCosineTermParityExact.agda
grep -q 'identifiedSineOddTermFamily' \
  DASHI/Physics/YangMills/BalabanBishopConcreteSineCosineTermParityExact.agda
grep -q 'identifiedCosineEvenTermFamily' \
  DASHI/Physics/YangMills/BalabanBishopConcreteSineCosineTermParityExact.agda
grep -q 'seriesNegationConvergence' \
  DASHI/Physics/YangMills/BalabanBishopConcreteSeriesConvergenceTransportExact.agda
grep -q 'bishopSeriesLimitParityInputsFromTermParity' \
  DASHI/Physics/YangMills/BalabanBishopConcreteSeriesConvergenceTransportExact.agda
grep -q 'concreteBishopAlternatingBracketsFromInterlacing' \
  DASHI/Physics/YangMills/BalabanBishopAlternatingBracketFromMonotoneLimitsExact.agda

# Finite Step-V summation and lightweight P06 boundary.
grep -q 'finiteGeometricUniformBoundFromSupersolution' \
  DASHI/Physics/YangMills/BalabanStepVFiniteGeometricInductionExact.agda
grep -q 'bishopFiniteGeometricUniformBound' \
  DASHI/Physics/YangMills/BalabanStepVBishopFiniteGeometricExact.agda
grep -q 'polynomiallyWeightedGeometricBoundFromDomination' \
  DASHI/Physics/YangMills/BalabanStepVPolynomialWeightedDominationExact.agda
grep -q 'reducedSkeletonComplexityLinearInDiameter' \
  DASHI/Physics/YangMills/BalabanP06PhysicalModelLeafLightweightExact.agda
grep -q '10.1007/BF01211762' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10SourceAudit.agda

# Exact frontier accounting must remain fail-closed.
grep -q 'concreteSineCosineTermParityDischarged = true' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Receipt.agda
grep -q 'polynomialFiniteSummationReducedToPointwiseDomination = true' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Receipt.agda
grep -q 'concreteSineCosineInterlacingDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Receipt.agda
grep -q 'polynomialPointwiseDominationDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Receipt.agda
grep -q 'globalYangMillsEndpointDischarged = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10Receipt.agda
grep -q 'record Round10CompleteCutset' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound10ExactCutset.agda

roots=(
  DASHI/Physics/YangMills/BalabanBishopConcreteFactorialCoefficientDischargeExact.agda
  DASHI/Physics/YangMills/BalabanBishopConcreteSineCosineTermParityExact.agda
  DASHI/Physics/YangMills/BalabanBishopConcreteSeriesConvergenceTransportExact.agda
  DASHI/Physics/YangMills/BalabanBishopAlternatingBracketFromMonotoneLimitsExact.agda
  DASHI/Physics/YangMills/BalabanStepVFiniteGeometricInductionExact.agda
  DASHI/Physics/YangMills/BalabanStepVBishopFiniteGeometricExact.agda
  DASHI/Physics/YangMills/BalabanStepVPolynomialWeightedDominationExact.agda
  DASHI/Physics/YangMills/BalabanP06PhysicalModelLeafLightweightExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound10LightValidation.agda
)

for root_file in "${roots[@]}"; do
  scripts/run_agda29_parallel_check.sh "$root_file"
done
