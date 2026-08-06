#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_millennium_substantive_crosspollination.sh

files=(
  DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda
  DASHI/Mathematics/LinearAlgebra/FiniteHodgeEnergyExact.agda
  DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeDecompositionExact.agda
  DASHI/Mathematics/LinearAlgebra/RationalTwoByTwoSelfAdjointSpectralExact.agda
  DASHI/Mathematics/NumberTheory/FiniteEulerProductExact.agda
  DASHI/Mathematics/NumberTheory/FiniteMultiplicativeDirichletExact.agda
  DASHI/Mathematics/Automorphic/TruncatedLFunctionExact.agda
  DASHI/Mathematics/Automorphic/MellinSplitFunctionalEquationExact.agda
  DASHI/Mathematics/Arithmetic/EllipticCurveSmallPrimeFrobeniusExact.agda
  DASHI/Mathematics/Arithmetic/SmallPrimeTruncatedEulerProductExact.agda
  DASHI/Mathematics/Arithmetic/EllipticCurveTwoTorsionAndBadPrimeExact.agda
  DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineProductHodgeExact.agda
  DASHI/Mathematics/Complexity/PSubsetNPTrivialCertificateExact.agda
  DASHI/Mathematics/Complexity/MachineRunCertificateExact.agda
  DASHI/Mathematics/Complexity/FiniteCookLevinTableauExact.agda
  DASHI/Moonshine/DualNumberDifferentialVertexAlgebraExact.agda
  DASHI/Moonshine/RankOneFockPartitionGradingExact.agda
  DASHI/Moonshine/RankOneFockEulerProductPrefixExact.agda
  DASHI/Analysis/SharedFiniteSpectralCertificationExact.agda
  DASHI/Physics/YangMills/FiniteAbelianGaugeHodgeExact.agda
  DASHI/Physics/Closure/FiniteHodgePhysicsCrossPollinationExact.agda
  DASHI/Physics/YangMills/YangMillsHodgeCoercivityFrontierExact.agda
  DASHI/Physics/Closure/NavierStokesFiniteVorticityDepletionExact.agda
  DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionGateExact.agda
  DASHI/Mathematics/CrossPollination/FrontierHodgeAutomorphicSpectralValidation.agda
  DASHI/EverythingFrontierHodgeAutomorphicSpectralCrossPollination.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "frontier tranche contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda:exactOneCochainIsClosed'
  'DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda:composeCochainMap'
  'DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda:cochainMapPreservesExact'
  'DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda:homotopicMapsGiveCohomologousImages'
  'DASHI/Mathematics/LinearAlgebra/FiniteHodgeEnergyExact.agda:hodgeEnergyIdentity'
  'DASHI/Mathematics/LinearAlgebra/FiniteHodgeEnergyExact.agda:harmonicImpliesCoclosedAndClosed'
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeDecompositionExact.agda:hodgeDecomposition'
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeDecompositionExact.agda:laplacianKernelIsHarmonic'
  'DASHI/Mathematics/LinearAlgebra/RationalTwoByTwoSelfAdjointSpectralExact.agda:selfAdjointPairingLaw'
  'DASHI/Mathematics/LinearAlgebra/RationalTwoByTwoSelfAdjointSpectralExact.agda:exactEigenpairHasZeroResidual'
  'DASHI/Mathematics/LinearAlgebra/RationalTwoByTwoSelfAdjointSpectralExact.agda:spectralSeparationSquared'
  'DASHI/Mathematics/NumberTheory/FiniteEulerProductExact.agda:finiteEulerProductExpansionTheorem'
  'DASHI/Mathematics/NumberTheory/FiniteEulerProductExact.agda:pointwiseLocalEqualityGivesProductEquality'
  'DASHI/Mathematics/NumberTheory/FiniteMultiplicativeDirichletExact.agda:coprimeCoefficientMultiplicativity'
  'DASHI/Mathematics/NumberTheory/FiniteMultiplicativeDirichletExact.agda:coprimeDirichletMultiplicativity'
  'DASHI/Mathematics/Automorphic/TruncatedLFunctionExact.agda:coefficientAgreementGivesTruncatedEulerAgreement'
  'DASHI/Mathematics/Automorphic/MellinSplitFunctionalEquationExact.agda:mellinSplitFunctionalEquation'
  'DASHI/Mathematics/Arithmetic/EllipticCurveSmallPrimeFrobeniusExact.agda:allSmallPrimeHasseBounds'
  'DASHI/Mathematics/Arithmetic/SmallPrimeTruncatedEulerProductExact.agda:selectedCoefficientAgreementGivesEulerAgreement'
  'DASHI/Mathematics/Arithmetic/EllipticCurveTwoTorsionAndBadPrimeExact.agda:torsionAdditionAssociative'
  'DASHI/Mathematics/Arithmetic/EllipticCurveTwoTorsionAndBadPrimeExact.agda:everyTorsionPointHasOrderTwo'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineProductHodgeExact.agda:projectiveLineProductBettiNumbers'
  'DASHI/Mathematics/Complexity/PSubsetNPTrivialCertificateExact.agda:pIncludedInNPFromTrivialCertificate'
  'DASHI/Mathematics/Complexity/MachineRunCertificateExact.agda:reachabilityToCertificate'
  'DASHI/Mathematics/Complexity/MachineRunCertificateExact.agda:finiteCertificateGivesBoundedAcceptance'
  'DASHI/Mathematics/Complexity/FiniteCookLevinTableauExact.agda:satisfyingTableauGivesAcceptingRun'
  'DASHI/Moonshine/DualNumberDifferentialVertexAlgebraExact.agda:derivativeLeibniz'
  'DASHI/Moonshine/DualNumberDifferentialVertexAlgebraExact.agda:truncatedVertexFieldsCommute'
  'DASHI/Moonshine/RankOneFockPartitionGradingExact.agda:canonicalFockPrefixCertificate'
  'DASHI/Moonshine/RankOneFockEulerProductPrefixExact.agda:fockPrefixEqualsEulerProductPrefix'
  'DASHI/Analysis/SharedFiniteSpectralCertificationExact.agda:maassTheoremToSharedEnclosure'
  'DASHI/Analysis/SharedFiniteSpectralCertificationExact.agda:finiteHilbertPolyaModesAreCritical'
  'DASHI/Analysis/SharedFiniteSpectralCertificationExact.agda:finiteHodgeModeEigenEquation'
  'DASHI/Physics/YangMills/FiniteAbelianGaugeHodgeExact.agda:curvatureGaugeInvariant'
  'DASHI/Physics/YangMills/FiniteAbelianGaugeHodgeExact.agda:finiteVolumeCoercivityAtOne'
  'DASHI/Physics/Closure/FiniteHodgePhysicsCrossPollinationExact.agda:weightedMetricAdjointnessRemainsOpen'
  'DASHI/Physics/YangMills/YangMillsHodgeCoercivityFrontierExact.agda:localCoercivityMatchesRGEntry'
  'DASHI/Physics/Closure/NavierStokesFiniteVorticityDepletionExact.agda:pointwiseGeometricDepletion'
  'DASHI/Physics/Closure/NavierStokesFiniteVorticityDepletionExact.agda:finiteSumGeometricDepletion'
  'DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionGateExact.agda:allLocalCoresAreNowSubstantive'
  'DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionGateExact.agda:yangMillsContinuumClosureRemainsBoundary'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

# Source metadata guards.
grep -Fq '10.2307/2373615' DASHI/Mathematics/LinearAlgebra/FiniteHodgeEnergyExact.agda
grep -Fq '10.1007/978-3-642-66282-9' DASHI/Mathematics/LinearAlgebra/RationalTwoByTwoSelfAdjointSpectralExact.agda
grep -Fq '10.1007/978-1-4684-9884-4' DASHI/Mathematics/NumberTheory/FiniteEulerProductExact.agda
grep -Fq '10.1007/978-0-387-27226-9' DASHI/Mathematics/Automorphic/TruncatedLFunctionExact.agda
grep -Fq '10.1007/978-0-387-09494-6' DASHI/Mathematics/Arithmetic/EllipticCurveSmallPrimeFrobeniusExact.agda
grep -Fq '10.1145/800157.805047' DASHI/Mathematics/Complexity/PSubsetNPTrivialCertificateExact.agda
grep -Fq '10.1073/pnas.83.10.3068' DASHI/Moonshine/DualNumberDifferentialVertexAlgebraExact.agda
grep -Fq '10.1073/pnas.81.10.3256' DASHI/Moonshine/RankOneFockEulerProductPrefixExact.agda
grep -Fq '10.1007/s00220-022-04609-1' DASHI/Physics/YangMills/YangMillsHodgeCoercivityFrontierExact.agda
grep -Fq '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NavierStokesFiniteVorticityDepletionExact.agda

# Scope and non-promotion guards.
grep -Fq 'No quotient type is silently identified with cohomology' DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda
grep -Fq 'does not assume analytic elliptic' DASHI/Mathematics/LinearAlgebra/FiniteHodgeEnergyExact.agda
grep -Fq 'No convergence or' DASHI/Mathematics/NumberTheory/FiniteEulerProductExact.agda
grep -Fq 'Modularity, convergence, analytic' DASHI/Mathematics/Automorphic/TruncatedLFunctionExact.agda
grep -Fq 'general tape alphabet' DASHI/Mathematics/Complexity/FiniteCookLevinTableauExact.agda
grep -Fq 'not the Heisenberg or Monster VOA' DASHI/Moonshine/DualNumberDifferentialVertexAlgebraExact.agda
grep -Fq 'do not identify the' DASHI/Analysis/SharedFiniteSpectralCertificationExact.agda
grep -Fq 'Nonabelian commutators' DASHI/Physics/YangMills/FiniteAbelianGaugeHodgeExact.agda
grep -Fq 'not a continuum regularity theorem' DASHI/Physics/Closure/NavierStokesFiniteVorticityDepletionExact.agda
grep -Fq 'openProblemLanesRemainOpen' DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionGateExact.agda

grep -Fq 'EverythingMillenniumSubstantiveCrossPollination' DASHI/EverythingFrontierHodgeAutomorphicSpectralCrossPollination.agda
grep -Fq 'FrontierHodgeAutomorphicSpectralValidation' DASHI/EverythingFrontierHodgeAutomorphicSpectralCrossPollination.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/EverythingFrontierHodgeAutomorphicSpectralCrossPollination.agda
