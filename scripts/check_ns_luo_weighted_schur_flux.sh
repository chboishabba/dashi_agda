#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 scripts/check_ns_luo_weighted_schur_flux.py

check() {
  scripts/run_agda29_parallel_check.sh "$1"
}

check DASHI/Physics/Units/MechanicalDimensionExact.agda
check DASHI/Physics/Units/PhysicalNormalizationExact.agda
check DASHI/Physics/Limits/PhysicsLimitCommutingSquare.agda
check DASHI/Physics/Closure/NSTriadKNNavierStokesNormalizationTransportExact.agda
check DASHI/Physics/Closure/NSTriadKNLocalizedBKMScaleDictionaryExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoPrimarySourceProofArchitectureExact.agda
check DASHI/Physics/Closure/NSTriadKNProjectedConvolutionIncidenceEnumerationExact.agda
check DASHI/Physics/Closure/NSTriadKNPhysicalHardHighTriadSelectionExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoPhysicalEnumerationReuseExact.agda
check DASHI/Physics/Closure/NSTriadKNPeriodicHardProjectorAlgebraExact.agda
check DASHI/Physics/Closure/NSTriadKNFiniteHermitianDiagonalMultiplierExact.agda
check DASHI/Physics/Closure/NSTriadKNHardProjectorCoefficientSelfAdjointExact.agda
check DASHI/Physics/Closure/NSTriadKNHardProjectorParsevalTransportExact.agda
check DASHI/Physics/Closure/NSTriadKNOfficialFiniteFourierHermitianParsevalExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoRadialSmoothMultiplierExact.agda
check DASHI/Physics/Closure/NSTriadKNHardSmoothLittlewoodPaleyTransferExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoPeriodicMultiplierKernelBoundExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoConcreteRadialMultiplierKernelExact.agda
check DASHI/Physics/Closure/NSTriadKNHardHighPhysicalZ3PairEncodingExact.agda
check DASHI/Physics/Closure/NSTriadKNPhysicalCutoffFluxWeightedSchurExact.agda
check DASHI/Physics/Closure/NSTriadKNWeightedSchurPhysicalFluxReuseExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoHardHighFullShellPhysicalIdentificationExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoFullShellFluxAdapterExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoCrossCarrierRationalIdentificationExact.agda
check DASHI/Physics/Closure/NSTriadKNProjectedConvectionEnergyFluxExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoCutoffEnergyBootstrapExact.agda
check DASHI/Physics/Closure/NSTriadKNRegularLerayHopfPeriodicSolutionExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoPhysicalEnergyDissipationTimeExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoOfficialPhysicalEnergyTimeExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoPublishedContinuationAuthorityExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoOfficialLerayHopfAuthorityExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoScalingExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoWeightedSchurContinuationSynthesisExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoOfficialContinuationClosureExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoWeightedSchurFluxIntegration.agda
check DASHI/Physics/Closure/NSTriadKNLuoOfficialContinuationIntegration.agda
check DASHI/Physics/Closure/NSTriadKNLocalizedBKMRouteIntegration.agda

# Physical-analytic and submission-grade frontier: weighted increment kernel,
# finite Young/Schur reducers, equation (4.2), Section 4, fixed-shift decay,
# finite/infinite and rational/real promotion, maximal time, final theorem type
# and audit receipts.
check DASHI/Physics/Closure/NSTriadKNLuoPhysicalAnalyticFrontierValidation.agda

echo "NS Luo analytic and submission frontier check completed"
