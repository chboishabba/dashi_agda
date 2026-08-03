#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 scripts/check_ns_luo_weighted_schur_flux.py

check() {
  scripts/run_agda29_parallel_check.sh "$1"
}

check DASHI/Physics/Closure/NSTriadKNLocalizedBKMScaleDictionaryExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoPrimarySourceProofArchitectureExact.agda
check DASHI/Physics/Closure/NSTriadKNProjectedConvolutionIncidenceEnumerationExact.agda
check DASHI/Physics/Closure/NSTriadKNPhysicalCutoffFluxWeightedSchurExact.agda
check DASHI/Physics/Closure/NSTriadKNWeightedSchurPhysicalFluxReuseExact.agda
check DASHI/Physics/Closure/NSTriadKNProjectedConvectionEnergyFluxExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoCutoffEnergyBootstrapExact.agda
check DASHI/Physics/Closure/NSTriadKNLuoWeightedSchurFluxIntegration.agda
check DASHI/Physics/Closure/NSTriadKNLocalizedBKMRouteIntegration.agda
