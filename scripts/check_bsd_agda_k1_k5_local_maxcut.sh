#!/usr/bin/env bash
# Agda-golden local-only BSD cut. No CI, Docker or trust in status flags.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Mathematics/Arithmetic/EllipticSupportedSquareClassSieveExact.agda
  DASHI/Mathematics/Arithmetic/EllipticActualDyadicPrimePlaceExact.agda
  DASHI/Mathematics/Arithmetic/EllipticRationalPlaceTwoDescentProducerExact.agda
  DASHI/Mathematics/Arithmetic/EllipticOriginalSelmerCohomologyExhaustionExact.agda
  DASHI/Mathematics/Arithmetic/EllipticShaTwoNotFullShaAgdaNegativeControlExact.agda
  DASHI/Mathematics/Automorphic/EllipticSelectedHeckePrimePowerExact.agda
  DASHI/Mathematics/Automorphic/EllipticCMJacobiThetaCheckedRowsExact.agda
  DASHI/Mathematics/Automorphic/EllipticCMLevel32EtaNewmanArithmeticExact.agda
  DASHI/Mathematics/Automorphic/EllipticCMLevel32FrickeMellinExact.agda
  DASHI/Mathematics/Automorphic/EllipticCMLevel32GenusOneArithmeticExact.agda
  DASHI/Mathematics/Automorphic/EllipticCMLevel32LigozatCuspArithmeticExact.agda
  DASHI/Mathematics/Automorphic/EllipticCMNormalizedOneDimensionalQSeriesExact.agda
)

for f in "${files[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "BLOCKED: missing $f" >&2
    exit 11
  fi
  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check' "$f"; then
    echo "BLOCKED: non-golden or unfinished declaration in $f" >&2
    exit 13
  fi
done


# Make the exact original theorem names part of the local preflight,
# without confusing textual presence with kernel proof acceptance.
required=(
  'EllipticSupportedSquareClassSieveExact.agda:filteredCodeRationalRepresentativeIsOriginalTorsion'
  'EllipticActualDyadicPrimePlaceExact.agda:actualTwoIsPrimeNat'
  'EllipticRationalPlaceTwoDescentProducerExact.agda:originalAllPlaceSelmerProjectsToTorsionCode'
  'EllipticOriginalSelmerCohomologyExhaustionExact.agda:originalSelmerGlobalH1ExhaustedByActualTorsion'
  'EllipticShaTwoNotFullShaAgdaNegativeControlExact.agda:vanishingTwoTorsionDoesNotForceGroupTrivial'
  'EllipticSelectedHeckePrimePowerExact.agda:rowEulerHeckeTruncationTwo'
  'EllipticCMJacobiThetaCheckedRowsExact.agda:thetaP13MatchesOriginalFrobenius'
  'EllipticCMLevel32EtaNewmanArithmeticExact.agda:etaNewmanArithmeticConditions'
  'EllipticCMLevel32FrickeMellinExact.agda:level32FrickeFromTwoEtaInversions'
  'EllipticCMLevel32FrickeMellinExact.agda:mellinCentralValueIsTwiceTail'
  'EllipticCMLevel32GenusOneArithmeticExact.agda:level32GenusOneArithmetic'
  'EllipticCMLevel32LigozatCuspArithmeticExact.agda:level32CuspOneWitness'
  'EllipticCMNormalizedOneDimensionalQSeriesExact.agda:normalizedOneDimensionalAllNCoefficientsAgree'
)
for owner in "${required[@]}"; do
  module="${owner%%:*}"
  symbol="${owner#*:}"
  source="$(find DASHI/Mathematics/Arithmetic DASHI/Mathematics/Automorphic -maxdepth 1 -name "$module" -print -quit)"
  if [[ -z "$source" ]] || ! grep -Fq "$symbol :" "$source"; then
    echo "BLOCKED: original named theorem missing: $owner" >&2
    exit 14
  fi
done

if ! command -v agda >/dev/null 2>&1; then
  echo 'BLOCKED: Agda executable unavailable; source-written is NOT kernel accepted.' >&2
  exit 12
fi

# Use the repository's own Agda 2.9 pinned parallel checker and
# dependency/library arguments; do not infer authority from CI.
bash scripts/run_agda29_parallel_check.sh "${files[@]}"

echo 'Agda local checker completed; retain actual receipt/logs and module hashes.'
echo 'This checks selected finite Kummer, Frobenius, Gaussian theta and Fricke/Mellin algebra, NOT classical H¹/Sha, infinite Jacobi, or universal BSD.'

# Optional, NON-GOLDEN numeric regressions: deliberately not mixed into
# Agda kernel acceptance so missing mpmath never downgrades a true proof.
if [[ "${BSD_K4_NUMERIC_ASSAYS:-0}" == 1 ]]; then
  python3 scripts/check_bsd_level32_cm_eta_theta_exact.py --cutoff 256
  python3 scripts/check_bsd_level32_mellin_fricke.py --dps 65 --terms 110
  echo 'Numeric K4 assays passed; these are NOT Agda proof certificates.'
fi


# Optional exact-rational K4 positivity and Cauchy-tail regressions.
# These do not require mpmath and MUST NOT be counted as Agda acceptance.
if [[ "${BSD_K4_EXACT_TAIL_ASSAYS:-0}" == 1 ]]; then
  python3 scripts/check_bsd_level32_positive_tail.py --n 10
  python3 scripts/test_bsd_level32_positive_tail.py
  echo 'Exact rational K4 tail assays passed; Bishop eta, Mellin and Agda kernel remain separate.'
fi
