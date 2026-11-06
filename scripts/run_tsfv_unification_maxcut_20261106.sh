#!/usr/bin/env bash
# P00/P11 exact-head proof gate for #1460, synchronized with #1444 Nix.
# Safe candidates MUST compile with --safe; roots are typechecked
# separately and require a transitive postulate/import trust audit.
# No chosen free scalar/KK or conditional Agda source equals E1 physics.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "DASHI_UNIFICATION_HEAD=$(git rev-parse HEAD 2>/dev/null || echo UNAVAILABLE)"
python3 scripts/check_emergent31_complete_186_status_20261104.py
python3 scripts/check_tsfv_unification_48_phase_cut_20261106.py
python3 scripts/check_tsfv_original_os_strong_domain_bidi_20261105.py
python3 scripts/check_tsfv_original_diamond_spatial_bits_bidi_20261105.py
python3 scripts/check_tsfv_acoustic_impulse_mass_bidi_20261106.py

if ! command -v agda >/dev/null 2>&1; then
  echo "FAILED: Agda is absent. Enter pinned Nix shell: nix develop .# --command bash scripts/run_tsfv_unification_maxcut_20261106.sh" >&2
  exit 127
fi
agda --version
flags=(-i . -i DCHoTT-Agda -i cubical -l standard-library)

safe_sources=(
  DASHI/Physics/Foundations/TSFVKKSelectedHorizontalMetricSchurExact.agda
  DASHI/Physics/Foundations/TSFVSelectedLatticeAcousticKKFlatControlExact.agda
  DASHI/Physics/Foundations/TSFVAcousticMassInverseBidiNoGoExact.agda
  DASHI/Physics/Foundations/TSFVAcousticLocalImpulseThirdDerivativeExact.agda
  DASHI/Physics/Foundations/TSFVKKHorizontalReductionNoninjectiveBidiExact.agda
  DASHI/Physics/Foundations/TSVFOSSelectedKetHamiltonianNonpromotionExact.agda
  DASHI/Physics/Foundations/TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact.agda
)
for src in "${safe_sources[@]}"; do
  echo "::group::Agda --safe $src"
  agda --safe "${flags[@]}" "$src"
  echo "::endgroup::"
done

roots=(
  DASHI/Unified/BalabanRGTOERegression.agda
  DASHI/Unified/TSFVUnifiedRegression.agda
  DASHI/Unified/TSFVParentChildRegression.agda
)
for src in "${roots[@]}"; do
  echo "::group::Agda typecheck, trust not assumed $src"
  agda "${flags[@]}" "$src"
  echo "::endgroup::"
done

echo "PASS native source typecheck; independent transitive trust and physical E1 remain separate"
