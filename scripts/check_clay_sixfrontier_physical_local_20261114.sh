#!/usr/bin/env bash
# Six-frontier canonical Clay ROLLUP acceptance, 14 Nov 2026.
# Agda rollup PR #1499 + Lean rollup PR #108; old lane worktrees
# are donor PROVENANCE ONLY, never active targets.
#
# Example:
#   DASHI_CLAY_LEAN_WORKTREE=/work/dashi_lean4-clay108 \
#     bash scripts/check_clay_sixfrontier_physical_local_20261114.sh
#
# CLAY_SIX_SOURCE_ONLY=1 runs exact finite diagnostics WITHOUT kernel.
# No theorem about YM continuum, N21 NP, BSD Sha, NS regularity,
# Bishop uniform eta, or the RH is promoted by a source-only run.

# External OAI 378 uses Lean 4.34.1 (later source revision) and requires a
# separate pinned checkout and axiom audit; never import into 4.28 on this root.
# External October 2026 YM uses Lean 4.32.0 and is also separate. The
# crosswalk check is a source-byte/metadata preflight only.
set -euo pipefail

AGDA_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="${DASHI_CLAY_LEAN_WORKTREE:-}"
if [[ -z "$LEAN_ROOT" || ! -d "$LEAN_ROOT" ]]; then
  echo "BLOCKED: set DASHI_CLAY_LEAN_WORKTREE to Lean Clay rollup #108" >&2
  exit 24
fi
for root in "$AGDA_ROOT" "$LEAN_ROOT"; do
  if ! git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "BLOCKED: $root is not a checked-out Git worktree" >&2
    exit 25
  fi
done
AGDA_SHA="$(git -C "$AGDA_ROOT" rev-parse HEAD)"
LEAN_SHA="$(git -C "$LEAN_ROOT" rev-parse HEAD)"
echo "AGDA_ROLLUP_PR=1499 SHA=$AGDA_SHA"
echo "LEAN_ROLLUP_PR=108 SHA=$LEAN_SHA"
# Mandatory P0: classify all 135 exact symbols against the live checked-out
# Agda and Lean rollup sources BEFORE any source-only or kernel claims.
# A discovered theorem previously marked TARGET_NAME_ONLY is a useful
# fail-closed RECLASSIFY_TARGET: update canonical roadmap/JSON first.
python3 "$AGDA_ROOT/scripts/check_clay_endpoint_symbol_audit_20261115.py" \
  --lean-root "$LEAN_ROOT" --strict
echo "P0_CANONICAL_SIX_ENDPOINT_SYMBOL_AUDIT=SOURCE_CHECKED_NOT_KERNEL"


# Existence checks ensure no implicit fallthrough to historical
# separate donor PR heads.
agda_required=(
  "DASHI/Mathematics/CrossPollination/ClayStagedSourceConvergence20261114.agda"
  "DASHI/Mathematics/Complexity/Karp21GammaBinaryGoldenCoreExact.agda"
  "DASHI/Mathematics/Complexity/Karp21NativeGammaAllLengthCompositePhysicalExact.agda"
  "DASHI/Mathematics/Complexity/Karp21NativeGammaPhysicalAcceptanceObservationExact.agda"
  "DASHI/Analysis/BishopOriginalEtaRawSeriesOfSameSourceExact.agda"
  "DASHI/Physics/Closure/NSTriadKNR650Rational345RelaxedEnvelopeRound855Exact.agda"
  "DASHI/Research/OpenAIMath/OpenAIMathFullSourceRollup20261114.agda"
  "DASHI/Research/OpenAIMath/OpenAIMathOriginalOptimizedSATDecisionBitExact.agda"
  "DASHI/Physics/YangMills/YMClayOriginalF19P0CommonOSSourceConvergence20261114.agda"
)
lean_required=(
  "Integration/OpenAIMath/ClayCrosswalkLeanSourceRollup20261114.lean"
  "Integration/OpenAIMath/FullUpstreamMainResultsCatalogue.lean"
  "Synthesis/ClaySixFrontierRollup20261114.lean"
  "Synthesis/MillenniumBSDCMQ2EightLocalPointWitnessesExact.lean"
  "Synthesis/RiemannA2ActualSelectedIntervalDecisionExact.lean"
  "Synthesis/RiemannSignedFifthEventualThreeProducerRollupExact.lean"
  "Synthesis/NavierStokesR854RealTimeIntegratedRateConditionalExact.lean"
)
for file in "${agda_required[@]}"; do
  test -f "$AGDA_ROOT/$file" || { echo "BLOCKED: missing Agda $file" >&2; exit 26; }
done
for file in "${lean_required[@]}"; do
  test -f "$LEAN_ROOT/$file" || { echo "BLOCKED: missing Lean $file" >&2; exit 27; }
done

pycheck() { (cd "$1" && python3 "scripts/$2"); }
echo "=== exact finite preflights, no kernel claim ==="
pycheck "$AGDA_ROOT" check_ym_r445_weighted_exterior_influence.py
pycheck "$AGDA_ROOT" check_ym_r445_interacting_transfer_contraction_20261114.py
pycheck "$AGDA_ROOT" check_karp21_literal_gamma_allwords_20261114.py
pycheck "$AGDA_ROOT" check_ns_r853_quadratic_lie_derivative_20261114.py
# R734 physical no-go and R856 optimal scalar source: independent exact
# SymPy/Fraction math only; these do NOT validate the PDE continuation.
pycheck "$AGDA_ROOT" check_clay_source_r855_wilson_locality_20261115.py
(cd "$AGDA_ROOT" && python3 -m pytest -q \
  tests/test_ns_r734_pure_plus_physical_w2_no_go.py \
  tests/test_ns_r734_critical_small_data.py \
  tests/test_ns_r734_critical_residence.py)
echo "NS_R734_PHYSICAL_W2_NO_GO: known universal leaf invalid; R855 scalar only"

pycheck "$AGDA_ROOT" check_bishop_eta_all_cutoffs_maxcut_20261114.py
pycheck "$AGDA_ROOT" check_bishop_natlog_two_sided_dyadic_20261114.py
pycheck "$LEAN_ROOT" check_bsd_q2_eight_squareclasses_20261114.py
pycheck "$AGDA_ROOT" check_rh_original_a2_interval_maxcut_20261114.py
(cd "$AGDA_ROOT" && python3 scripts/check_openai_math_full_crosswalk_20261114.py --self-test)
(cd "$AGDA_ROOT" && python3 scripts/check_oai_ym_endpoint_logic_maxcut_20261114.py)
(cd "$AGDA_ROOT" && python3 scripts/check_oai_bidi_ns_sat_20261114.py)
(cd "$AGDA_ROOT" && NS_TOE_VERIFY_MODE=source-only bash scripts/check_ns_toe_abcd_pinned_local_20261115.sh)
echo "NS_ABCD_TOE_SOURCE_PIN_PASS: all four lane owners, A/R3 and nested C/D f9e source; no kernel verdict"
echo "OAI_BIDI_NS_SAT_FINITE_PASS: 580 exact list/Finset CNFs, 4 forced/unforced scope models; kernel still open"
echo "OAI_YM_A7_A8_FINITE_LOGIC_PASS: separate endpoints are not a combined same-witness theorem"
echo "OAI_MATH_CORPUS_PINS_PASS: 721/373/208 historical source index; no mathematical import"
(cd "$AGDA_ROOT" && python3 scripts/check_clay_existing_vs_open_source_20261114.py --lean-root "$LEAN_ROOT" --self-test)
echo "CLAY_TERMINAL_TYPE_AUDIT_PASS: 13 exact-source receipts; no physical or kernel promotion"
echo "EXACT_FINITE_PASS: source-only diagnostics != Agda/Lean theorem"

if [[ "${CLAY_SIX_SOURCE_ONLY:-0}" == "1" ]]; then
  echo "SOURCE_ONLY_PASS; no Agda/Lean kernel; all physical/analytic C gates remain OPEN"
  exit 0
fi

if ! command -v agda >/dev/null 2>&1 &&
   ! command -v nix >/dev/null 2>&1; then
  echo "KERNEL_BLOCKED: Agda 2.9/Nix unavailable" >&2
  exit 28
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "KERNEL_BLOCKED: Lake/Lean unavailable" >&2
  exit 29
fi

(cd "$AGDA_ROOT" && bash scripts/check_ym_r445_original_physical_maxcut_local.sh)
(cd "$AGDA_ROOT" && bash scripts/check_karp21_allwords_physical_local.sh)
(cd "$AGDA_ROOT" && bash scripts/check_ns_r854_affine_integral_local.sh)
(cd "$AGDA_ROOT" && bash scripts/check_bishop_eta_native_exp_cross_pr_local.sh)
(cd "$LEAN_ROOT" && bash scripts/check_bsd_q2_hensel_3705_local.sh)
(cd "$AGDA_ROOT" && RH_LEAN_REPO_DIR="$LEAN_ROOT" bash scripts/check_rh_a2_g3_attachment_local.sh)
(cd "$AGDA_ROOT" && bash scripts/run_agda29_parallel_check.sh DASHI/Mathematics/CrossPollination/ClayStagedSourceConvergence20261114.agda)
(cd "$AGDA_ROOT" && bash scripts/run_agda29_parallel_check.sh DASHI/Research/OpenAIMath/OpenAIMathFullSourceRollup20261114.agda)
(cd "$AGDA_ROOT" && bash scripts/run_agda29_parallel_check.sh DASHI/Physics/Closure/NSTriadKNR650Rational345OptimalEnvelopeRound856Exact.agda)
(cd "$LEAN_ROOT" && lake env lean Integration/OpenAIMath/ClayCrosswalkLeanSourceRollup20261114.lean)
(cd "$LEAN_ROOT" && lake env lean Synthesis/ClaySixFrontierRollup20261114.lean)
(cd "$LEAN_ROOT" && lake env lean Synthesis/RiemannSignedFifthEventualThreeProducerRollupExact.lean)
(cd "$LEAN_ROOT" && lake env lean Synthesis/NavierStokesR854RealTimeIntegratedRateConditionalExact.lean)
(cd "$LEAN_ROOT" && lake env lean Synthesis/NavierStokesR734PurePlusW2NoGoScalarExact.lean)
(cd "$LEAN_ROOT" && lake env lean Synthesis/NavierStokesR855SharpRealTimeConditionalExact.lean)

echo "SOURCE_KERNEL_TARGETS_PASSED: review transitive axioms, --safe, golden pinned toolchains"
echo "OPEN: original physical Wilson RG/E1/D1, bit-TM F3/F4/NP, BSD H1/Sha, NS flow, eta uniform, RH actual zeros."
