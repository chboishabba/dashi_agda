# Dust / Sovereign-LILA runnable handoff (26 October 2026)

This is a **restricted last-E8-projection Dust forward-only smoke**, NOT a full-model training implementation, Noise GPU benchmark, or held-out proof of generalisation. Original Dust method: Samip Dahal, Bishwas Mandal, Serdar Gülbahar, Akshay Vegesna. Sovereign-LILA/E8GPT source: SPUTNIKAI, mirrored by meta-introspector. DASHI integrates, does not claim either upstream project's authorship.

## Single entrypoint

From the **DASHI Agda PR #1265 checkout root**:

```sh
python scripts/run_dust_lila_handoff.py
python scripts/run_dust_lila_handoff.py --run-analogue
python scripts/run_dust_lila_handoff.py --run-real --lila-checkout /absolute/path/to/sovereign-lila-e8
```

The first line is a Python-stdlib-only AST/missing-file preflight (does NOT import Torch, run the model or report success for the real learner). The second invokes the existing shape-compatible Torch smoke. The third invokes the existing `scripts/run_sovereign_lila_e8_dust_smoke.py` directly, which instantiates `E8GPT` in the user-provided checkout, runs a *single synthetic-token update*, and checks parameter change, forward call count, and absence of backward gradients. It does not silently download packages or model checkpoints.

Optional trusted state-dict: `--run-real --lila-checkout /path --checkpoint /path/to/weights.pt`; PyTorch loads with `weights_only=True`. Use only a trusted provenance source. Source/config mismatches should fail rather than be worked around by invented arguments.

To additionally verify a checkout of the two currently pinned 30M Noise record scripts before any run:

```sh
python scripts/run_dust_lila_handoff.py --noise-checkout /absolute/path/to/noise
```

This delegates to `scripts/audit_noise_record_source_identity.py`. Failures indicate a missing, altered or unverified algorithm version; update/review pins explicitly rather than comparing unmatched benchmarks.

## Exact status and responsibility

- Owner of real `E8GPT` forward-only trainer and local Torch smoke: existing #1265 parallel LILA work; handoff script delegates, does not duplicate.
- Mathematical Dust credit and source-specific reward/head branches: existing #1265 proof candidates; new Agda files have not received kernel checks.
- Original Noise records: separate pinned upstream scripts for validation Boost→Cut and speedrun identity→Cut-lite. Pinning is *source identity*, not a claim of reproduced runtime, physical compute or correctness.
- Actual Sovereign-LILA execution has **not** been performed in this tool runtime. The prior executed receipt uses a shape-compatible Torch analogue.
- No CI required or run. Real-world acceptance requires output from the user's execution, then diagnosis of any concrete source/config mismatch; do not predeclare the smoke green.

## Current post-smoke research frontier

1. If the real E8GPT source succeeds: confirm exact model/chkp hashes, hook placement, token semantics and state restoration. The restricted projection update is not the full optimizer.
2. Compare against the same model/initial state with AdamW and no-update controls on held-out data; paired semantic correctness separately.
3. Formal source refinement of Dust's nonlinear temporal/attention/head routes and actual Noise record optimizer transitions; prioritize tested premises rather than new generic records.
4. Preserve source/author provenance and distinguish local syntactic preflight, executable analogue, original-model training and GPU benchmark receipts.
