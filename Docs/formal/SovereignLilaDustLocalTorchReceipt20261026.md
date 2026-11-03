# Sovereign-LILA Dust CPU max-cut receipt — 26 Oct 2026

Original implementation owner: SPUTNIKAI/sovereign-lila-e8 (accessible meta-introspector mirror). Original forward-only activation-credit algorithm: Dahal, Mandal, Gülbahar, Vegesna, Dust (2026). DASHI owns this source-specific integration and the local reproduction harness only.

**Local execution:** PyTorch 2.10.0+cpu, one thread. A shape-compatible Torch module (embedding -> last-layer from_e8 linear -> output head) received 8 Gaussian forward-only perturbations. Population-centred per-token CE, immediate reward gamma=0, and outer-product projection update were evaluated; 10 forward calls total. Local standalone mirror of the committed optimiser logic finished within a short timeout:
- loss before 2.3726654052734375
- loss after 2.351482629776001
- projection update norm 0.025982258841395378
- no parameter gradients populated.
This is a single seed/single synthetic batch and is not an independent reproducing run against upstream E8GPT.

**Real source runner added:** `scripts/run_sovereign_lila_e8_dust_smoke.py --lila-checkout /path/to/sovereign-lila-e8`. It imports actual `config.config.E8Config` and `models.model.E8GPT`, builds a small instance, calls `scripts/sovereign_lila_dust_projection_step.py`, and checks real weight changes without `backward()`. Optional trusted checkpoint path uses `weights_only=True`. No upstream checkout could be downloaded into the tool container (network DNS blocked); thus this source runner has **not** been executed with the original E8GPT here. A successful runnable interface is not equivalent to full source-model compatibility.

Latest PR inspiration relevant to the research governance lane: #1266 revisable observer/source-first proof-search, #1268 Follow Through and attribution, and #1265 itself. Reuse the claim-relative provenance framework instead of treating loss decrease in one batch as improved generalisation or universal fast training.

**Limitations:** Target is only final E8 `from_e8` weight, K sequential full model forwards, not 1.6-second Noise benchmark, no cache/head/residual ES optimisation, no matched AdamW comparison, no real TinyStories held-out evaluation. Native model stochastic noise is suppressed by `eval()` during probes and the old train/eval flag is restored. CI not run.
