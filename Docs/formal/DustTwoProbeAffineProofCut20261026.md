# 2026-10-26 affine two-probe proof cut

Original Dust estimator credit: Samip Dahal, Bishwas Mandal, Serdar Gülbahar, Akshay Vegesna (2026), https://qlabs.sh/research/dust/ . Derived two-probe rational proofs are DASHI mathematical work, not an original experimental Dust result.

Extended canonical `DASHI/Reasoning/DustTwoProbeCenteringExact.agda` with `twoProbeAffineCredit`, `twoProbeAffineSquare`, `twoProbeAffineIdentical`, `twoProbeAffineAntithetic` over ℚ and the repository's rational ring-solver tactic. This is a deterministic affine calculation with two arbitrary draws, not a general finite-K Gaussian expectation proof.

Exact identity: `credit(g,a,b)=g*(a-b)^2/4`. For identical draws, credit=0; for the designed antithetic pair (1,-1), credit=g. This must remain separate from the iid finite-K expected factor (K−1)/K, which is an average over independent populations, not an identity for all designs.

Local Python Fraction spot-check: 27 choices of (g,a,b) passed with a 10-second timeout. Agda executable unavailable; no kernel/CI claim. This doesn't yet implement or validate a complete LILA learning objective, the full original Dust temporal credit rule, the attention surrogate, or Gaussian expectation theorem. Canonical LILA observer/refinement, Walsh and semantic-action owners remain unduplicated.

Next genuine cut: finite-probability-sum theorem of iid centering for general K, then concrete matrix outer product with kernel-checked finite sums and real source implementation correspondence; held-out LILA task afterwards.
