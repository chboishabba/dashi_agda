# Vector Dust finite-K max-cut, 26 October 2026

**Original algorithm:** Samip Dahal, Bishwas Mandal, Serdar Gülbahar, Akshay Vegesna, *Dust: Pretraining Transformers Without Backpropagation* (2026), https://qlabs.sh/research/dust/ ; https://github.com/qlabs-eng/dust .
**DASHI contribution:** exact finite-population vector-affine audit and source-bound integration; no attribution of this test to the paper's original authors.

For independent zero-mean unit-covariance perturbations `a_i ∈ R^d`, define `abar = (1/K) Σ_i a_i` and `C_K = (1/K) Σ_i a_i a_iᵀ − abar abarᵀ`. For an affine perturbed loss and the paper's sample-mean centering, the activation-credit estimator is `ghat = C_K g`. Hence `E[C_K] = ((K−1)/K) I` and `E[ghat] = ((K−1)/K) g` when the stated independence and finite second moments hold. This is an algebraic/moments consequence, not a new scientific performance claim.

Local Python execution: `python scripts/check_dust_vector_finite_k_expectation.py` with exact `fractions.Fraction` and full Rademacher enumeration, under a 10-second timeout. Passed d,K = (1,2), (2,2), (2,3), (3,3), (3,4), exhausting respectively 4, 16, 64, 512, 4096 draw populations. No stochastic approximation or floating-point tolerance was used.

**Gates still open:** kernel theorem over actual finite sums and probability measures; source-code shape/equation refinement; nonlinear smoothed-gradient/variance analysis; attention and future reward representation; literal trainable LILA objective and held-out benchmarks. Existing `ObserverRefinementLatticeExact` is the canonical refinement owner and must not be rederived.
CI intentionally omitted.
