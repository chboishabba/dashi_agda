# Finite-K Dust population-centering theorem audit (26 October 2026)

## Scientific attribution
Original Dust activation perturbation / estimator Eq. (2): Samip Dahal, Bishwas Mandal, Serdar Gülbahar and Akshay Vegesna, https://qlabs.sh/research/dust/ and https://github.com/qlabs-eng/dust. This exact affine expectation derivation and the exhaustive signed-population test are DASHI's mathematical audit, not an original paper performance result or a representation of the authors' own claims. LILA training is a separate downstream consumer (#1265).

## Statement with exact hypotheses
Let K≥1 and a_i be iid *scalar* random perturbations with E[a_i]=0, E[a_i²]=1 and finite second moments. For affine loss ell_i=g*(h+sigma*a_i)+b with sigma nonzero, Dust's c_i=mean_j ell_j - ell_i and ghat=-(1/(K*sigma)) Σ_i c_i*a_i lead to

  ghat = (g/K) Σ_i (a_i-a_bar)*a_i
       = g*( (1/K)Σ_i a_i² - a_bar² ).

By independence and centering, E[a_bar²]=1/K. Thus

  E[ghat] = (1-1/K)*g.

For a vector perturbation a_i∈R^d with E[a_i]=0 and covariance I_d, the analogous affine expression is ghat = [ (1/K)Σ_i a_i a_i^T - a_bar a_bar^T ] g, so E[ghat] = ((K-1)/K) g, subject to compatible vector orientation. It is sample covariance with divisor K. An optional rescaling K/(K−1) corrects the affine expectation only for K>1, but must not be silently introduced as an assertion about the source algorithm or arbitrary nonlinear networks.

Under the paper's **nonlinear** losses, finite sigma and temporal reward propagation, the estimator targets a noise-smoothed surrogate and additionally depends on cross-token causal effects and smoothness; do not promote the affine expectation theorem into global unbiasedness or convergence.

## Finite execution receipt
Executed with local Python stdlib and exact Fraction arithmetic under a 10-second container timeout; all cases passed: K=1..8, enumeration of all 2^K Rademacher vectors. Outputs respectively 0, 1/2, 2/3, 3/4, 4/5, 5/6, 6/7, 7/8. Reproducible script committed to `scripts/check_dust_finite_k_centered_expectation.py`. Rademacher probes are an independent finite test of the moments-based identity, not a simulation of Gaussian draws.

## Precise remaining kernel cut
1. Build an actual finite probability carrier (finite Rademacher is smallest) and prove expectation identity as a lemma about finite sums, not simply a supplied equality premise.
2. Generalise via a probability interface expressing zero-mean, identity-covariance, independence and integrability; specialise to Gaussian as a separate law/measure identification.
3. Prove Eq. (3) in vector/matrix form with concrete finite sums and matrix multiplication.
4. Refine real reference Dust implementation (`dust.py` and `model.py`), including future reward, attention surrogate, cached-logit estimator and residual scalar ES, before claiming paper-complete formalisation.
5. Integrate the *actual* LILA task's semantic loss and trainable parameters, then conduct matched held-out benchmarks and full-compute accounting.

Agda kernel checks and CI intentionally not run. Exact Python enumeration is evidence for the specific finite instances, not a universally checked formal proof.


## Follow-on exact two-probe Agda source (26 October)

New `DASHI/Reasoning/DustTwoProbeCenteringExact.agda` states and source-writes the concrete identity
`(1/2)Σ_{i=1,2}(a_i - a_bar)a_i = (a_1-a_2)^2/4`,
the cancellation for identical probes, and unit sample covariance for the *antithetic* pair `(+1,-1)`. The proof uses the same rational ring-solver pattern present in the existing repository's Walsh owner. No new Walsh or probability ontology is introduced.

**Experimental distinction:** the iid `(K-1)/K` expectation correction applies to iid, zero-mean, unit-variance samples. An exactly paired antithetic design is dependent and has a different variance structure. This is not a licence to claim uniformly better neural optimisation: compare credit bias/variance, number of distinct forward calls, time, and held-out loss under matched budgets.

Local stdlib Python exact rational test checked 36 input pairs and the antithetic/identical special cases, PASS. The Agda proofs are **source-written but not kernel-run**, CI intentionally skipped. The user-facing deliverable remains a partial Dust theorem cut; the actual nonlinear temporal, attention, head, and complete Noise optimizer proof obligations remain.


## 26 October: actual loss-to-credit Agda theorem candidate

Added `DASHI/Reasoning/DustFinitePopulationCovarianceExact.agda`, extending (not duplicating) `DustTwoProbeCenteringExact`. Defines the measured affine loss `ell(a)=g*(h+sigma*a)+offset`, its **perturbed population mean**, the signed Dust two-draw credit calculation, and the pure polynomial factorisation:
`DustCredit(g,h,sigmaInv,sigma,offset,a,b) = (sigmaInv*sigma)*g*CenteredCov(a,b)`.
With the explicit amplitude-inverse premise, derives `g*CenteredCov(a,b) = g*(a-b)^2/4` using the previous owner's exact rational square theorem. This is a mathematical measurement-to-credit bridge in the *affine, two-probe, single-coordinate* case, not a postulated coefficient-identification field.

Independently checked 147 exact rational input triples (a,b,g) at fixed rational activation, baseline and nonzero perturbation amplitude, all PASS; local Python check is separate from Agda proof authority.

**Kernel receipt:** none. The new Agda source uses the rational ring solver and is *not* claimed typechecked. CI intentionally bypassed. Finite-K stochastic law for all K, nonlinear/token-coupled effects, full Noise source-code refinement, Sophontic experiment and held-out performance are still open.
