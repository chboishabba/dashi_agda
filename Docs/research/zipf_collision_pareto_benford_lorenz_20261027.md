# Zipf family: collision, Simpson, Pareto–Benford–Lorenz finite max-cut

Date: 27 October 2026. Dedicated statistics PR #1275. This document
extends the 27-subject inventory without adding a new universal law.

## Attribution and method

- Foundational occupancy/inclusion-exclusion and variance identities remain
  classical probability results. Collision concentration/inverse concentration
  belong to the historical Simpson / Herfindahl–Hirschman / Hill diversity
  lineages, not to the repository's original discovery.
- Original Benford history: **Simon Newcomb (1881)** before Frank Benford (1938).
  Earlier original text roots and later historical summaries remain distinct.
- Classical Pareto distribution and Max O. Lorenz (1905), with the analytical
  Gini coefficient, retain their mathematical authorship.
- *Relevant direct recent original studies*: Stanojevic, Radojicic, Rajic
  and Rakonjac-antic (2024), DOI 10.15672/hujms.1316712, study conditions
  for Pareto/Weibull leading-digit conformity; a separate study,
  *Benford and power law distributions: Representation and simulation*
  (2025), https://www.sciencedirect.com/science/article/pii/S0960077925002668,
  discusses strong Benford/power-law relations. These publications are
  different source objects, not authored or replicated by this PR.
- Repository implementation, synthetic exact tests and selection of proof
  obligations credited to **Johl Brown with OpenAI ChatGPT assistance** on
  27 October 2026. Distinguish source-written Agda, locally executed Python,
  and kernel-verified Agda: **NO Agda kernel receipt**.

## I. IID Zipf rank masses → collision and concentration

Let `p_i>=0`, `Σ_i p_i=1`, and suppose that the draws are IID.
Collision index `C=Σ_i p_i²=Pr(X1=X2)`. Then:

- `E[V2]=2-C`, and `E[V3]=3-3C+Σ_i p_i³`.
- `Δ²E[V_t]=-Σ_i p_i²(1-p_i)^t<=0` for `t>=0`.
- `Var(V_t)=Σ_i a_i(1-a_i)+2Σ_(i<j)[(1-p_i-p_j)^t-a_i a_j]`
  where `a_i=(1-p_i)^t`.
- The off-diagonal covariance terms are nonpositive because
  `1-p_i-p_j <= (1-p_i)(1-p_j)`, hence
  `0<=Var(V_t)<=E[V_t]`.
- Cauchy–Schwarz on `Σ_i p_i=1` gives `1/K<=C<=1` for K declared
  atoms, with `C=1/K` exactly at the uniform mass vector; inverse Simpson
  effective-type count is `1/C`.

These are mathematically precise **conditional** finite identities.
They do not prove real corpora are independent or exhibit Zipf/Heaps.
`scripts/zipf_occupancy_collisions_exact.py` and
`tests/test_zipf_occupancy_collisions_exact.py` give 10 locally tested
regressions, including independently enumerated finite word spaces.

For a fixed multiset with positive counts `f_i`, `N=Σf_i>=2`,
uniform permutation without replacement yields

`Pr(first two equal)=Σ_i f_i(f_i-1)/[N(N-1)]`;

`E[V2]_without-E[V2]_with=(N²-Σ_i f_i²)/[N²(N-1)]>=0`.

The last comparison uses IID with replacement probabilities `p_i=f_i/N`.
It never replaces one sampling law by the other.

## II. Pareto rank concentration → Lorenz / 80:20

For a *continuous* Pareto Type I distribution with minimum `x_min>0`
and tail shape `α>1` (finite population mean):

`L(u)=1-(1-u)^((α-1)/α)`;
`TopShare(t)=t^((α-1)/α)`;
`Gini=1/(2α-1)`.

Exactly 80% of total expected size owned by the upper 20% corresponds
to `α=1/[1-log(.8)/log(.2)]≈1.160964047443681`. Its Gini is about
`0.7564707973660302`. This is a *parameter match*, **not** a universal
Pareto principle or empirical finding for observed wealth.

For `α<=1`, the underlying Pareto mean is infinite. The conventional
finite-mean population Lorenz/80:20 formula cannot be invoked;
code rejects it.

## III. Pareto first-digit law is not automatically Benford

For a continuous Pareto Type I random variable with **minimum exactly 1**
and tail exponent `α>0`, integer base `b>=2`, digit `1<=d<b`,
geometrically partition its support by significant-digit bands
`[d b^k,(d+1)b^k)`, `k=0,1,...`. The exact mass is

`Pr(D_b=d)=[d^-α-(d+1)^-α]/[1-b^-α]`.

This telescopes to total mass one over `d=1,...,b-1`, giving exact
rational probabilities whenever α is a positive integer. For b=10,
`Pr(D=1)=5/9` at α=1, or `25/33` at α=2, whereas Benford requires
`log10(2)≈0.3010`. Thus a power tail is **not sufficient** to prove an
exact Benford leading-digit law. In the **one-sided limit α→0+**, the
formula tends to `log_b(1+1/d)`; setting α=0 inside the Pareto
distribution would NOT be a valid proper Pareto law. Different minimum
scales and scale mixtures change the digit law, so the minimum-one gate
is essential.

The exact integer-shape formula, stable real-parameter limit and
finite-mean inequality formulas are in
`scripts/pareto_benford_lorenz_bridge.py`. Nine local tests in
`tests/test_pareto_benford_lorenz_bridge.py` cover normalization,
countermodels, conditional 80/20, and invalid parameter domains.

## IV. Reuse of existing Agda proof ownership

`DASHI/Statistics/ZipfIIDTwoDrawAndPNFExact.agda` is source-written
and imports **canonical**
`DASHI.Cognition.PNF.GenericExpectedFibreRateExact` finite rational
probability atoms and the already-owned constant-rate expectation identity.
It carries explicit rank-model/provenance/positivity/normalization hypotheses
and source-writes a two-rank IID four-outcome collision/expected-vocabulary
ring identity. This is **NOT kernel-certified** in the current environment:
no Agda executable is installed, and no `agda` call was run.

The source uses `Data.Rational.Tactic.RingSolver` (existing repo style)
and `Data.Rational.Properties`, rather than assuming four named outcomes
from an empirical Zipf spectrum. Whether the new theorem passes the full
Agda kernel remains an open check; never cite it as typechecked.

## Pareto / Ibrahim next-cut and nonpromotion stop rule

P0: exact GitHub-head regression; compile
`DASHI/Statistics/ZipfFamilyFiniteExact.agda`,
`DASHI/Statistics/ZipfHeapsOrderNoGoExact.agda`, and
`DASHI/Statistics/ZipfIIDTwoDrawAndPNFExact.agda`, repair only real
compiler errors. Existing 27-law owner stays canonical.
P1: constructive normalized PMF proof for arbitrary finite integer
exponent/shift, conditional PNF adapter discharge, finite moments/entropy.
P2: independent real-source original-article genealogy plus corpus data
identity, tokenisation, sample-size, sensitivity, threshold and held-out
negative controls.
P3: distinguish Zipf/Pareto/Benford/Heaps fitted models and alternative
lognormal / stretched exponential / discrete body-tail mixtures under
power-law goodness-of-fit with honest uncertainty. Preserve dependence and
ordering assumptions, and source prior discoveries.
P4: only after externally verified same-carrier mathematical transport
consider the optional Zeta/Eisenstein/RH/NS applications. Similar exponents,
third-root phases or Pareto ranks do not establish a same-object mapping.
