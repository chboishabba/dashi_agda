# Finite two-sampler Heaps stochastic dominance — 28 October 2026

**Scope:** PR #1275, original 27 Zipf-family subjects. This strengthens the existing
`zipf_majorization_expected_heaps_exact.py` expected-vocabulary comparison.
It is not a 28th statistical law or a Balaban/Monster/NS/RH result.

## Original attribution (retain original proof owners)

- Issai Schur (1923) and Hardy, Littlewood and Pólya, *Inequalities* (1934):
  classical majorization and transfer methods.
- Albert W. Marshall and Ingram Olkin, *Schur-Convex Functions*, Stanford
  technical report OLK NSF 74 (May 1973),
  https://statistics.stanford.edu/technical-reports/schur-convex-functions
  and Marshall, Olkin and Barry C. Arnold, *Inequalities: Theory of
  Majorization and Its Applications*, 2nd ed. (2011),
  https://link.springer.com/book/10.1007/978-0-387-68276-1
  specifically treat stochastic comparisons for multinomial occupied cells.
  **Do not claim original discovery of IID stochastic occupancy ordering.**
- Zimmerlin, Louail, Moussallam and Barthelemy, *Physical Review E* 113,
  054304 (11 May 2026), https://doi.org/10.1103/543d-frbq: independent
  temporal-dependence and extremal Heaps/Zipf analysis.
- Clauset, Shalizi and Newman, *SIAM Review* 51 (2009), 661–703,
  https://doi.org/10.1137/070710111: independent falsifiable empirical
  power-law model methodology.

New exact Python finite sampler integration and tests: Johl Brown-directed
DASHI repository work with OpenAI ChatGPT assistance, 28 October 2026.
Earlier Ibrahim Monster 3B and other repository PR proof ownership remains
separate. This code is **not an Agda kernel-verified proof**.

## The finite conditional theorem

Let `f,g` be positive integer type-frequency vectors with the same type
count K and token count N. Suppose f majorizes g. For any `0<=t<=N`,
under EACH of two distinct sampling processes:

1. Independent with-replacement draws with probability f_i/N or g_i/N.
2. Uniform random permutation of an N-token multiset, without replacement.

For every integer threshold `j=0,...,K`:

`Pr_f[V_t >= j] <= Pr_g[V_t >= j]`.

The IID-only distribution API also permits arbitrary nonnegative t.
This is **first-order stochastic dominance** of observed distinct-type
counts, not just an ordering of expected vocabulary. It does **not**
order variances, incremental novelty rates, empirical chronology or
dependence structures.

### Proof via concentrating transfers

Take a>=b>=2 and replace (a,b) with (a+1,b-1). Aggregate these two types
into one group of size M=a+b. All other types, the group schedule and its
number m of draws can be coupled identically before and after transfer.

Given m>=1 group draws, the group contributes 1 type, plus an indicator
that both original types have appeared:

- IID: `1 - (a/M)^m - (b/M)^m`.
- Permutation: `1 - [C(a,m)+C(b,m)]/C(M,m)`, with C(x,m)=0 for x<m.

Both indicator success probabilities weakly **decrease** when the two
counts become more unequal. The first follows from convexity of powers.
The second follows from discrete convexity
`Delta^2 C(x,m)=C(x,m-2)>=0` for m>=2; m=1 is equal.
For m=0 the group contributes zero types under both models.
Conditioning on the common outside schedule gives stochastic dominance
for each transfer, and the classical integer majorization transfer
decomposition gives the full finite statement.

## Executable exact coefficient evaluator

`scripts/zipf_stochastic_majorization_exact.py` imports canonical
`zipf_heaps_bridge` count validation, two expectations and majorization.
It uses rational generating-function coefficients for the full PMF:

- IID: `t! [z^t y^j] product_i (1+y(exp(p_i z)-1))`.
- Permutation: `[z^t y^j] product_i (1+y((1+z)^(f_i)-1)) / C(N,t)`.

No new probability carrier or synthetic proof authority is added.
It checks normalization and equality with the existing mean owner.

## Executed and unpaid gates

Six tests in `tests/test_zipf_stochastic_majorization_exact.py` passed
locally. These independently enumerate IID words and without-replacement
subsets of individually labeled multiset tokens, and exhaust **1,007**
comparable count pairs (K=2..4, counts 1..3), all prefix times and
thresholds for both samplers. New module/test GitHub blobs match the
locally executed source.

The focused tests ran against a locally extracted set of dependency
functions from the existing repository owner. **No exact-head full-suite,
Agda kernel or matching GitHub Actions pass is asserted here.** The
acceptance shell script and workflow include this twelfth focused test
file. Remaining P0: exact checkout execution, compatible Agda compiler,
master reconciliation, real source-qualified held-out empirical work.
Do not promote this finite distribution ordering into Monster 3B
same-object recognition, RH, Fourier phase, pressure or physical dynamics.
