# Zipf/Heaps completion-time and rare-tail max-cut (28 October 2026)

**Owner:** PR #1275, the existing 27-subject statistical family. This is an extension of the existing finite Heaps, occupancy and majorization code. It is not a 28th requested law. No ESD, Balaban, Monster, RH or NS theorem is imported or asserted.

## Prior art and original proof ownership

- Hermann von Schelling, "Coupon Collecting for Unequal Probabilities," *American Mathematical Monthly* **61** (1954), 306–311: original unequal-probability coupon-collection distribution, as independently identified in Nakata's references. This mathematical priority is NOT DASHI's.
- Philippe Flajolet, Danièle Gardy and Loÿs Thimonier, "Birthday paradox, coupon collectors, caching algorithms and self-organizing search," *Discrete Applied Mathematics* **39** (1992), 207–229: classical inclusion-exclusion/algorithmic coupon-collection source. No code from that work is copied.
- Toshio Nakata, "Coupon Collector's Problem with Unlike Probabilities," *Journal of Classical Analysis* **14** (2019), 177–180, DOI https://doi.org/10.7153/jca-2019-14-13: **explicitly proves IID full-collection CDF Schur concavity, completion-time stochastic ordering and expected-time Schur convexity.** The IID majorization/completion corollary here is inherited, NOT newly proved first by DASHI.
- Hardy, Littlewood and Pólya, *Inequalities* (1934): classical majorization; Marshall, Olkin and Arnold, *Inequalities: Theory of Majorization and Its Applications* (2nd edition, 2011): later systematic framework.
- Célestin Zimmerlin, Thomas Louail, Manuel Moussallam and Marc Barthelemy, *Physical Review E* **113**, 054304 (11 May 2026), https://doi.org/10.1103/543d-frbq: independent temporal-order/Heaps–Zipf context, not a new coupon-collector law.
- Filippo Santoro, Alberto Petri and Francesca Tria, *Physical Review Research* **8**, 043083 (22 October 2026), https://doi.org/10.1103/shhp-4dht: separate empirical novelty-avalanche research, not replicated here.
- New exact rational Python integration, independent tests, and research/attribution ledger: Johl Brown-directed repository work with OpenAI ChatGPT assistance, 28 October 2026. Earlier Ibrahim Monster 3B ownership and prior repository/PR contributors remain untouched.

## Precisely declared models

Fix a vector of **K strictly positive integer counts** f=(f_1,...,f_K), with total N. Let T denote the *first* draw number at which every type has appeared.

1. IID replacement: every draw selects type i with probability f_i/N independently of all earlier draws. T may exceed N.
2. Uniform permutation: permute N individually distinguishable tokens uniformly and observe type labels. T is at most N. This is NOT IID and NOT an empirical temporal-independence assertion.

For a nonempty subset A of types, write f_A=sum(i in A) f_i. Exact inclusion-exclusion yields:

```
P_iid(T <= t) = 1 - Σ_{A ≠ ∅} (-1)^(|A|+1) ((N-f_A)/N)^t.
P_perm(T <= t) = 1 - Σ_{A ≠ ∅} (-1)^(|A|+1) C(N-f_A,t)/C(N,t).
```

Under the usual convention C(n,t)=0 for t>n, the second formula holds for integer 0<=t<=N. For positive counts, the first holds for every nonnegative integer t, including t>N. Both give zero at t=0 and one at t=N under permutation.

## Exact expectations: closed finite subset sums

The tail-sum identity E[T]=Σ_{t>=0}P(T>t) and geometric summation give:

```
E_iid[T]  = N Σ_{A ≠ ∅} (-1)^(|A|+1) / f_A.
E_perm[T] = (N+1) Σ_{A ≠ ∅} (-1)^(|A|+1) / (f_A+1).
```

For permutation, the elementary hypergeometric hockey-stick identity is

```
Σ_{t=0}^{N-1} C(N-f_A,t)/C(N,t) = (N+1)/(f_A+1).
```

These are *classical finite probability computations* with exact arithmetic. The permutation formula is separately derived for the fixed-multiset sampler and is not silently borrowed from an IID model.

## A conditional concentration consequence and a tail obstruction

Existing PR-owned `discovery_stochastic_majorization_certificate` gives a two-sampler first-order stochastic discovery-count order when **f majorizes g** and K,N are equal. In particular, for the top threshold K:

```
P_f(T<=t) <= P_g(T<=t).
E_f[T] >= E_g[T].
```

For IID the comparison holds at every integer t>=0; for permutation at t<=N. The expected-time statement follows by summing the ordered completion tails. Nakata (2019) already owns the general IID theoretical direction; no novelty priority is claimed.

For either sampler, the exact probability of **at least one still-unseen type** obeys

```
max_i P(i unseen at t) <= P(T>t) <= min(1, Σ_i P(i unseen at t)).
```

Here the singleton missing probabilities are `((N-f_i)/N)^t` for IID and `C(N-f_i,t)/C(N,t)` for a permutation. This gives a meaningful *conditional* rare-type bound without fitting a physical exponent or inventing a tail sample.

**Same-head counterexample:** f=(9,7,3,1) and g=(9,7,2,2) have identical N=20, K=4, first two rank frequencies and head mass. Their completion CDFs and means differ under BOTH models. Therefore even a perfect top-two rank fit does not identify rare-tail completion risk. This is a finite counterexample, not corpus evidence.

## Test receipts, implementation ceiling, and remaining P0 gates

- `scripts/zipf_completion_time_exact.py` reuses `_validated_counts` and `multiset_count_majorizes` from `scripts/zipf_heaps_bridge.py`. It does not define a new probability ontology.
- `tests/test_zipf_completion_time_exact.py`: **10 independently executed tests**; 10 prior stochastic-majorization tests also passed in the same local invocation = **20/20 focused local tests**.
- Tests compare IID CDFs to fully enumerated independent draw words, permutation CDFs to physical-token subset enumeration, IID mean to an independent absorbing-state dynamic program, permutation mean to full token-permutation enumeration, and check all-pair majorization/rare-tail inequalities with exact fractions. Invalid domains and sampler confusion fail closed.
- The source and test Git blobs were read back from GitHub and matched locally executed bytes. This is **not** a full exact-head 27-topic Python suite. The P0 acceptance script and workflow include the 13th test module, but no passing matching GitHub Actions or Agda kernel result is claimed.
- For explicit computational complexity, the direct exact subset evaluator rejects K>18. This is not a claim that the theorems are mathematically restricted to 18 types.
- Empirical corpus model fitting, held-out evaluation, real-tail identity, source-original comparison, and independent kernel verification remain unpaid. Zipf rank values alone identify neither chronology nor Fourier phase/pressure, RG scale flow, RH, or Ibrahim Monster 3B same-object representation.
