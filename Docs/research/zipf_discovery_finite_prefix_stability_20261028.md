# Finite-prefix discovery stability versus rare-tail completion instability

**28 October 2026 · PR #1275 · existing 27 Zipf-family subjects.** Finite empirical measurement-error and tail-coverage bridge, not a new population law or separate probability ontology.

## Mathematical and historical priority

- Coupling and total variation are classical probability. See Torgny Lindvall, *Lectures on the Coupling Method*, reprint 2002. Finite maximal-coupling bounds are inherited mathematics.
- Majorization belongs to Schur and Hardy–Littlewood–Pólya. The original IID coupon-collector completion-order proof is Toshio Nakata (2019), https://doi.org/10.7153/jca-2019-14-13, citing von Schelling (1954), rather than DASHI.
- The two-sampler implementation, exact rational boundary tests and the parameterized tail counterfamily are new Johl Brown-directed repository synthesis with OpenAI ChatGPT assistance, 2026-10-28. No claim of priority over the classical identities.
- Independent 2026 caution: Aristides V. Doumas and S. Spektor, "Equal probabilities maximize the expected deficit in the siblings of the coupon collector," https://arxiv.org/abs/2606.21591, report a related *different* functional that is **not Schur-concave**. We do not infer a general ordering for all coupon-family observables.
- Original Zipf/Estoup, Mandelbrot, Heaps, Zimmerlin, Santoro/Petri/Tria and prior Ibrahim Monster 3B owners retain independent source/PR priority. Same-object NS/RH/Monster and ESD surfaces are out of scope.

## Exact common-support hypotheses

For IID, fix two rational PMFs p and q on the **same labeled K atoms**, including possible zero probabilities, with `TV(p,q) = 1/2 Σ_i |p_i-q_i|`. Draw independently t times in each model. Coupling each draw maximally, then using the *same* per-step coupling independently, gives

```
|P_p(E) - P_q(E)| <= 1 - (1-TV(p,q))^t <= min(1,t TV(p,q))
```

for **any** event E determined by the first t labeled draws. Thus this controls the whole observed Heaps-prefix path distribution, novelty runs, and full-collection event at a fixed t. It is not a bound on future dynamics inferred from a fitted exponent.

For two **positive** finite histograms f,g with the same N,K and aligned type labels, let `D=1/2 Σ_i |f_i-g_i|`, an integer. Reassign exactly D individual token labels to transform one multiset into the other. Apply one common uniform random permutation of the N *distinguishable token positions* to both populations. Their first t observed type labels differ only if a changed token position has appeared. Consequently,

```
|P_f(E)-P_g(E)| <= 1 - C(N-D,t)/C(N,t),  0<=t<=N.
```

This second bound concerns a uniform fixed-multiset permutation, NOT independent replacement. It does not assert the observed order of a real corpus is exchangeable. It also requires the type labels to be aligned; sorted ranks that reorder categories do not automatically define a same-label coupling.

## Precise no-go: small fitting error need not control expected complete discovery

Choose any integer m>=2 and put N=m^2,

```
f_m=(m^2-1,1),   g_m=(m^2-m,m).
TV(f_m/N,g_m/N) = (m-1)/m^2 -> 0.
IID E[T_f] = m^2 + 1/(m^2-1).
IID E[T_g] = m + 1/(m-1).
E[T_f]/E[T_g] > m/2 -> infinity.
```

Hence, even with exactly the **same K=2 support and fixed named categories for each m**, probability distributions can approach each other in TV while the expected IID full-collection waiting-time ratio diverges. This is a rigorous sequence of finite counterexamples: not a claim about universal empirical scaling, nor a contradiction with the finite-horizon coupling inequality.

For fixed t, `1-(1-TV)^t` tends to zero. The gap in expected waiting time comes from arbitrarily long rare-type tails and cannot be certified by checking only finitely many prefix horizons.

## Exact code and evidence status

- `scripts/zipf_discovery_fit_stability_exact.py` reuses existing rational PMF validation and the already committed completion-time CDF/mean owner. It creates no duplicate probability carrier.
- `tests/test_zipf_discovery_fit_stability_exact.py`: 6 focused exact rational tests of IID one-step maximal TV, the common-index permutation coupling, all small arbitrary same-N count pairs, wrong-domain gates, the explicit `m` counterfamily and finite-prefix convergence.
- New suite **6/6**, and the combined local three-file stochastic/completion/stability suite **26/26** passed. Source and test Git blobs match the locally executed bytes. Earlier archived full 27-topic Python suites have not been replayed at the current GitHub exact head; Agda kernel, matching CI receipt and full empirical replication remain pending.
- Acceptance shell runner and dedicated GitHub workflow include this 14th test module. Its presence is not evidence that GitHub Actions executed successfully.

## Scientific ceiling and next Pareto cut

This bridge gives a mathematically sound uncertainty *upper bound* for fixed-horizon predictions when the full labeled probability error is known. A head-only Zipf fit supplies **no valid bound** on `TV(p,q)` for the unseen support by itself. Thus the next source/data priority is to retain rare types, declare missing mass and tokenization, freeze a source corpus and chronological holdout, and report fitted-model alternatives and uncertainty. A successful synthetic test cannot replace acquisition of the actual source observations.

Master reconciliation, exact GitHub-head Python acceptance, compatible Agda typechecking of `DASHI/Statistics/ZipfFamilyEverything.agda`, and original sourced empirical replication remain release gates. Do not import a master-only Balaban/Ibrahim aggregate into the older Zipf branch to make a fictitious bridge. No ESD paths were edited.
