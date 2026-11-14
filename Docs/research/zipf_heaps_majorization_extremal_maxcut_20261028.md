# A sharp, all-prefix Heaps envelope and majorization theorem

**28 October 2026 · PR #1275 · scoped to the original 27 Zipf-family subjects.**

## Original-root and proof-status attribution

- The count budgets, majorization and finite permutation arguments are classical elementary combinatorics. The partial-order language follows Hardy, Littlewood and Pólya, *Inequalities* (1934); do not claim the majorization concept as a new physical discovery.
- Célestin Zimmerlin, Thomas Louail, Manuel Moussallam and Marc Barthelemy, “Dynamics of discovery and the Heaps–Zipf relationship,” *Physical Review E* **113**, 054304, **11 May 2026**, DOI https://doi.org/10.1103/543d-frbq, published the central temporal-order decoupling and extremal discovery-history motivation. Their models, analysis and empirical data are original to those authors, not newly invented by DASHI.
- New repository code, formalised finite identities, counterexamples and independently executed tests: Johl Brown with OpenAI ChatGPT assistance, 2026-10-28. **Not Agda-kernel-verified**: this is a constructive mathematical argument implemented in Python.
- Other Zipf/Estoup/Mandelbrot/Hurwitz/Heaps/Lorenz/Pareto and the original separate Monster 3B Ibrahim owners retain their dated attribution. No NSE, RH, Monster or Balaban recognition conclusion follows from these results.

## Mathematical theorem 1 — simultaneous sharp envelope

Fix **K positive integer type counts** `f_1,...,f_K` and **N = Σ f_i**, and let `f_(1) ≥ ... ≥ f_(K) > 0` be the same counts sorted decreasingly. Let `S_j = Σ_(i=1)^j f_(i)`, `S_0=0`. A sequence is any permutation of the fixed multiset; this is *sampling without replacement with exactly fixed terminal counts*, NOT IID draws.

For any prefix length `0≤t≤N`, the number of observed types `V(t)` satisfies:

- `L(0)=U(0)=0`.
- For `t>0`, `L(t) = min{j≥1 : S_j ≥ t}`.
- `U(t) = min(t,K)`.
- Every permutation satisfies `L(t) ≤ V(t) ≤ U(t)`.
- One **single** constructive permutation attains `L(t)` for every t: output *all tokens of type 1*, then all tokens of type 2, etc., in descending frequency order.
- One **single** constructive permutation attains `U(t)` for every t: output one token of each type first, then all remaining tokens in any order.

**Proof (no asymptotic step):** A prefix containing at most j types can contain at most the sum of the j largest counts `S_j`; hence no prefix of t tokens can have fewer than the first j satisfying `S_j≥t`. The descending grouped permutation attains that lower value at all t. Every new type needs at least one token, so `V(t)≤min(t,K)`, attained by the early-first-appearance construction.

Existing code `scripts/zipf_heaps_bridge.py:distinct_envelope` already gave per-prefix bounds. The added construction `extremal_multiset_token_orders` strengthens this into **one joint all-t witness**. `observed_prefix_diversity` and `multiset_heaps_extremal_profiles` provide independent exact surface checks.

## Mathematical theorem 2 — explicit all-prefix information-loss area

Define `G(f) = Σ_(t=0)^N [U(t)-L(t)]`. If type i first appears at time `b_i`, it contributes one to `V(t)` for `N-b_i+1` distinct prefix lengths. For the lower schedule, `b_i=S_(i-1)+1`. For the upper, `b_i=i`.

Thus the **sharp exact integrated ambiguity** is

`G(f) = Σ_(j=0)^(K-1) S_j - K(K-1)/2`

and, equivalently,

`G(f) = Σ_(i=1)^(K-1) (K-i)(f_(i)-1) ≥ 0`.

This is a finite integer identity. **Not** a Shannon entropy, randomness estimator, causal explanation or Hilberg scaling exponent.

Example: `f=(20,2,1)`, `N=23`: at `t=3`, the grouped schedule has 1 type and the early-first-occurrence schedule has 3; both have exactly the same full histogram, Zipf rank fit, head mass and end vocabulary. The integrated difference is **39 type-prefix units**.

## Mathematical theorem 3 — Pareto *concentration* widens possible temporal histories

Let f and g be two positive-count histograms with exactly the same K and N, sorted decreasingly. Suppose f **majorizes** g: `S_j(f)≥S_j(g)` for every `j<K` and totals equal.

Then for **all** prefix lengths `t`:

`L_f(t) ≤ L_g(t)`, `U_f(t)=U_g(t)=min(t,K)`, and `G(f)≥G(g)`.

Proof: the budget `S_j(f)` fills at least as many tokens using the first j types, so the minimal number of types needed for any t cannot increase. Summing the sharp lower-curve inequality gives the gap inequality, or directly use the explicit gap formula. The converse does **not** hold generally; the majorization order is partial, not a universal law for all pairs.

This is a **valid conditional Pareto/Lorenz-style head-concentration connection**. It is NOT a claim that a particular physical turbulence field, language, historical event or Monster representation has the same carrier as the histogram. It does not use Balaban renormalization-group methods.

## Executed validation and evidence boundaries

- New file `tests/test_zipf_heaps_extremal_profiles.py` has **8** tests. They exhaust all permutations of selected finite multisets, check simultaneous exact attainability and per-t extrema, confirm fixed-multiset hypergeometric expected vocabulary is bounded, reject invalid counts, and exhaust count-majorization pairs for K=2,3,4 with counts 1..4.
- Exact local Git blob parity: `scripts/zipf_heaps_bridge.py` **bee0ef16bc460e84029e3dcb4bf5c3f8bfff55e4**; new tests **f85b7c56c3fc238f394f489f9382644b8e6a6b95**; both were verified against GitHub after upload.
- Local nine older focused suites plus new file: **123 passed**. Some older local files are not GitHub-HEAD-identical; therefore **not** a claim of a 123/123 exact-head CI run. Agda remains kernel-pending.
- Current GitHub latest related PRs inspected: #1396 evidence non-promotion, #1391 same-physical-carrier NS nonpromotion, #1406 non-Archimedean source reuse. They reinforce source ownership and type gates but are not mathematical imports into this finite statistics module.
- **Balaban is not a critical path prerequisite.** PR #1275's current-master bridge note should be interpreted solely as optional provenance/interface context; there is no Balaban RG theorem needed for any item of the 27-statistical-subject acceptance.

## Next exact acceptance

Reconcile the diverged PR with master, rerun the updated ten-suite shell/CI against the **same GitHub commit**, and actually compile `DASHI/Statistics/ZipfFamilyEverything.agda` with a compatible standard library. Then, separately, connect the exact finite histogram/candidate laws to properly identified real source data. Test empirical models with explicitly frozen rank dictionaries, chronology, holdouts and alternative fits; the new sharp envelope itself does not imply that any observed sequence saturates it.

The original 27-subject ledger remains authoritative; this work **extends the existing Heaps/Zipf/Pareto carriers** rather than adding a 28th subject.
