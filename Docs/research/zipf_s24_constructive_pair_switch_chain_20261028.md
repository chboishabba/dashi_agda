# S24 constructive Heaps path coupling: pair switch and HLP-chain gluing

Date: 28 October 2026. Owner: [Zipf family PR #1275](https://github.com/chboishabba/dashi_agda/pull/1275). No ESD edits. This is *additional* to, not a replacement for, the original 27-subject registry or the previous max-flow witness.

## O: Concrete missing cut

The previous `zipf_s24_monotone_path_transport_exact.py` searched for a monotone coupling by finite rational max-flow and verified its row/column marginals. That was a correct **finite proof witness**, but did not construct the coupling from majorization's generating operations.

This continuation makes the general finite mathematical argument executable on bounded inputs **without max-flow search**. It reuses the original full-Heaps path distribution and certificate types. A single positive concentrating transfer is handled by coupled second-type arrival times; longer majorization relations are handled by positive integer transfer-chain reachability and exact rational Markov gluing.

## R: Original sources and earlier owners

- **Hardy, Littlewood and Pólya**, *Inequalities* (1934), majorization, transfer operations and their combinatorics.
- **Volker Strassen** (1965), “The Existence of Probability Measures with Given Marginals”, *Annals of Mathematical Statistics* 36:423–439, DOI **10.1214/aoms/1177700153**. This general coupling theorem is not a DASHI discovery.
- Classical elementary inverse-CDF/quantile coupling and probability disintegration/gluing.
- Prior repository source owners: `zipf_heaps_bridge._validated_counts`, `multiset_count_majorizes`, `zipf_full_heaps_path_distribution_exact.full_heaps_curve_law`, `zipf_s24_monotone_path_transport_exact.PathTransportCertificate` and `pair_one_type_survival_probability`. These remain intact.
- Prior SSSP six-permutation `ABC/ACB/BAC/BCA/CAB/CBA` modules and their independent 1 September 2026 commits retain ownership. Original Ibrahim Monster 3B proofs remain unrelated and unmodified.
- New *repository source implementation*: Johl Brown-directed, with OpenAI ChatGPT assistance, 28 October 2026. Historical mathematical priority remains with the original authors.

## C: New concrete algorithms

### 1. `scripts/zipf_s24_pair_switch_constructive_exact.py`

Input: any strictly positive finite histogram f, indices i≠j with f_i=a≥f_j=b≥2, sampler IID or uniform multiset permutation, horizon t. The concentrated histogram g changes only a,b to a+1,b-1.

The new `pair_switch_truncated_law` converts the **existing original S24 pair survival formula** `S(m)=Pr(T>m)` to the exact finite distribution of `min(T,H+1)` by `P(T'=k)=S(k-1)-S(k)` and `P(T'=H+1)=S(H)`. It handles **m=0** separately. For uniform permutation H=min(t,a+b); for IID H=t. The executable horizon cap is 14 for switch laws and 12 for complete transfer path receipts.

`quantile_ordered_pair_switches` constructs a common inverse-CDF coupling of the concentrated and original switch indices. It rechecks every switch-time row/column marginal and ensures `T_concentrated≥T_original` on every positive edge.

`_common_group_schedules` emits the same outer sequence of pair-group draws vs unaffected named types, with correct independent IID probabilities or hypergeometric remaining-token counts. This common outer sequence has the **same distribution** under the original and concentrated histograms because their pair count a+b and all other counts agree.

`_pair_curve` maps the common outer sequence plus each pair's switch index to the *entire* vocabulary-size curve. The pair contributes 0 if unseen, 1 before its second new type, and 2 afterward. Therefore the concentrated vocabulary curve never exceeds the original curve at any prefix.

`constructive_pair_transfer_path_certificate` multiplies common-schedule and coupled-switch rational weights, aggregates repeated pairs of curves, then **reuses the old certificate** with independent canonical full-path law marginals. Its `.validate()` checks all rows, columns and pointwise support. This is a constructive transfer, not a max-flow search.

### 2. `scripts/zipf_s24_majorization_chain_exact.py`

`positive_majorization_transfer_chain` performs bounded BFS on sorted positive integer count partitions. Every edge corresponds to a **literal** source transfer (a,b)→(a+1,b-1) with a≥b≥2, followed by a type-label permutation. The resulting path is recorded and independently checked. The search has a hard, explicit state budget; failure on budget does **not** imply a counterexample to integer HLP majorization.

`glue_monotone_path_certificates` composes two exact path couplings `γ_CB` and `γ_BA` by finite conditional disintegration:

```math
γ_CA(c,a) = \sum_{b:\mu_B(b)>0}
               γ_CB(c,b) γ_BA(b,a) / \mu_B(b).
```

Every positive edge respects `c≤b≤a` at all prefixes. The intermediate curve mass is required to match **exactly** in both certificates. The glued result rechecks normalization, both endpoint marginals and pointwise ordering. No duplicate probability carrier or unverified numeric tolerance is added.

`constructive_majorization_path_certificate` combines sorted-type relabeling, one-transfer certificates, and gluing. A length-zero chain gives a diagonal coupling. The final output uses the original requested labeled histograms, because Heaps vocabulary-size laws are invariant under type-label permutations, which the executable verifies by exact canonical PMF equality.

## S: Tests actually executed locally and proof ceiling

Both new Python source files were written to disk and executed against a **separate independent complete-word oracle**: IID `itertools.product` with exact `Fraction` word probabilities, and uniform physical multiset `itertools.permutations` with each distinct label sequence equiprobable.

- **94** chosen single-transfer, two-sampler, all-prefix cases were checked against this independent word-space oracle, with every joint coupling validated.
- **716** additional single-transfer inputs were checked for all valid (a,b) moves among 2- and 3-type count vectors with components in {1,2,3}, at each tested horizon.
- **804** majorization-chain/horizon/model combinations were checked over all 2- and 3-type histogram pairs with components in {1,2,3}, including equality and reverse-label permutations.
- **Nontrivial HLP chain** `(2,2,2)→(3,2,1)→(4,1,1)` returned a composed valid exact rational coupling for both samplers.
- The local reproduction used lightweight source-compatible shims for earlier imported modules, whose mathematical outputs were independently checked. The two **new source files' byte-identical Git blob SHA values** were verified by comparing `git hash-object` locally against GitHub `fetch_file` blob SHA: pair module `28d181f8c8be113144bf2c069fc6cd7529a74d36`; majorization-chain module `33aa8181e844a26ecc327bfc9d0a05f572b0f6ad`.
- Their companion GitHub test files were committed and registered in `scripts/check_zipf_family_acceptance.sh`. **The entire GitHub checkout, full test suite and Agda compiler were NOT run.** Do not promote local oracle checks to an exact-head full test receipt or kernel-certified theorem.

## L: Limits and no-go guards

The **mathematical fixed-horizon theorem** follows the classical HLP finite transfer chain and pair-switch coupling argument, but this Python implementation has explicit limits (sample horizon 12, count-partition search budget, finite number of group schedules). The general theorem's **Agda type**, transfer-chain normalization, conditional sampler laws and gluing proofs are still kernel-pending.

The previously committed counterexample to `S23 marginal order ⇒ S24 path order` remains valid: equal per-time marginals but a Hall deficit 1/2. The new construction derives path order from the **actual two-sampler structure** and does not use that invalid implication.

A joint path order for sampled Zipf histograms is **not** a universal empirical law of text, a Hilberg entropy theorem, a Fourier/pressure phase identity, a proof of NS/RH, a C6=S3 group isomorphism, or an Ibrahim Monster same-object representation. Original primary authors, earlier repo contributions, executable check owners, and Agda kernel verification status remain separate. No ESD/protected import graph changes.

## P/G/F: Next max-cuts

1. Prove **F13b `ConcreteAddLaw`** using a valid positive-denominator normalized rational interpretation, and run Agda on F13/F13b. Do not flip the adapter's existing identification Bool before this kernel proof.
2. Formalize the constructive finite **pair switch time distribution**, **inverse-CDF rational coupling**, **common-group schedule** and **full-path equality of marginals** as Agda theorems over existing PNF/finite distribution carriers.
3. Prove the **positive integer HLP transfer chain**, **relabel invariance** and **finite coupling gluing law** at the Agda kernel level; no unverified imported axiom.
4. Revisit **H08** arbitrary-count extremal witness and the 27 subject acceptance/empirical authority gates. Keep the independent ABC six-order source claims distinct.
5. Do not treat CI as the critical path, but preserve exact source-vs-executed-vs-kernel receipts.
