# Zipf → Heaps → Hilberg: conditional finite bridge and sharp information-loss gates

**27 October 2026; dedicated DASHI statistics PR #1275.** This is a 27-subject formalisation continuation; empirical laws remain hypotheses requiring independent data. Historical/original researchers own their work. This particular source-written adaptation and testing: Johl Brown with OpenAI ChatGPT assistance. No Agda kernel receipt.

## Primary recent scholarship and independent authorship

- Łukasz Dębowski, *From Zipf's Law to Neural Scaling through Heaps' Law and Hilberg's Hypothesis*, **JMLR 27(194)**, 1–35 (2026), https://www.jmlr.org/beta/papers/v27/25-3192.html . Published **conditional** Zipf→Heaps→Hilberg→neural-scaling deduction, with the Santa Fe process as an example. **We did not reproduce or kernel-formalise its full hypotheses.**
- Célestin Zimmerlin, Thomas Louail, Manuel Moussallam and Marc Barthelemy, *Dynamics of discovery and the Heaps-Zipf relationship*, **Phys. Rev. E 113**, 054304 (11 May 2026), DOI https://doi.org/10.1103/543d-frbq . Original result addresses dependence on ordering/temporal correlations, including bounding type-token curves. Our elementary finite envelope is NOT their stochastic result.
- Filippo Santoro, Alberto Petri and Francesca Tria, *Universalities in the avalanche dynamics of novelties and non-novelties and some notes on the Heaps law*, **Phys. Rev. Research 8**, 043083 (22 October 2026), DOI https://doi.org/10.1103/shhp-4dht . Original avalanche results suggest additional temporal discriminators; our finite novelty flags do NOT reproduce their model.
- Independent **open** TauCeti Lean PR https://github.com/TauCetiProject/TauCeti/pull/21232 provides a mathematically richer finite-Zipf distribution with reported Lean build/axioms checks. We borrow *only the checklist idea* (quantiles, finite/infinite relationship and explicit TV convention), no source, proofs or ownership.

Other historical original-source roots (Zipf/Estoup, Mandelbrot, Hurwitz, Herdan/Heaps, Hilberg, Lotka etc.) remain in `zipf_family_formalization_20261027.md`. Later research is never mislabeled as an independent original source for an older eponymous law.

## Finite Zipf–Mandelbrot and Hurwitz

For `N>=1`, integer `s>=0`, `q>=0`, `p_r=(r+q)^-s/H_N(q,s)`, `H_N(q,s)=Σ_(r=1)^N (r+q)^-s`. All masses are **exact rational**, normalized, with implemented CDF, least-crossing quantile for `0<t<=1`, and every integer nonnegative moment. For **any integer exponent** (including negative) the **finite** rational sum is valid and obeys the split `H_(N+M)(q,s)=H_N(q,s)+H_M(q+N,s)`; this does NOT establish complex analytic continuation or permit pole subtraction at s=1.

Exact binomial shifted-rank moment:
`E[R^m]=(Σ_(j=0)^m C(m,j)(-q)^(m-j)H_N(q,s-j))/H_N(q,s)`.
The source matches exact finite rank moments on sampled parameter lattices, not general real exponents.

## Two separate Zipf–Heaps sampling models

For declared **IID with replacement** PMF `p`, the expectation and incremental novelty probability are

`E[V_t]=Σ_i[1-(1-p_i)^t]`;
`E[V_(t+1)]-E[V_t]=Σ_i p_i(1-p_i)^t`.

Thus expected novelty increments decline (the second difference is `-Σ_i p_i²(1-p_i)^t<=0`). This does NOT assert that every individual sample path has concave type growth.

For **uniformly permuting a fixed corpus** of counts `f_i>0`, total `T=Σ_i f_i`, prefix `t<=T`, the exact hypergeometric expectation is
`E[V_t]=Σ_i[1-C(T-f_i,t)/C(T,t)]`,
with `C(a,t)=0` if `t>a`.

At `f=(2,2,2)` and `t=3`, permutation expectation is **12/5**, but IID with identical unigram probabilities `p=(1/3,1/3,1/3)` yields **19/9**. These models cannot be substituted into each other.

For any positive fixed multiset with counts sorted descending, a sharp vocabulary-count envelope over **all** orderings is:
- `min V_t = min{j: sum_(i<=j) f_i >= t}` for `t>0`;
- `max V_t = min(t,K)`, with both endpoints zero for `t=0`.

An exhaustive test checks **all 60 permutations** of a corpus with counts `(3,2,1)` at all seven prefix lengths. The new Agda `ZipfHeapsOrderNoGoExact` reuses the existing typed family and source-writes the finite histogram-to-prefix **nonfactorability witness**: `T,T,F,F` and `T,F,T,F` have identical histograms but different 2-token diversity (1 versus 2). **No Agda compiler run; source-written/kernel-pending.**

## Hilberg and avalanche nonpromotion

A fair IID bit process and a persistent fair-bit process both have **identical unigram distribution** `(1/2,1/2)`, but exact 2-block entropies are respectively **2** and **1** bit, and 4-block entropies are **4** and **1** bits. The exact local dyadic probability tests establish **unigram-to-block-entropy non-identifiability**, not a Hilberg exponent or refutation of Dębowski under his own additional hypotheses.

The words `aabbcc` and `abcabc` also share their histogram and final distinct-type total, but their chronological novelty flags are `101010` and `111000`. Basic run-length diagnostics differ; this is a bounded illustration inspired by, NOT replication of, Santoro–Petri–Tria's 2026 avalanche results.

## Total-variation convention

For a normalized finite PMF `p`, condition on first `K` ranks, `h=P(R<=K)>0`. Exact identity:

`L1(p, p|head)=Σ_r |p_r - (p|head)_r| = 2(1-h)`.

The statistical total-variation distance `sup_A|p(A)-q(A)|` is **half** that L1 norm, hence equals `1-h`. Do not silently transfer factor-two normalizations across libraries.

## Receipts and remaining Pareto/Ibrahim gates

- Newly committed `scripts/zipf_heaps_bridge.py`, `tests/test_zipf_heaps_bridge_exact.py`: **17 exact local tests passed**. **Both local files' Git blob SHAs were confirmed to match the fetched GitHub blobs.**
- Previous locally available 40 tests also passed, but their older local worktree versions are **not byte-identical** to current GitHub PR files. **Do not claim a complete exact-PR-head 57-test execution**.
- Source-written `DASHI/Statistics/ZipfHeapsOrderNoGoExact.agda` blob matches its local source. **Kernel-pending**; Agda unavailable in this runtime.
- P0: Agda typecheck/repair/import in canonical Everything; P1: more general finite real-exponent normalized distribution and proof-level moments; P2: original-source corpus/provenance and independent audits; P3: temporal-dependence and held-out Zipf/Heaps/avalanche discriminators; P4: genuinely established conditions before Hilberg/neural-scaling inference.
- No Zipf/fractal/zeta/NS/RH/Monster same-object or physical regularity conclusion from matching a power law. No universal behavioural/statistical law is asserted from a definition, model or synthetic test.
