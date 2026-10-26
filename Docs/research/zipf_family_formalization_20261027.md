# Zipf-family 27-subject formalisation — source-first max-cut (2026-10-27)

## Scope and proof-status wall

**Sole focus:** the user-supplied 24 see-also topics, plus Zipf law, Zipf–Mandelbrot and Hurwitz zeta = **27 separately named surfaces**. Existing mathematics, empirical discoveries and source-text authorship remain attributable to their original researchers. This particular source-written implementation: **Johl Brown with OpenAI ChatGPT assistance (2026-10-27)**. A definition or finite test is NOT proof that natural languages, online communities, cities or journals follow a proposed distribution.

`DASHI/Statistics/ZipfFamilyFiniteExact.agda` supplies the 27-constructor typed taxonomy, distinct authority classes, original-root observation receipt, finite rational shifted-index sum, q=0 Zipf specialization, corpus-count additivity, corpus-relative hapax predicate and a rank/fingerprint nonfactorability theorem. The finite denominator/power carrier uses integer exponent/shift, **not all-real Hurwitz analytic continuation**. **Agda source-written; no kernel/typecheck receipt.**

`scripts/zipf_family_formal.py` implements 27 mathematical/observational APIs. `tests/test_zipf_family_formal.py` contains **27 targeted tests**, including negative examples. A materially equivalent local package passed 39/39 with pytest (27 named-law + 12 cross-law regression cases); exact GitHub blob has not been independently executed by a Python runtime and should be retested at the branch head.

## Complete semantic matrix

| # | Subject | Mathematical/operational object | Authority / original roots |
|---:|---|---|---|
| 1 | Zipf | finite rank mass proportional to `r^-s` | model; Estoup 1916, Zipf 1935/1949 |
| 2 | 1% participation | empirically observed lurker/active fractions | hypothesis, 90–9–1 literature; no exact 1% necessity |
| 3 | Benford | `Pr(D=d)=log_b(1+1/d)` | model; **Newcomb 1881** precedes Benford 1938 |
| 4 | Bradford | journals grouped into equal-output zones, ideal `1:n:n²` | empirical; Bradford 1934 |
| 5 | Brevity | word length × occurrence count joint observations | empirical; Zipf and quantitative linguistics |
| 6 | Demographic gravitation | `G P_i P_j / d^gamma` conditional model | Reilly/Stewart models; NOT Newtonian proof |
| 7 | Word list | tokenization-specific ordered frequencies | representation, exact corpus input |
| 8 | Gibrat | observed growth ratios; size-independence open | hypothesis; Gibrat 1931 |
| 9 | Hapax legomenon | frequency exactly one under declared token equivalence | exact finite count |
| 10 | Heaps/Herdan | vocabulary-prefix diversity; fit `K n^beta` | empirical; Herdan 1960, Heaps 1978 |
| 11 | Hilberg | parameterized entropy-block power growth | hypothesis; Hilberg 1990, later Dębowski distinct |
| 12 | Historical recurrence | repeated event-code predicate | observer-coded, no historical cause inference |
| 13 | King effect | rank-one outlier versus ranks 2+ fitted baseline | empirical diagnostic |
| 14 | Long tail | share after explicitly chosen top-K | exact conditional share |
| 15 | Lorenz | sorted cumulative population/quantity polygon, Gini | mathematical; Max O. Lorenz 1905 |
| 16 | Lotka | count-of-publications PMF across authors | empirical productivity, Lotka 1926; **not rank-size** |
| 17 | Menzerath–Altmann | `a n^b exp(-c n)` mean constituent size | empirical; Menzerath; Altmann 1980 |
| 18 | Pareto distribution | `1-(xmin/x)^alpha` above xmin | mathematical distribution; Pareto |
| 19 | Pareto principle | observed top-K mass, possibly but not necessarily 80/20 | empirical rule |
| 20 | Price | fraction produced by top `ceil(sqrt(N))` authors | heuristic, not identical to Price 1976 cumulative-advantage model |
| 21 | Least effort | feasible minimizer(s) of declared cost function | behavioural hypothesis, Zipf 1949 |
| 22 | Rank-size | nonincreasing vector of observed sizes | representation, does not assert power law |
| 23 | Stigler | mismatch between eponym and documented originator | provenance observation, Stigler 1980; Merton earlier |
| 24 | Letter frequency | specified alphabet/casefold and text counts | representation |
| 25 | Most common English words | top-K in specified corpus | representation, not fixed universal table |
| 26 | Zipf–Mandelbrot | `p(r)=(r+q)^-s/H(N,q,s)` | shifted model, Mandelbrot 1950s |
| 27 | Hurwitz zeta | `zeta(s,a)=sum_(n>=0)(n+a)^-s` | mathematical series for real s>1,a>0; continuation separate |

## Twelve additional cross-law falsification controls

The separately committed `tests/test_zipf_family_crosslaw.py` adds 12 checks. In particular, the same token histogram and exact Zipf rank distribution can yield different Heaps prefix trajectories when the token ordering changes: `a,a,b,b,c,c` versus `a,b,c,a,b,c` have the same counts, but cumulative vocabularies `(1,1,2,2,3,3)` versus `(1,2,3,3,3,3)`. No deterministic Zipf-to-Heaps *finite trajectory* map exists without an additional temporal/probabilistic hypothesis. Other checks cover shifted finite Hurwitz head/tail additivity, monotonic shifted Zipf PMF, Lorenz/Gini permutation and scaling invariance, Pareto survival conditional scaling, Benford base-dependence, King-baseline dependence, Gibrat size non-identifiability, tie-breaking and Price-uniform counterexamples.

## Exact algebraic bridges and invalid deductions

For **N>=1, q>=0, s>=0** the finite normalization `H(N,q,s)=sum_(r=1)^N (r+q)^-s` is positive. `q=0` is the finite unshifted Zipf model. For **s>1**, `H(N,q,s)=zeta(s,q+1)-zeta(s,q+N+1)`, derived from convergence of the two positive Hurwitz tails. At s=1 do NOT subtract divergent defining sums: finite H remains valid, while pole cancellation via separate meromorphic continuation is a different theorem.

Benford digit mass telescopes under logs, but neither Zipf nor heavy-tail observation entails Benford for an arbitrary dataset. Lotka indexes **publication output count**; Zipf indexes **rank**; these are not interchangeable. Heaps concerns **distinct vocabulary growth**, not token rank. Lorenz and Gini quantify observed inequality; Pareto 80/20 and Price 50%/sqrt are contingent sample-level tests. Menzerath may have an increasing segment depending on `b,c`. Stigler explicitly acknowledges exceptions: it cannot be formalized as a true universal quantification over all discoveries.

Counterexample families: uniform contribution data violate asserted 80/20; everyone active violates 1%; uniform authors fail Price's half-output; same rank vector cannot recover independent phase/author provenance; English top-K depends on corpus; Gibrat ratios and Menzerath trend can fail.

## Genealogy / original- versus secondary-source constraints

* Zipf/Estoup historical order: quantitative-linguistics publisher preview https://catalogimages.wiley.com/images/db/pdf/9781119625278.excerpt.pdf ; historical first editions need exact pages/hashes before quotes.
* Mandelbrot finite shifted law: https://ele-math.com/static/pdf/books/670-MIA15.pdf (later mathematical source, not original 1950s primary source).
* Newcomb (1881) and Benford (1938) distinction: https://benford.readthedocs.io/en/latest/Introduction.html (secondary history).
* Bradford journal scatter ideal ratio reproduced in https://files.eric.ed.gov/fulltext/ED045169.pdf (later reproduction; **not** Bradford 1934 root).
* 2019 primary empirical linguistic synthesis: https://pmc.ncbi.nlm.nih.gov/articles/PMC6731709/ and https://pmc.ncbi.nlm.nih.gov/articles/PMC7514498/ ; distinct dependent datasets/studies, not primary evidence for earlier eponyms.
* Menzerath original model genealogy in later text https://ira.lib.polyu.edu.hk/bitstream/10397/70922/1/Hou_Chinese_Menzerath-Altmann_Law.pdf .
* Derek J. de Solla Price, **1976 cumulative advantage** DOI https://doi.org/10.1002/asi.4630270505 ; do not equate it to square-root law.
* Stephen M. Stigler, **original 1980 publisher edition** DOI https://doi.org/10.1111/j.2164-0947.1980.tb02775.x explicitly allows exceptions; Merton prior theoretical contributor.
* Clauset–Shalizi–Newman (2009), DOI https://doi.org/10.1137/070710111 : power-law fitting requires null distributions, threshold estimation, alternatives and goodness-of-fit, not visual log-log slope.

These URLs are source identifiers only. No original scan/page hashes of all 27 empirical eponymous works have been audited in this PR. Do not count encyclopedia references, identical reprints and later quotations as independent primary roots.

## Repository reuse and acceptance

- Preserve canonical analytic `DASHI.Analysis.ZetaTheoremSurface` and separately `DASHI.Core.ParetoSymmetryQuotientAdmissionExact` / `NDimParetoHyperfabricExact` owners. The finite statistics library does **not** prove a new RH, zeta analytic continuation, fractal invariant, or a fluid regularity claim.
- Inspiration only from current PRs #1274 (typed retention), #1273 (fidelity fail-closed), #1259 (phonology/form vs semantic data), #1260 (finite Eisenstein vs analytic Riemann); no unmerged content copied.
- **Local verification:** 27 target cases passed with a materially equivalent Python module; **exact Github head not run**. **Agda compiler not available**, thus theorem source claims are kernel pending.
- Next proof-obligation Pareto cut: (P0) exact-head Agda/pytest; (P1) finite positive normalized PMF, CDF, moments and zero-shift Agda theorems; (P2) primary-source root acquisition and corpus-dependent estimators; (P3) goodness-of-fit/alternative models and dependent-sample rejection controls; (P4) separately typed optional applications to other programmes.

**Stop rule:** implemented definitions ≠ empirical confirmation; synthetic test ≠ corpus replication; Agda declaration ≠ kernel receipt; historical association ≠ priority proof.
## Primary source follow-through (27 October)

A direct 1926 root for Lotka's productivity distribution is Alfred J. Lotka, *The Frequency Distribution of Scientific Productivity*, *Journal of the Washington Academy of Sciences* 16(12), pp. 317–323, original 19 June 1926 journal object: https://www.jstor.org/stable/24529203 . Heaps's 1978 monograph is bibliographically identified as H. Stanley Heaps, *Information Retrieval: Computational and Theoretical Aspects* (Academic Press 1978), ISBN 0123357500, https://ndlsearch.ndl.go.jp/books/R100000002-I000006212405 . Robert Gibrat's original 1931 book/thesis is catalogued under *Les inégalités économiques ... d'une loi nouvelle, la loi de l'effet proportionnel*, https://search.worldcat.org/title/1024555751 . Bibliographic identification is not a full-page content audit or independent empirical replication.
