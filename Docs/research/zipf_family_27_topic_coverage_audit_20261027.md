# Complete 27-topic coverage and nonpromotion ledger — 27 October 2026

**PR:** https://github.com/chboishabba/dashi_agda/pull/1275
**Scope:** original 24 Zipf see-also subjects + Zipf itself + Zipf–Mandelbrot + Hurwitz zeta, exactly **27 distinct topics**. This table matches `DASHI/Statistics/ZipfFamilyFiniteExact.agda` and `scripts/zipf_family_formal.py`. It is **not** a declaration that 27 empirical or analytic theorems have been proved.

**Verification:** locally `pytest -q tests/test_zipf_family_formal.py tests/test_zipf_family_crosslaw.py tests/test_zipf_heaps_bridge_exact.py tests/test_zipf_occupancy_collisions_exact.py tests/test_pareto_benford_lorenz_bridge.py tests/test_zipf_family_coverage_gates.py` gave **95 passed** in a local source snapshot. The newly added coverage implementation/tests have been verified Git-blob-identical to executed local copies. Earlier 79 local files remain not universally byte-identical to the GitHub head. **Agda kernel: UNVERIFIED**. No GitHub Actions CI result is claimed.

## Subject-by-subject owned carrier, exact check, remaining gap

| # | Original requested topic | Implemented operational carrier | Proof-status ceiling | Source/test owner | Unpaid scientific/analytic step |
|---:|---|---|---|---|---|
| 1 | Zipf law | finite rank PMF, counts, normalization | finite exact model | zipf_family_formal.py; zipf_heaps_bridge.py | Observed rank samples / real-exponent proof |
| 2 | 1% rule / 90–9–1 | creator, commenter, noncontributor tier fractions | diagnostic, not universal | zipf_family_coverage_gates.py:participation_roles | Recorded readers separated from inactive accounts |
| 3 | Benford's law | base-b first-digit expected/observed distributions; Pareto counterexample | model + exact finite statistics | zipf_family_formal.py; pareto_benford_lorenz_bridge.py | Held-out scale and digit tests |
| 4 | Bradford's law | journal productivity sorted and equal-output contiguous zones | finite optimized diagnostic | zipf_family_coverage_gates.py:bradford_optimal_equal_zones | Geometric progression fit and source query provenance |
| 5 | Brevity law | type-frequency versus declared word-length covariance | exact finite diagnostic | zipf_family_coverage_gates.py:type_level_brevity_covariance | Within-language conditional tokenization |
| 6 | Demographic gravitation | two-population inverse-distance parameterized attraction | conditional model | zipf_family_formal.py:demographic_gravity | Units, calibrations and confounders |
| 7 | Word list | type counts and stable ranked frequency table | exact finite representation | zipf_family_formal.py:word_list | Document/language/tokenization identity |
| 8 | Gibrat's law | growth ratios and size–growth covariance (not independence) | exact diagnostic / hypothesis | zipf_family_coverage_gates.py:gibrat_size_growth_covariance | Proper size-conditional distributional independence tests |
| 9 | Hapax legomenon | frequency exactly one under declared token equality | finite exact predicate | ZipfFamilyFiniteExact.agda; zipf_family_formal.py:hapaxes | Corpus and token-equivalence rule |
| 10 | Heaps' law | prefix diversity, finite IID / permutation expectation, variance | conditional exact finite identity | zipf_heaps_bridge.py; ZipfHeapsOrderNoGoExact.agda | Dependent stochastic process / empirical fit |
| 11 | Hilberg's hypothesis | block entropy plug-in estimator; same-unigram block-entropy no-go | finite diagnostic / hypothesis | zipf_family_coverage_gates.py:empirical_block_entropy; zipf_heaps_bridge.py | Entropy rate/excess scaling with stationarity and limits |
| 12 | Historical recurrence | dated matching event codes and distinct source roots | evidence-scoped observational relation | zipf_family_coverage_gates.py:coded_historical_recurrence | Events, temporal window, coding scheme, no automatic causality |
| 13 | King effect | largest-rank model deviation against second-rank baseline | descriptive diagnostic | zipf_family_formal.py:king_effect_ratio | Outlier null model and rank fitting with uncertainty |
| 14 | Long tail | rank-head versus tail mass under chosen threshold | finite exact statistic | zipf_family_formal.py:long_tail_share | Threshold selection and comparability |
| 15 | Lorenz curve | ranked cumulative share and Gini; Pareto model curve | finite identity / conditional model | zipf_family_formal.py:lorenz_curve; pareto_benford_lorenz_bridge.py | Nonnegative measurement and population sample |
| 16 | Lotka's law | author-output histogram, discrete output-count PMF | finite model / diagnostic | zipf_family_coverage_gates.py:lotka_author_productivity | Field scope, zero-output censoring and exponent fit |
| 17 | Menzerath's law | mean constituent length by whole length, parametric curve | finite descriptive diagnostic | zipf_family_coverage_gates.py:menzerath_empirical_means | Segmentation level and dependence/fit |
| 18 | Pareto distribution | Type I CDF, survival, leading-digit law and Lorenz | conditional exact model | pareto_benford_lorenz_bridge.py; zipf_family_formal.py | Fit/threshold, infinite-mean gate |
| 19 | Pareto principle | top-k contribution fraction; conditional 80/20 Pareto shape | finite statistic not a universal 80/20 law | zipf_family_formal.py:top_share; pareto_benford_lorenz_bridge.py | Population reference and selected cutoff |
| 20 | Price's law | top ceil(sqrt authors) share, empirical 50% diagnostic | hypothesis / exact finite count | zipf_family_formal.py:price_share | Nicholls 1988 challenges universality; field-specific validation |
| 21 | Principle of least effort | minimum cost versus observed cost regret | exact optimization / behaviour unverified | zipf_family_coverage_gates.py:observed_choice_regret | Preferences, feasible choice and hidden cost |
| 22 | Rank–size distribution | deterministic sorting and ordering | finite exact representation | zipf_family_formal.py:rank_size | No power law follows from sorting |
| 23 | Stigler's law of eponymy | documented naming versus original root and chronology | provenance diagnostic, not universal | zipf_family_coverage_gates.py:documented_eponym_gap | Primary documents; Stigler explicitly acknowledges exceptions |
| 24 | Letter frequency | casefolded alphabet-specific character counts | exact finite count | zipf_family_formal.py:letter_frequencies | Language, Unicode and source corpus |
| 25 | Most common words in English | corpus-specific deterministic top-k frequency | exact finite representation | zipf_family_formal.py:common_words | Representative identified English reference corpora |
| 26 | Zipf–Mandelbrot law | shifted finite-rank PMF, finite moments and normalization | finite exact conditional model | zipf_heaps_bridge.py:finite_rank_probabilities | General real/complex parameters, fractal identity not automatic |
| 27 | Hurwitz zeta | finite shifted rational sums / moments and convergent-tail bounds | finite exact identity; no analytic continuation | zipf_heaps_bridge.py:finite_hurwitz_sum | Complex continuation / Riemann/Eisenstein RH separately typed |

## Coverage interpretation

- **27/27** independently named in Agda/Python taxonomy and shown in this ledger; every subject now has at least an explicit operational function or typed original-source predicate, and the focused test suite includes direct or cross-law negative controls.
- **Numerical/exact finite computation** is not **Agda kernel proof**; only the previous repository's canonical PNF finite probability identity is imported. The newly source-written Agda family/Heaps/two-draw adapters still require typecheck.
- **No corpus replication:** word lists, letter frequencies, participation percentages, historical events and English top words are always **sample-dependent**. Synthetic numbers and synthetic original-root tokens are test fixtures, not historical discoveries or observational confirmation.
- **Pareto/Ibrahim max-cut:** preserve identity of semantic carrier and prior original mathematical authors; prevent count-collision, source-claim conflation and asymptotic model promotion. Reuse PNF expected-mass and canonical zeta owners; no Monster/NS/RH same-object inference from shared powers.
- **Snowball cut:** on each source, distinguish first scholarly publication, later reprint, critical replication, dataset and code; an inaccessible original scan is an acquisition debt, never fabricated a full-page verification.
- **Primary source corrections:** Bradford 1934 *Sources of Information on Specific Subjects* (1934 original; the 1985 journal item is later); Price, *Little Science, Big Science* (1963), rather than confusing Price's square-root heuristic with his separate 1976 cumulative-advantage work; Jakob Nielsen (8 October 2006) 90–9–1 heuristic acknowledged earlier Will Hill studies; Stephen Stigler's **April 1980** original paper names Robert K. Merton's earlier priority work and explicitly allows exceptions.
- **Conditional recent originals:** Dębowski JMLR 27(194) (2026), Zimmerlin et al. PRE 113 054304 (2026) and Santoro/Petri/Tria PRR 8 043083 (2026) are separately attributed. Our finite representations are NOT typechecked replications of their results.

## Audited original-root and later critical links

Bradford 1934 catalogued original: https://openlibrary.org/works/OL7427071W/Sources_of_information_on_specific_subjects .
Price 1963 original book named in 1988 critical original research: https://www.sciencedirect.com/science/article/pii/0306457388900490 (P. T. Nicholls; DOI 10.1016/0306-4573(88)90049-0).
Nielsen 2006 original 90–9–1 discussion: https://www.nngroup.com/articles/participation-inequality/.
Stigler 1980 original publisher root: https://nyaspubs.onlinelibrary.wiley.com/doi/10.1111/j.2164-0947.1980.tb02775.x .
Altmann's 1980 mathematical Menzerath formulation is referenced independently by https://pmc.ncbi.nlm.nih.gov/articles/PMC8230130/ ; source full original not audited.
Dębowski 2026 original JMLR: https://www.jmlr.org/beta/papers/v27/25-3192.html .
External Lean finite Zipf primary implementation (independent, do not vendor): https://github.com/TauCetiProject/TauCeti/pull/21232 .

## Next actual blockers

P0: exact GitHub-head all-test run and Agda typecheck of three source-written modules plus `ZipfFamilyEverything.agda` in compatible standard-library environment. P1: normalized constructive finite mass theorem and equality to PNF probability atoms rather than a supplied Boolean admission. P2: named real corpora and original bibliometric samples with immutable roots, tokenization rules, dimensional SI/coding choices and held-out fits. P3: genuinely analytic Hurwitz continuation/fractal/symmetry bridge only through the already-owned typed zeta/Eisenstein/RH interfaces, with no theorem transfer from coincidence or a shared exponent.

**No universal law has been established just by naming, defining, fitting, or matching a model.**
