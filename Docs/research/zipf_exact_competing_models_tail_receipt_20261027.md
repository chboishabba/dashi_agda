# Zipf-family severe-model discrimination: exact finite likelihood, tail and provenance

**Date:** 2026-10-27 (Brisbane), lane `chboishabba/dashi_agda` PR #1275.
**Original topic boundary:** the existing **27/27** original user items are kept intact. This work strengthens the distinction between a fitted Zipf/Pareto model and evidence that the population follows that model.

## Existing mathematical ancestry and credit

Original mathematical likelihood, multinomial sampling and conditional independence belong to probability/statistics, not this repository. Original source-root priority on robust power-law inference: Aaron Clauset, Cosma Rohilla Shalizi, M. E. J. Newman (2009), *Power-law distributions in empirical data*, SIAM Review 51(4), 661–703, DOI https://doi.org/10.1137/070710111 . They advocate threshold/parameter estimation, goodness-of-fit and alternative model comparisons; none of their paper's full statistical estimators has been reimplemented or validated here. Later conditional Zipf→Heaps→Hilberg work remains Łukasz Dębowski's 2026 JMLR paper: https://jmlr.org/beta/papers/v27/25-3192.html . The original Hurwitz recurrence belongs to Hurwitz 1882 / NIST DLMF https://dlmf.nist.gov/25.11 .

**Repository authorship:** Johl Brown with OpenAI ChatGPT assistance, 2026-10-27, of this bounded source implementation and exact tests. All previous named mathematical and empirical authors, repository/PR proof owners and Ibrahim Monster 3B owners retain their independent attribution. Neither a shared glyph/phase nor the same rank profile establishes any Monster, RH, fractal or NSE same-object transfer.

## Exact conditional finite score

Fix **K labelled ranks in advance**; do not rerank a held-out set by its own frequencies. For a normalized rational categorical mass vector `p=(p_1,...,p_K)`, and held-out nonnegative counts `c`, the score is the rational

`L(p;c)=product_(i=1)^K p_i^(c_i)`.

It equals the IID ordered-sequence likelihood up to a model-independent multinomial-count factor. For a fixed held-out frequency vector it gives the same ranking of candidates as the multinomial likelihood; it is not a p-value, posterior, independent-origin receipt, causal proof or distribution-fit certification.

A separately typed competitor is a **truncated geometric** rank model `p_r∝rho^(r-1)`, `0<rho<=1`, with exact rational normalizer. A predeclared parameter-grid Zipf model is supplied by the existing `finite_rank_probabilities` owner; there is no duplicate Zipf implementation.

Synthetic distinct countermodels:
- Counts `(64,16,4,1)`: normalized geometric ratio `1/4` exactly matches that sample's rank fractions and strictly out-scores the predeclared unshifted Zipf exponents 1 and 2.
- Counts `(60,30,20)`: the unshifted Zipf exponent 1 out-scores geometric ratio `1/2`.
- With **zero held-out observations**, all normalized candidates would return score 1, which is no model evidence. The candidate-selection function therefore **raises an error** rather than awarding an arbitrary lexical winner. Zero counts in one rank remain allowed for nonempty sample.

### Protected rare tails

For any fixed normalized PMF and **IID** sample of length N, if the first H ranks contain mass `m_H` then

`Pr(no draw from any rank>H | p, IID)=m_H^N`.

For `m_H<1` and finite N this may be strictly positive. Therefore observing no tail event does **not** prove a zero tail mass. Tail categories need explicit provenance and retention; deleting zero-frequency types before model comparison changes the declared support and may erase an evidential counterexample.

## O/R/C/S/L/P/G/F and stop conditions

**O:** distinguish exact finite rank likelihood from universal Zipf claims. **R:** existing finite Zipf/Hurwitz owner, the 27-topic registry and canonical PNF evidence/provenance owners. **C:** new `scripts/zipf_rank_model_evidence_exact.py` plus 7 adversarial tests `tests/test_zipf_rank_model_evidence_exact.py`. **S:** K finite, fixed rank dictionary, rational candidate PMFs, predeclared alternatives and declared sampling hypothesis. **L:** 27-family lane only; no Agda new claim owner and no ESD edit. **P:** train and heldout split identifiers must be distinct; a merely declared split cannot certify actual independence or data integrity. **G:** reject universal fit from score, and zero observations from selection. **F:** local source/test blobs match their GitHub connector hashes and **7/7 tests passed**; with older seven-suite local snapshot **110/110**. That **does not constitute exact GitHub PR-head 110/110**, because several older local blobs differ from current PR source.

**Remaining true proof/science debt:** execute CI against exact PR head; kernel typecheck Agda (not available locally); source-identify original real corpus/journal/population datasets; formally state threshold/censoring/ranking calibration and fit uncertainty; run proper power-law goodness-of-fit and alternative selection with complexity adjustment and dependence checks; preserve first-primary publication roots before claims. A synthetic exact likelihood example is a finite counterexample, **not a replicated empirical law**.
