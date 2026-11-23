# P0-A3 — exact unequal-variance pooled-window selection obstruction

**Date:** 22 November 2026, Brisbane. **Source:** Connie X. Wang, Isaac A. Hilburn and colleagues, *Transduction of the Geomagnetic Field as Evidenced from Alpha-Band Activity in the Human Brain*, *eNeuro* 6(2), 2019, DOI [10.1523/ENEURO.0483-18.2019](https://doi.org/10.1523/ENEURO.0483-18.2019). Published EEG protocol, data and all physiological conclusions belong to original authors, with raw-file custody at [CaltechDATA D1.930](https://doi.org/10.22002/D1.930) and [D1.931](https://doi.org/10.22002/D1.931).

**Original source versus DASHI extension:** the original study pooled experimental conditions to select an individualized most-negative time–frequency window and evaluated alpha event-related desynchronization; it did **not** state the exact Gaussian theorem below. The symbolic result, simulations, test code and false-positive design belong to the present independent **synthetic** audit. No original participant bytes were retrieved; therefore this is **not** a replication, criticism established on observed condition variances, or a claim of biological artefact.

## Exact theorem (two-window independent Gaussian null)

Four cell values for each candidate window are independent, centered Gaussian with variances **v_AS, v_AF, v_SS, v_SF > 0**. Define pooled mean M=(AS+AF+SS+SF)/4 and interaction C=AS−AF−SS+SF. There are **two independent candidate windows**. Select the window with the smaller pooled mean, then calculate its interaction. Since C and M are jointly Gaussian in each window, E[C|M]=(Cov(C,M)/Var(M))M. Standard normal order statistics imply E[min(M1,M2)]=-sqrt(Var(M)/pi). Thus:

    E[C_selected] = -(v_AS - v_AF - v_SS + v_SF) /
                    sqrt(pi * (v_AS+v_AF+v_SS+v_SF)).

This is exact under the stated two-window independent-Gaussian assumptions. It is **zero** under equal condition variances, and more generally when the **signed sum of the four variances is zero**. It is nonzero when that signed sum is nonzero, without any actual experimental or biological mean effect. The sign is determined by the signed variance contrast. The original paper uses correlated time–frequency windows, wavelets, trials and other conditioning, so the actual numerical magnitude **cannot** be transferred to Wang's experiment without original-data replay.

## Local SymPy 1.14 + NumPy/SciPy synthetic execution

[Executable owner](../../scripts/radiobio_heteroscedastic_window_sympy.py) specifies seed 20261122, **5,000 independent synthetic studies per case**, 29 virtual participants per study, 2 candidate windows per participant, 4 experimental conditions. Exact formula verified with SymPy; Gaussian draws and one-sample two-sided t-test of participants' matched selected contrasts simulated.

| Synthetic case, [v_AS,v_AF,v_SS,v_SF] | Exact mean bias | Simulated selected mean | Selected false positive (alpha=.05) | Heldout false positive |
| --- | ---: | ---: | ---: | ---: |
| Equal [1,1,1,1] | 0 | +0.00232 | 0.0536 | 0.0536 |
| Higher active-sweep variance [4,1,1,1] | −3/sqrt(7*pi) ≈ −0.63973 | −0.65288 | **0.2596** | 0.0564 |
| Higher active-fixed variance [1,4,1,1] | +3/sqrt(7*pi) ≈ +0.63973 | +0.63871 | **0.2506** | 0.0464 |
| Unequal but variance-cancelling [4,2,4,2] | 0 | −0.00217 | 0.0522 | 0.0480 |

**Interpretation:** the earlier iid equal-variance synthetic null is insufficient to clear the window-selection sensitivity in general. But the counterexample does not prove the original data have this imbalance, or that the authors' empirical statistics were biased. The independent heldout halves return near-zero interaction and near-nominal rejection rates here, by design. Always compare original-source effect estimator, actual window-selection procedure, trial counts, artifact correction and statistical randomization against this *distinct* mathematical model.

## Revised acceptance gate

1. **Original dataset admission:** retrieve the original MATLAB scripts and first .mat subject from the original CaltechDATA object store; verify Caltech catalogue MD5; use original script condition mappings rather than guessed data layout. Earlier signed-URL attempts remain **BLOCKED** in this environment; do not claim any real EEG results.
2. **Original preprocessing replay:** recover source-defined ERP subtraction, 100 frequency bins, wavelet dependencies, baseline, 6–14 Hz candidate search, condition-specific trial balancing and original per-person tests before synthetic alternatives.
3. **Variance diagnostic:** for each subject/time–frequency window compute trial-level residual variances by condition (active sweep, active fixed, sham sweep, sham fixed), and signed variance contrast. Include heterogeneity across subjects, serial correlation, artifacts and condition-specific missingness. Compare source-selected training vs held-out scores. Pre-register split and repeat over split seeds.
4. **Source versus extension:** original author's ANOVA and controls on their complete data first; independent crossfitted and variance-matched analyses second. Report both without changing the original target or claiming discovery of bias from synthetic effects.
5. **Stop condition:** a synthetic significance rate or symbolic theorem must not be presented as human EEG validation, or as evidence for / against intercellular radiative coupling, geomagnetic consciousness, Schumann entrainment or a covert research programme.

**Attribution rules:** [Docs/SourceAttributionPolicy.md](../../Docs/SourceAttributionPolicy.md); [ScientificSourceAttributionRule.md](../../Docs/support/reference/ScientificSourceAttributionRule.md). The first implementation of this DASHI extension is the feature-branch commit creating the script; it does not inherit priority for the original 2019 finding.
