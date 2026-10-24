# DMT EEG G1 source-owner trace — 25 October 2026

## Attribution (preserve every origin)

1. **General mathematical origins:** Billingsley (1961) and Kullback and colleagues (1962) developed Markov-order likelihood-ratio tests. Do not credit the original statistic to DASHI, an AI implementation, or the 2026 DMT investigators.
2. **EEG-specific origin:** F. von Wegner, E. Tagliazucchi, H. Laufs (2017), *Information-theoretical analysis of resting state EEG microstate sequences — non-Markovianity, non-stationarity and periodicities*, *NeuroImage* 158:99–111, DOI `10.1016/j.neuroimage.2017.06.062`. Original paper investigates EEG non-Markovianity, not DMT or external entities.
3. **Independent published software implementation:** F. von Wegner (with 2018 co-authored software/methods work), [Frederic-vW/eeg_microstates](https://github.com/Frederic-vW/eeg_microstates), file `eeg_microstates3.py` original repository blob `290cbc3e7f22b822450d264b9603c999ef3886ae`, contains `testMarkov1` and the identical positive-count ratio `2*sum n_ijk log(n_ijk*n_j/(n_ij*n_jk))`, with Chi-square df `K(K-1)^2`. This is separate code verifying the mathematical form, not an independent DMT participant study.
4. **Original MATLAB toolbox implementation:** L. Tait and J. Zhang (2022), *+microstate: A MATLAB toolbox for brain microstate analysis in sensor and cortical EEG/MEG*, DOI `10.1016/j.neuroimage.2022.119346`. Original [plus-microstate/toolbox](https://github.com/plus-microstate/toolbox) pinned commit `1ce32466bbd49b9751bbe8575a8b7422ff2540fe`; exact `+microstate/@individual/stats_markov.m` blob `a738a95c4218b8de76920e8333cef307126ef13f` computes `G1` from observed three-consecutive-label counts, replacing zero cells with machine epsilon before logging. It calculates `p1=1-chi2cdf(G1,K*(K-1)^2)` asymptotically.
5. **DMT experimental source:** M. Niedernhuber, D. Suay, B. Lenggenhager, M. Müller, M. Scheidegger, D. Dornbierer and H. Aicher (online 22 September 2026), DOI `10.1177/02698811261481062`. Their source `disemb_mc_Rprep.m` at commit `c5c064d109563e97127403a8fbb340009ba1e88b` exports `coh.stats(idx).markov.G1` and analyses DMT/harmine, harmine-only and placebo groups. This is the original human-study claim, NOT independent validation by DASHI.
6. **Local DASHI adaptation:** `scripts/audit_dmt_microstate_G1.py` and `tests/test_dmt_microstate_G1.py` reproduce the **positive-count mathematical expression** on synthetic integer label sequences. The calculation is equivalent to `2(N-2) I(X_{t-1};X_{t+1}|X_t)` using empirical triple frequencies, under a single contiguous stream and consistent conventions. This identity is standard conditional mutual information algebra, not a novel theory. The source MATLAB's zero-cell epsilon regularisation can produce tiny numerical differences.

## Completed mathematical and documentary discriminators

### Independent enumerative arithmetic check (performed outside the GitHub checkout)

A separate local Python/NumPy count-cube implementation with the *original MATLAB axis convention* (next/current/previous) was compared against a separately implemented simple positive-support G1 count function. Enumerating all (3^n) label sequences for (n=3,4,5,6,7) (total **3,267** sequences) gave **maximum absolute G1 difference = 0.0** in the local run. This verifies the *mathematical count-index equivalence on this bounded synthetic domain*, NOT the exact GitHub-file runtime, missing-state/epsilon behaviour of the original MATLAB, or any original study participant data. The test sources committed in this PR are still pending their own Python execution receipt.


An independent local Python arithmetic calculation on the constructed 12-label sequence `[1,2,3,2,1,2,1,3,2,1,3,1]` yields `G1=2.7725887222397807`, consistent with `4 log 2=2.772588722239781`. A repeating `1→2→3` cycle, a deterministic alternating sequence and a constant single-state sequence yield `G1=0` on their stated supports. Reversal leaves this three-label conditional-dependence statistic unchanged. These results belong to synthetic mathematics, not to the original EEG patients; 14 dedicated regression cases were committed, **not run at current GitHub head**.

The source-level join is now precise: author participant IDs align with 25 Zenodo recording pairs; the original three-condition MATLAB pipeline is located; the exact original G1 estimator in its donor package is located; an independent original Python software formulation matches the statistic. None of this alone establishes:
- that original `.set/.fdt` recordings have been downloaded, legally admitted or integrity-verified;
- the effective author `getconds` extraction, condition order, data timing, preprocessing or original microstate fitting labels;
- precise library/toolbox versions used in 2026 (the pinned 2022 donor is *compatible code*, not demonstrated executed version);
- any original DMT/harimine participant G1 distribution or original p-value;
- any external independently conscious entity.

**Remaining Pareto max-cut:** acquire licensed original EEG + source condition crosswalk and `getconds` helper, recover effective author toolbox/tool versions and fitted maps, then run original MATLAB/R and cross-check against the local G1 calculation on identical label sequences. Respect participant-level pairing and author `NaN` row filtering; never infer subject independence from trial, epoch or motif counts. No universal hidden-state ontology is identified by G1.
