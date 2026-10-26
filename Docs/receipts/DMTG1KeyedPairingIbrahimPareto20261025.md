# DMT G1 pairing integrity max-cut — 2026-10-25

## Original owners and exact objects

**Primary experimental authors:** Maria Niedernhuber, Dila Suay, Bigna Lenggenhager, Michael Müller, Milan Scheidegger, Dario Dornbierer and Helena Aicher, *Journal of Psychopharmacology* (2026), DOI 10.1177/02698811261481062. This work reports participant measurements and findings; no original human data were loaded here.

**Original analysis code:** `marianiedernhuber/DMT_microstates` at `c5c064d109563e97127403a8fbb340009ba1e88b`.
- `disemb_mc_Rprep.m` blob `3f58dde834189972410165cdd06392dea9220b33`: exports per-condition `coh.stats(idx).markov.G1`; it first combines condition columns, then removes any rows containing NaNs **jointly** before writing column vectors. This preserves positional alignment *if* the source cohort order already matches across conditions. It does not carry explicit participant IDs in the exported vectors.
- `microstates_statistics.R` blob `884d37c6155951a4af2e7b74b89be2a86ddf58be`: `readdat()` independently removes NA/non-numeric entries; `run_getstats()` checks **only the lengths** of the three files, builds `Subject=1..N` from row position and fits aligned-rank-transform repeated-measures ANOVA via **ARTool**. Source code alone does not prove the original output rows were misaligned; neither does equal vector length prove alignment. This is an evidentiary gap, **not a discovered author error**. Because the MATLAB exporter jointly removes NaN rows, the source pipeline has a partial alignment safeguard. The original ANOVA claims require actual subject-to-row provenance and original runtime state for independent reproduction.
- `check_counterbalance.r` blob `9716ab46f15782294e53ccf8e3588593653dbdfc` gives the original 25 participant prefixes; actual `getconds` and treatment assignment mapping still needed.
- Original `G1` statistic belongs to Tait & Zhang's published `+microstate` MATLAB toolbox, pinned reference source `a738a95c4218b8de76920e8333cef307126ef13f`, building upon earlier Billingsley/Kullback and von Wegner EEG analyses. Original 2026 installed toolbox version remains unverified.

## What the exact synthetic witness establishes

Take three labelled subjects. Their DMT G1 values are (10,20,30), placebo values are (8,18,28). With the source-verifiable order-preserving pairing, differences are (2,2,2), and their sample variance is zero. Permuting ONLY the unkeyed placebo rows as (28,18,8) preserves both per-condition marginal distributions, file lengths and the mean paired difference, but changes the signed differences to (-18,2,22), with positive sample variance. Therefore *marginal values and equal lengths do not identify the paired contrast variance or any repeated-subject model needing the join*. This is a synthetic nonfactorability example; it does **not** allege that the original researchers committed such a misalignment.

The latest related PRs support this bounded cut:
- **#1255**: existing `IntersectionalNonFactorability` reused for a finite order-erasure witness; chronological observation is not reconstructed from a bag of features.
- **#1259**: different phonological observation coordinates do not license semantic identity; likewise neural label-sequence G1 is not reported visual motifs or perceived external agency.
- **#1240**: proof-search/laboratory source-conditioned gates and original-object contact, rather than abstract success substituted for real execution.
- **#1258**: postselection can change conditional distributions without changing original unconditional evidence; similarly dropping NaNs per condition requires an explicit missingness/cohort join audit.
All these PRs remain independent and are not copied, imported or asserted merged into #1243.

## Implementation and interpretation

The new `scripts/audit_dmt_g1_keyed_pairing.py` requires named participant, arm, original-code identity, original G1 values, **source-defined samplewise versus jump-collapsed sequence type**, epoch-boundary provenance and contiguous-label sample count for every observation, with explicit condition/session and labelled-stream provenance. It refuses unkeyed marginal arrays, missing or duplicated arms, absent subject IDs, unrecognised condition strings, invalid G1 decimals and incomplete actual-source participant rosters. A separately digest-bound reviewer attestation is mandatory for proposed actual-study values, but such text is not cryptographic proof of legal rights, ethical authorization or raw measurement validity.

The constructed paired audit reports exact rational raw-G1 contrasts and the alternate `G1 / [2*(N-2)]` scale, the empirical triple conditional-information quantity, conditional on a **single contiguous labelled stream**. This normalised quantity is an exploratory *new* diagnostic, not the original author's reported ARTool analysis. If condition label counts differ, a raw-G1 comparison may partly reflect different triple opportunities; this code flags the unequal lengths and does not silently promote a normalized contrast into original ANOVA reproduction.

Tests: `tests/test_dmt_g1_keyed_pairing.py` (22 source-written synthetic regression cases) exercise positive pairing, permutation invariance when labels stay attached, unkeyed marginal rejection, variance collision, missing/duplicate/unknown conditions, sample-count and source hash admission, and separate review gates, including mixed/unknown label-sequence-type and unsourced epoch boundary rejection. **GitHub-head test execution not claimed** unless independently run.

## Current 2026 higher-order EEG method compatibility

The directly relevant original methodological analysis is F. von Wegner and collaborators, *A Quantitative Comparison of Two Methods for Higher-Order EEG Microstate Syntax Analysis*, *Brain Topography* (2026), DOI 10.1007/s10548-026-01196-5. Its distinction between **continuous/samplewise** label streams and **jump** streams is source-material: syntax and Markov null properties can change when self-transitions are collapsed. A study that only says “back-fitting to EEG” does not on its own resolve which sequence was tested. The keyed evaluator therefore requires an explicit, uniform sequence type and per-record epoch provenance rather than mixing both. This is a compatibility requirement for our source-level audit, not a claim that the 2026 DMT article omitted or mishandled it.

## Pareto / Ibrahim / snowball frontier (same-object inputs, not number of papers)

1. **P0 original analysis ordering**: recover `getconds`, original session/condition map, `coh.individual` iteration order and the **joint** NaN row-removal log with participant IDs. This single artifact family pays source-aligned `G1` inferential replay and the broader microstate-statistics ANOVA pipeline.
2. **P0 authorized byte and label stream**: verify rights/consent for the Zenodo `.set/.fdt` files, source MD5s, version-specific toolbox, clustering/maps, and exact sample counts. Reproduce original G1 on *identical labelled streams* before any reanalysis.
3. **P1 statistical sensitivity**: with verified keyed rows, rerun source-original ARTool workflow and compare missingness handling, condition order and sample length sensitivity. Apply first-order surrogates conditional on estimated first-order transition matrix rather than naive arbitrary shuffles when appropriate; this is a separate, literature-attributed diagnostic (von Wegner et al. 2026, DOI 10.1007/s10548-026-01196-5).
4. **P1 phenomenological distinctness**: maintain Sanders participant phases, Lewis-Healey TET, Erowid narrative categories as separately recruited/coded sources with their own authorization/crosswalk obligations. No same-person pooling or independent-agent ontology inference without a distinct observed restriction.

**Strict claim ceiling:** published original study exists; author scripts and Zenodo file metadata are located; G1 mathematical identity and source-export alignment risk are auditable; no actual author row mismatch, ANOVA reproduction, source licence, participant EEG reanalysis, independent experiment or external agent proof has been established.
