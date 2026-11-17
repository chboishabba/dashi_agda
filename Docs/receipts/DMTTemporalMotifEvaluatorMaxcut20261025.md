## 2026-10-25 correction: source-gated v2 supersedes original v1 instructions

The original v1 adapter and seven prototype tests have been replaced by a **v2 exact-source verified** adapter and **20/20 passing synthetic unit tests**. The current input is `dashi-dmt-temporal-motifs-v2` with explicit `mode`, predeclared `motif_vocabulary`, `source_collection_id`, four governance references, and each report's `independence_unit_id`. The evaluation withholds *all* reports from the same independent group at once and fits vocabulary-free (training-only frequency) denominators against a prespecified codebook; it is **not** report-only leave-one-out where recurring authors can contaminate training. Unknown motif labels, cross-source joins, raw narrative text, duplicate IDs, unverifiable chronology and synthetic-to-research relabeling are rejected. The research-data path additionally requires a separate reviewer receipt bound to the canonical dataset SHA256, specific rights scope and written-permission document hash. A receipt is a recorded reviewer assertion, **not** automatic verification of legal authority or chronology. No real data were admitted or inspected.

The precise committed Git blob hashes match those of the local files that passed `python -m unittest discover -s tests -v` from the focused test checkout: evaluator `531778ac881725fed0bbf382fbac50484fc982d2`, tests `68a284eddc74e48c1b420d4527ea1745908e453d`. A separate source-root/Ibrahim/Pareto update with the new EEG microstate deposit and explicit Sanders→Timmermann provenance is at `Docs/receipts/DMTSourceRootSnowballIbrahimPareto20261025.md`. Neither dataset-access authority nor kernel-checked Agda is asserted.

# DMT temporal motif admission: 2026-10-25 next max-cut

## Owner and attribution
The existing DASHI finite motif dynamics, ternary semiconjugacy, observer quotient, source hyperfabric and Erowid evidence audits remain canonical. This change supplies only a **conditional executable evaluation adapter** in `scripts/evaluate_dmt_temporal_motifs.py`, not a new mathematical kernel or empirically estimated matrix.

Original empirical source: Noah, Shen, Earth Erowid, Fire Erowid and Silver (2024), DOI 10.3389/fpsyg.2024.1397064. Original within-experience phase descriptions: Sanders et al. (2026), DOI 10.1093/nc/niag015. Do not join their participants, assume chronology from static narrative categories, or confer Erowid mining permission by citing a published article.

## Acceptance contract
The CLI expects a JSON object with `schema=dashi-dmt-temporal-motifs-v1`, `observation_unit=report`, source/governance references and a collection of independently identified report records. Each report must have a verified temporal ordering and at least two distinct integer ordinal positions carrying nonempty motif labels.

**Important:** this is only a *structural preflight*. The permission and chronology references are provenance pointers, not digitally validated permissions; the caller/reviewer must independently inspect the documents and confirm the coded sequence is genuinely supported. The synthetic tests use `synthetic-fixture-only` deliberately. Do not supply Erowid text unless access, reuse, and processing rights have actually been reviewed.

For each held-out report, transition counts are fit only from other reports, then compared with an additive-one static next-motif baseline using exact Fraction likelihood ratios. Reports, rather than transitions, are the holdout units. A ratio is a predictive diagnostic under the chosen smoothing and feature representation, not an evidential likelihood ratio for external-agent ontology. No individual report narrative, brain data or participant phases have been retrieved or analysed.

## Checks and blocker status
A matching local prototype ran seven synthetic unit tests successfully (not an exact GitHub-head execution receipt). New branch tests remain to be run on the precise committed source. The current code does not prove independent reporting-unit identities, category coding reliability, rights, temporal faithfulness or cultural/exposure/nuisance adjustment. It is a minimal honest bridge for later appropriately sourced evaluations, not a completed M1a-versus-M2 mechanistic experiment.

## Follow-on Pareto
1. Source-author permission and chronology review for report-level data; never scrape raw Erowid Vault by default.
2. Independent coder reliability, within-report ordinal uncertainty, source dataset identity and report/report-author duplication audit.
3. Baselines: M0 static frequencies, restricted M1a predictive-perceptual and selection/context models; M1b unrestricted observation-equivalent latent state remains the ontology ceiling.
4. Pre-register model restrictions, exposure/time variables, report-level held-out metrics and prospective predictions before interpreting any M2 preference.
5. Continue original Timmermann fMRI motion/cohort/preprocessing+rights and Sanders phase-matrix acquisitions as **separate source fibres**.

No Agda typecheck, empirical Erowid transition estimation, original fMRI replay or hidden-target experiment is claimed in this cut.
