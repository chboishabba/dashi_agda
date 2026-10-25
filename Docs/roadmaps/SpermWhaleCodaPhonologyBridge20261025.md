# Sperm whale coda phonology: source-bounded Agda/Animalexic bridge

Date: 2026-10-25  
Status: **source-written finite model; Agda typecheck and empirical replication not yet receipted**  
Formal owner: `DASHI/Biology/SpermWhaleCodaPhonologyExact.agda`  
Regression: `DASHI/Biology/SpermWhaleCodaPhonologyRegression.agda`  
Consumer root: `DASHI/Biology/AnimalexicEverything.agda`  
Runtime owner: `chboishabba/animalexic`, existing open PR #8 for candidate passive acoustic association.

## Original roots and accurate attribution

1. Pratyusha Sharma, Shane Gero, Roger Payne, David F. Gruber, Daniela Rus, Antonio Torralba, Jacob Andreas (2024). *Contextual and combinatorial structure in sperm whale vocalisations*. Nature Communications 15:3617. DOI: https://doi.org/10.1038/s41467-024-47221-8. Source-reported four factors: rhythm, tempo, rubato, ornamentation.
2. Gašper Beguš, Ronald L. Sprouse, Andrej Leban, Miles Silva, Shane Gero (2025). *Vowel- and Diphthong-Like Spectral Patterns in Sperm Whale Codas*. Open Mind 9:1849–1874. DOI: https://doi.org/10.1162/opmi.a.252. Source-reported `a`/`i` spectral categories and formant trajectories; cross-species source/filter analogy.
3. Gašper Beguš, Maksymilian Dąbkowski, Ronald L. Sprouse, David F. Gruber, Shane Gero (2026). *The phonology of sperm whale coda vowels*. Proceedings of the Royal Society B 293:20252994. DOI: https://doi.org/10.1098/rspb.2025.2994. Five source-reported phonology patterns.

These are **three distinct original studies**. Do not promote a press release, reprint, blog post or common Project CETI association into an independent corroboration. The present DASHI product-type witnesses and impossibility countermodel are new synthetic formalisation, **not the paper authors' experimental results**.

## What the 'whales speaking Chinese' analogy does (and does not) say

Mandarin tone contrasts can distinguish words containing the same segmental material. Mandarin tone and human vowel identity can combine across dimensions. Sperm whale coda click count/timing (source) and formant/trajectory (filter) likewise admit different combinations. These are **structural/acoustic correspondences**, not Mandarin speech by whales, demonstrated sperm-whale phonemes, a decoded dictionary, common subjective experience, or proven whale referential semantics.

The 2025 paper argues that source/filter mechanisms can vary partly independently. The 2026 paper adds evidence of **uneven empirical association** between vowel quality and coda type. These are compatible: product-type representability does **not** imply statistical independence.

## Quantitative reproducibility boundary: 2026 paper

The 2026 published methods state:

- Dominica Sperm Whale Project EC1 recordings collected 2014–2018; 15 female or immature whales.
- 3,948 temporally ordered, speaker-identified, manually annotated codas in the parent corpus.
- 1,144 focal codas with adequate audio/hand labels after exclusion of non-focal or noisy material.
- 1,066 codas for the main vowel-quality/coda-type analysis after omitting sparse coda types.
- 628 codas across four named whales for the focused 1+1+3 duration analysis.
- 760 codas for the adjacent-coda first-click mismatch/coarticulation analysis; adjacent codas separated by **less than 10 seconds** are eligible under the bout rule.
- Focal/non-focal classification and tag-deployment geometry must remain present to avoid confounding acoustic propagation.
- The original authors link original analysis data/code at DOI https://doi.org/10.17605/OSF.IO/9T6QU and supplementary material at https://doi.org/10.6084/m9.figshare.c.8383586. Neither has yet been downloaded, hashed, or executed by this implementation.

The published five result families, distinct from their confirmation in our code, are: (1) coda type–quality association; (2) generally longer a- than i-codas; (3) short/long i-coda duration modes; (4) between-whale baseline durations; and (5) adjacent-coda quality influencing mismatched onset clicks. The code records each as `SourceReportedFinding` with `replicatedFromUnderlyingData = false`, not as a proved theorem.

## Formal ownership and what is actually proved

- Reuses `DASHI.Core.AttributedSourceCore` for provenance without importing authority.
- Reuses `DASHI.Biology.AnimalCommunicationLatentExact` for species-local fibres and cross-species analogy firewall.
- Reuses `DASHI.Biology.AnimalCommunicationSemanticEvidenceExact` for semantic payment status.
- Reuses `DASHI.Culture.PhonologicalFeatureMatrixContrastExact` to prevent source-filter resemblance becoming a phonemic/lexical equivalence.
- Reuses `DASHI.Core.QueryIndexedProjectionAdequacyExact` to express an exact **synthetic** acoustic-observation/semantic-world adequacy defect.

Finite formal witnesses: two synthetic codas have identical source-coordinate structure and different filter constructors. A pair of synthetic worlds has one identical acoustic observation but different putative meanings; consequently no unrestricted acoustic-only function can recover those meanings. This is a conditional mathematical indistinguishability result, **not** evidence that real whales have or lack particular meanings.

## Pareto remaining work (no authority jumps)

1. **P0 — kernel payment.** Typecheck focused files and `AnimalexicEverything.agda` using the repository's pinned Agda/library toolchain. Fix compiler errors if any, retain exact command/output/hash.
2. **P1 — real data lineage.** Fetch the OSF/figshare original data/code; preserve hashes, original schema, DTAG calibration, annotation revisions, focal/non-focal exclusions, per-whale identity and same-coda provenance. Do not fabricate source measurements.
3. **P2 — direct paper replication.** Re-run quality/type association, within-whale duration model, i-duration multimodality, identity random effects and the edge-click adjacent-coda model; compare point estimates/CI/heldout splits against published figures with explicit mismatch receipts. Preserve conditioning sets (especially 1+1+3, whale subset, focal tags).
4. **P3 — Animalexic integration.** A thin **candidate-only** adapter from coda event/click/focal tag/timing/formant features to existing scene/interaction/latent schemas. Reuse passive acoustic localization and many-to-many AV associations; never equate an array of overlapping clicks with a uniquely identified sender.
5. **P4 — strongest functional discriminator.** Test cross-context receiver response and ethical non-invasive playback, cross-clan out-of-sample transfer, and matched null models before considering communicative function. Source-form regularity alone cannot pay semantics.

**Explicit residual:** no Agda kernel receipt, no fetched same-object source corpus, no reproduced published estimates, no animal-to-Mandarin translation, and no promotion authority from human-language analogy.
