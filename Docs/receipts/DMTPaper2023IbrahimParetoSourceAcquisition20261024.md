# DMT empirical contact — Ibrahim / snowball / Pareto source-acquisition cut
**As-of 2026-10-24. Source-first, consumer-relative, no fabricated subject IDs.**

## Provenance roots and paper-specific cohort rules

**R0 PRIMARY study root:** Christopher Timmermann, Leor Roseman, Sharad Haridas, Fernando E. Rosas and collaborators, *Human brain effects of DMT assessed via EEG-fMRI*, PNAS 120(13) e2218949120 (2023), DOI [10.1073/pnas.2218949120](https://doi.org/10.1073/pnas.2218949120). The original research group collected the participant data and reports the primary measurement; DASHI does not own those results. The paper states fMRI, EEG and analysis scripts deposited at [timmer500/DMT_Imaging](https://github.com/timmer500/DMT_Imaging).

**R1 ORIGINAL analysis denominators, source-authored, NOT necessarily disjoint people:**
- 20 completed participants with paired DMT/placebo conditions.
- **Main static fMRI**: four excluded for >20% scrubbed volumes with FD threshold 0.4 over **the 8-minute post-DMT window**. Therefore the main whole-brain GFC claim **t(15)=3.11; p=0.007; 95% CI [0.028,0.15]** uses **16** paired participants.
- **Original dynamic fMRI**: three *additional* exclusions based on the **whole 28-minute session**. The stated sequential arithmetic yields **13** eligible for that particular dynamic rule, barring any measure-specific deviations; subject identities NOT source-verified.
- **Joint EEG-fMRI**: 12 survived both modality rules. EEG main plots have other filtering/exclusion criteria; never substitute a generic EEG n for fMRI.
- The repository README says 15 passed motion correction; treat this as an incompletely specified *repository/analysis-revision* count, not a correction that replaces the original 16-person static analysis. Later 2025 DMT whole-brain-dynamics papers report 15 or 14 under their own motion criteria, and 2026 mega-analysis n=16 refers to previously acquired DMT data. These papers are reuse/derivative branches, not independent primary experiment roots.
- Actual per-subject original FD/scrubbing masks, exclusion IDs, original static GFC final values and exact preprocessing/analysis correspondence are **not established by filenames or the public README**. The person-ID debt stays open.

**R2 EXACT code/data repository root:** [b35701d88d904e2f602164ff2eae0fc879772078](https://github.com/timmer500/DMT_Imaging/tree/b35701d88d904e2f602164ff2eae0fc879772078). The existing source-tree receipt at [DMTImagingPinnedSourceTree20261024.json](DMTImagingPinnedSourceTree20261024.json) records 56 source files, 40 parcelled-fMRI .mat files (20 subject pairs) and five *regional EEG regressor* .mat files, with Git blob IDs and sizes. The files' existence does not certify n=16/n=13 eligibility, participant consent scope, original pipeline correspondence, or current legal permissions.

**R3 RIGHTS/TRANSFER:** The PNAS primary statement deliberately makes the material available on GitHub. The inspected exact public repository tree does **not** contain an explicit LICENSE/LICENCE/COPYING/NOTICE file; GitHub's own licensing documentation cautions that public visibility and forking do not supply an unrestricted reuse/redistribution licence. Thus: **access/discovery = observed; unrestricted rehosting/commercial/derivative permission = unverified; no patient-level raw bytes will be committed to DASHI**. Record research-rights/consent guidance or written author/institution permission before redistribution or uncertain reuse. This is a provenance/rights gate, not a claim the original paper's publicly deposited data are inaccessible or unlawfully published. This environment could fetch GitHub text and file inventory, and the GitHub connector returns base64-encoded MAT files, but the local execution container cannot resolve raw.githubusercontent.com; therefore no independently hashed participant data have been materialized locally or analyzed in this cut.

## IBM / Ibrahim provenance traversal: bounded source object graph

This route follows the **user's existing repo method**: typed primary object → stable DOI or exact Git ID → source lineage → consumer gap → lowest-cost verified acquisition. Existing owners: `DASHI.Core.AttributedSourceCore`, `DASHI.Core.SnowballAttributionProvenanceInvariantExact`, `DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact`, `DASHI.Core.DiscriminatorSynthesisExact`, `DASHI.Governance.AnomalousExperimentalDesignFarCrossPollinationExact`. Mark Ibrahim, Christopher Danforth and Peter Dodds (2017), *Connecting every bit of knowledge: The structure of Wikipedia's First Link Network*, DOI **10.1016/j.jocs.2016.12.001**, own their historical graph result; applying source navigation to DMT is a DASHI methodological extension, **not** a purported historical Ibrahim first-link edge. QIDs/Dewey are optional classification/navigation only; no inferred QIDs and no ontology/proof authority from adjacency.

Source edges by evidentiary role:
1. R0 DOI → R2 Git repository/commit: **primary author's explicit data-deposit statement**, confirmed.
2. R2 Git blob IDs → participant data-content SHA256: **not yet fetched/independently computed**.
3. R0 main static claim → R0 supplementary QC-motion threshold rule: **published analytic protocol**, n=16 supported; *actual subject IDs* still open.
4. R0 first-author data contact address `cbt14@ic.ac.uk` as **source-public contact**, not consent to automated outreach or personal-data release.
5. Timmermann 2023 → 2025/2026 reanalyses: **dependent secondary analyses** unless proved independent participant recruitment and new data. Different results, eligibility and source manifests remain separate evidence objects.
6. Timmermann 2023 → Sanders/Millière/Demšar/Daily et al., *Micro-phenomenology of immersion and perceived presences under DMT* (2026), DOI **10.1093/nc/niag015**: **related protocol/data root under active participant-identity audit**; 23 interviewed (21 complete matrices), 125 categories. Do **not** count as independent participant replication without recruitment-ID comparison. This is more directly relevant to perceived-agency dynamics than form constants.
7. Separate DMT dose-response candidate: Lewis-Healey et al., *Time-resolved Neural and Experience Dynamics of Medium- and High-dose DMT* (2026), DOI **10.1162/JOCN.a.2423**, 19 participants; source-level article, access to synchronized data unverified.
8. Independent **methodological** comparator: psilocybin PsiConnect 62-participant OpenNeuro [ds006110, v1.2.0](https://openneuro.org/datasets/ds006110), paper DOI **10.1038/s41586-026-10910-z**. Independent experiment and public dataset, but **different drug and participants**: may validate neural/experience methods, never DMT entity ontology.

## Consumer-indexed non-scalar Pareto frontier

An action is preferred for **retiring existing live obligations per verified primary object**, not for growing a bibliography. Vector axes: (number/type of relevant obligations retired, independent source strength, same-object specificity, cost/access burden, privacy/rights/quality risk). We do not collapse those into a fabricated one-dimensional expected truth score.

| Frontier | Next primary object / route | Live consumer leaves | Payment ceiling / stop |
|---|---|---|---|
| **A: highest dependency fan-out** | Author/archived source **participant FD/motion vectors + original inclusion list** for each static 8-min, dynamic 28-min and joint modality analysis | Exact analysis-cohort membership; eligible paired files; censoring/quality reproduction; source-specific GFC; validation splits | Cannot infer missing IDs from downloaded .mat filenames or later reanalysis; if source object not public, request from primary data custodian rather than search more reviews |
| **B: parallel high-value, low modelling cost** | Exact commit/source MAT objects, local Git SHA1+SHA256, documented reuse/consent terms; replicate **PNAS GFC t(15)** with frozen 8–16 min window | Data-origin contract, signal dimensions, computation/effect direction, reproducibility and rights | Public Git availability ≠ unlimited redistribution. No claimed original result reproduction until exact cohort/preprocessing and test agree |
| **C: directly discriminating phenomenology** | Sanders et al. primary 2026 category/phase-matrix dataset & provenance (125 categories; 21 complete interviews), plus Lewis-Healey synchronized DMT EEG/experience source | Agency-emergence temporal order, intra-/interparticipant observer reliability and stronger endogenous alternative; candidate independent discriminators | Phenomenology cannot establish unavailable-target information transfer or independently conscious beings |
| **D: independent-method stress test** | PsiConnect ds006110 v1.2.0 data dictionary + trained/frozen evaluator across contexts | Neural observation/prediction model transport, nuisance control and context sensitivity | Psilocybin dataset is **not** replication of DMT |
| **E: dormant until after B/C** | More Klüver projections, free Q=DAP encodings, historical first-link QID breadth, extra papers sharing same participants | No presently unpaid model/empirical claim is closed | Stop; avoid citation-count-as-evidence and wrapper growth |

## Executable arithmetic receipt (source aggregates only)

`python scripts/audit_dmt_pnas2023_published_gfc.py` independently recomputes **p=0.007169260405410824** from **t=3.11, df=15** and checks consistency of the reported rounded 95% CI. It infers **n=16**, not 15. **No raw DMT participant data are used** and this is *not* a reproduction of the original 112-region functional connectivity matrices. Source-specific static GFC candidate `scripts/evaluate_dmt_paired_fc.py` now requires an explicit 16-person static-motion inclusion manifest and an 8–16-min post-bolus window with TR=2s, plus a separately supplied preprocessing/alignment source reference; no actual data run has been completed.

**Next completion frontier:** secure A (official motion vectors/inclusion record) and B (rights and data bytes) first, then run the locked primary static claim; in parallel progress C for direct experience/agency predictions. Source author contact is public and can be used for a permissions/analysis manifest request with the user's authorization; no correspondence has been sent by this PR.


## 2026 direct phenomenology result recovered (source genealogy, not promotion)

Primary paper: **James W. Sanders, Raphaël Millière, Ema Demšar, Zachary G. Daily, David Erritzoe, Robin Carhart-Harris, Christopher Timmermann**, *Micro-phenomenology of immersion and perceived presences under DMT*, Neuroscience of Consciousness (2026), DOI **10.1093/nc/niag015**. The credited investigators interviewed 23 people; two incomplete interviews meant **21 phase matrices** in the structural temporal analysis, with **125 phenomenological categories**. The paper reports that, among cases where perceived presences emerged, **multisensory effects (including bodily) and 3D spatial characteristics were present beforehand or concurrently**. The authors also report a κ=0.72 inter-rater agreement for category assignment. These are retrospective time-order and coding-reliability observations, **not verified external consciousness or a causal intervention**.

The article's actual *Data availability* statement is **"Data from this manuscript is available upon reasonable request to the corresponding authors."** Corresponding contacts are publicly given as `james.sanders.25@ucl.ac.uk` and `c.timmermann@ucl.ac.uk`. The data's public article and illustrative figures do not constitute unrestricted access to full interview transcripts/phase matrices. Request anonymised phase matrices, coding dictionary, reliability/adjudication, recorded temporal granularity, interview consent/reuse scope, and a recruitment/cohort-overlap crosswalk against Timmermann 2023 before any cross-study independence claim. Nothing was requested or transmitted by DASHI.

**Prospective discrimination:** freeze two independent test axes before looking at a future cohort: (a) whether reported presences ever occur *before* multisensory+3D experiential scaffolding under a time-locked protocol, and (b) whether any sealed concealed-target information is recovered after robust leakage controls. The first is a **phenomenological structural hypothesis** observed by Sanders et al., potentially favourable to some endogenous-generation accounts, but not uniquely predicted by them; the second is an information-source test. Crossing them after data does NOT automatically establish entity ontology. Neither an unverifiable agent-cooperation variable nor free interpolation through a Markov kernel counts as a falsifiable point prediction.

## Current permission/acquisition status

Primary PNAS 2023 paper expressly deposits fMRI, EEG and scripts at GitHub, but no explicit machine-readable **licence/consent/reuse permission** appears in the pinned source tree. GitHub's licensing guidance says a public repository without a licence defaults to retained copyright; reading/forking is distinct from unrestricted derivative redistribution. Treat internal scholarly reproduction and external redistribution as **separate legal/consent consumers** requiring jurisdiction- and use-appropriate review. The GitHub connector was able to return one .mat source blob as base64 with its exact Git identifier, **but no participant array was transferred to the local scientific-computation container or independently analysed** because the container network is restricted. A claim that the source files are unavailable online would be false; a claim that a human-data replay is complete would also be false.

## Pinned acquisition command (execution environment and rights permitting)

The source-locked acquisition helper is `scripts/acquire_dmt_imaging_source.py`. It requires a **nonempty written rights/consent/use review record before cloning**, checks out exactly commit `b35701d88d904e2f602164ff2eae0fc879772078`, refuses an existing destination, and verifies **every** acquired file's expected size and Git SHA1 object identity against the committed source-tree receipt. It never commits participant files or infers clinical-consent rights. Synthetic tests `tests/test_dmt_source_acquisition.py` cover missing-review refusal and corruption failure.

```sh
python scripts/acquire_dmt_imaging_source.py \
    --destination /secure/approved/DMT_Imaging \
    --rights-review-record /secure/approved/reuse_review.txt
python scripts/preflight_dmt_imaging_data.py \
    --data-root /secure/approved/DMT_Imaging \
    --manifest /secure/approved/analysis_manifest.json
python scripts/evaluate_dmt_paired_fc.py \
    --data-root /secure/approved/DMT_Imaging \
    --manifest /secure/approved/analysis_manifest.json
```

The source-locked exact Python acquisition and new post-correction synthetic tests were **committed, not executed against raw files in this environment**. The only freshly executed arithmetic receipt is the public-paper aggregate check: `python scripts/audit_dmt_pnas2023_published_gfc.py` returned p=0.007169260405410824 from t=3.11 and df=15. No participant values are implied.

The source repository's accompanying right to view/fork and the paper's GitHub data-deposit statement are documented, but a specific request for permission to rehost, publicise any participant-derived products, or redistribute derivatives is **not closed** by a nonempty `reuse_review.txt`. A real review must state purpose/jurisdiction/consent/security/outputs and resolve restrictions where needed.

### Exact next external custodian request (not sent)
Ask the corresponding original-study data custodian for:
- **Subject ID lists and FD/scrubbing masks** behind original static eight-minute **n=16**, original full-session dynamic **n=13**, joint EEG/fMRI **n=12**, and the README's separate **n=15**; include session date/condition mapping and revisions.
- Frozen **112-parcel** static whole-brain GFC calculation, treatment of diagonal, used time samples/bolus alignment, preprocessing version and results table sufficient to reproduce **t(15)=3.11, p=0.007, CI [0.028,0.15]**.
- Express scope of reuse/redistribution of Git-deposited human fMRI/EEG data and scripts, privacy/consent constraints, preferred acknowledgement and publication policy.
- From the 2026 Sanders et al. corresponding authors separately, anonymised **21** phase matrices, **125** category codebook, phase timing and participant-lineage crosswalk (published access rule: reasonable request).

If the request cannot be fulfilled, report the exact-source admission block rather than guessing the subject list or substituting a secondary n=15/14 analysis.


## 2026-10-24 follow-up implementation / custodian acquisition outcome

**New tested owner:** `scripts/derive_dmt_original_motion_cohort.py` with `tests/test_dmt_original_motion_cohort.py`. It requires exactly 20 pseudonymous per-subject DMT FD arrays, a sourced 2-second TR/bolus alignment and source/QC provenance. It applies FD >0.4 mm and strictly >20% scrubbed TRs separately to the 8-minute post-bolus window and the 28-minute full scan, preserving the n=16 static / n=13 dynamic distinction. This is a **candidate formal operationalisation of the described source rules**; the exact author-side full-window filtering and condition-specific nuisance pipeline still require the original QC receipt. If actual FD input differs it **blocks**, never adjusts a threshold to force a sample count. Four synthetic tests were executed locally (**4 passed**), including exclusion boundaries, invalid FD and cohort-count discrepancy.

**Primary data contact:** a draft request to the publicly listed original-study corresponding researcher was attempted through the connected email draft capability, but the application required user approval/login and it was declined. **No email was drafted in Gmail or sent; do not retry without new user instruction.** Exact requested material: per-analysis pseudonymous IDs, FD/QA arrays, bolus/TR alignment, original static GFC pipeline, distinction from README's n=15, and explicit reuse/redistribution terms. For future voluntary correspondence a request can be copied from the exact problem statement in this ledger; this repo change is not a request to contact a third party.

**Acquisition in this runtime:** full public binary MAT retrieval into the Python computation container was not possible because container networking fails name resolution. The GitHub connector can independently show the original file's MATLAB 5.0 header and compressed matrix tag, but that does not equal complete validated matrix extraction or independent source-replay. Existing file-tree SHA1 receipts remain the exact source anchors. The runnable pinned acquisition utility requires user-supplied locally reviewed rights/use record and works only in a network-enabled environment.

**Pareto status:** no more derivative bibliography or extra nominal formalisms; obtain the actual primary author FD/QC file or documentation and permitted file bytes, then execute/compare the original 16-person static analysis. In parallel, request-only Sanders phenomenology phase matrices remain higher-value for agent-experience hypotheses than additional visual form-constant modules.

## 2026-10-24 exact original author-code namespace receipt

**Positive primary-source object:** the original author-script `timmer500/DMT_Imaging/Scripts/StaticGFC.m` at pinned Git blob **f87d99f448848c3b0531fea0780ee241ebd77549** explicitly enumerates pseudonymous IDs **S01,S02,S03,S06,S07,S08,S09,S10,S11,S12,S13,S14,S15,S16,S17,S18,S19,S22,S23,S25**. The set equals exactly the **20** subject prefixes in the 40 paired DMT/placebo source `.mat` entries (separate independent Git tree receipt). Therefore **the source's subject namespace is now found and paired**, but the original static n=16 QC-eligible list, which four people exceeded threshold, and exact code/experiment same-object output remain OPEN.

**Scoped negative primary-source object:** the same 56-file pinned tree does not include a standalone `tapered_sliding_window.m` (nor any source path of that name), although `Scripts/dRSFC.m` calls `tapered_sliding_window`. The negative search was made against **that precise repository tree**, not against the original authors' drives, other scientific repositories, installed MATLAB paths, or the world. The source-world world status is therefore `knownAbsent` *within that Git revision* and yields **no self-contained dynamic-source replay route** from that tree alone; a future different repository/version could supply it.

**Source genealogy, not independent replication:** this original script and repository remain manifestations of the **same Timmermann 2023 root**. Sanders 2026 is a distinct published source root whose interview participant overlap still needs evidence, and Brain-IT is an unrelated method dataset. The library currently holds seven attributed source records but only **three lineage roots**. These counts must not be used as independent experimental sample size.

**World proof-search:** the runtime verifies the author-script Git object against the separately pinned tree, requires all 20 IDs to match file prefixes and rejects a mutation. New `--candidate-artifact` / `--candidate-receipt` options dry-run which consumers would be selectively reopened by a *proposed* new source but do not change any artifact from `notLocated` to `present`, resolve permissions, or contact authors.

## 2026-10-24 source-object mismatch discovered: static GFC is NIfTI/atlas, not BOLD_AAL

Exact author script: [StaticGFC.m](https://github.com/timmer500/DMT_Imaging/blob/b35701d88d904e2f602164ff2eae0fc879772078/Scripts/StaticGFC.m), Git blob `f87d99f448848c3b0531fea0780ee241ebd77549`, Christopher Timmermann (script header 2022). Lines 5–23 load `Schaeff1007NExt.nii.gz` and subject/condition-specific author-local preprocessed NIfTI images; lines 26–42 construct ROI means and correlations; lines 62–121 apply `atanh`, aggregate and call a paired t-test. The public source tree contains **40 parcelled BOLD_AAL MAT files**, not those processed NIfTI/mask assets. Those .mat arrays may be useful for exploratory statistics but are **not demonstrated to be the original script's same-object measured input**.

The pinned tree also lacks the particular NIfTI and atlas file objects. This is an EXACT-GIT-TREE-scoped `knownAbsent` record; the author-side versions, pipeline code, and resulting series remain `notLocated`. The script uses `nets` prior to an in-file definition and refers to `xdata`, `ydata`, `fdrcorrection` and NIfTI-related MATLAB functions, requiring an actual executed-source/workspace receipt before claiming line-equivalent reproduction. No criticism of the primary paper's data validity is implied.

**Source-world consequence:** original-static empirical claim now needs original n=16 FD/QC, access authorization, original processed NIfTI, atlas, effective MATLAB workspace, and independent matched replay. The corrected FIVE-action conditional path is a dependency proposal only: original QC, rights/access, original voxel-NIfTI/atlas acquisition, effective author execution state, and static-GFC replay. The public BOLD_AAL MAT files are NOT a necessary source input to this original NIfTI-based analysis. The `BOLD_AAL`-only purported exact reproduction has no declared route. The live Pareto frontier retains the independent author-code/workspace recovery even when another QC acquisition reaches overlapping consumer labels. No participant data, rights status or paper measurement was promoted.


## 2026-10-24 corrected consumer-indexed Pareto and no-promotion admission

The public `BOLD_AAL` MAT deposit and original source `StaticGFC.m` voxelwise NIfTI route are two distinct input representations. The latter cannot be reconstructed by granting additional credibility to the former, nor is downloading the latter a precondition for an *exploratory* MAT calculation. Source-world `c_static_reproduction` no longer depends on `source_local_bytes`. Its **five-step hypothetical** path requires original motion/preprocessing, consent and rights scope, the NIfTI and `Schaeff1007NExt` atlas, effective MATLAB workspace, and measured replay. No original participant data was acquired or replayed.

`scripts/evaluate_dmt_paired_fc.py` now refuses a manifest calling itself `original_static_gfc` even if source hashes pass. A parcelled-data exploratory manifest must name `exploratory_parcelled_static_fc`, the `BOLD_AAL_MAT` input type and `exploratory_not_source_equivalent`. These declaration tokens are **not evidence** of source, QC or rights authenticity: external source review and file-hash preflight remain separate; the result always retains `matching_paper_measurement_reproduced=false`.

The source scheduler now blocks actions that claim to recover an artifact marked `knownAbsent` **within a specific pinned source tree**, while preserving searches for the equivalent function or data under different source coordinates. It distinguishes three bibliographic source genealogies from independent participants: 2026 Sanders participant overlap remains unresolved. A source graph or higher consumer count cannot create biological or philosophical proof.


## 2026-10-24 locally executed exact-blob regression receipt

**Environment:** isolated Python 3.13.5 container, with installed pytest, numpy, scipy. Local network could not resolve GitHub directly, so fourteen source files were retrieved from the connected GitHub branch, transported through a temporary native Google Doc text export and reconstructed in a local test directory. For all fourteen original files, local `git hash-object` matched the GitHub source-content blob SHA. The one changed test file was updated on GitHub, reconstructed locally, and independently hash-checked against new Git blob `3f4d7df3e988fc9a1c206d980878f1a79f00ce9b`.

**Initial execution:** `python -m pytest -q tests/test_dmt_source_world_search.py tests/test_dmt_paired_fc.py tests/test_dmt_original_motion_cohort.py tests/test_dmt_source_acquisition.py` → **1 failed, 36 passed**. The source-world inventory test accidentally counted all `fMRI/` entries as participant MAT files, but original pinned tree contains **40 paired MAT objects plus `fMRI/temp`**.

**Corrected execution:** same four-suite command after one regression-test repair → **37 passed in 0.84 s**. The production runtime, source world and source-tree receipt were unchanged by the correction. Independent executable CLI checks: `--consumer c_static_reproduction` returns the five-action **conditional** original NIfTI route; `--consumer c_public_mat_reproduces_original_static` correctly returns `no_declared_source_route`. The published-number audit executes and gives `2*scipy.stats.t.sf(3.11,15)=0.007169260405410824`, i.e. the reported `p=.007` is arithmetically consistent.

**Scientific authority:** this is a genuine exact-source Python test receipt for synthetic fixtures, metadata identity, source-action logic and an aggregate t/p audit. Original 16-person QC identities, voxel NIfTI, atlas, source-equivalent MATLAB workspace and independently recomputed human metrics remain **unlocated and unreproduced**. This does not certify the Agda aggregate, for which an Agda compiler is unavailable in this container. Data use and redistribution permissions remain unresolved.


## 2026-10-24 exact Git commit/tree correction, phase decision and verification

Original upstream `timmer500/DMT_Imaging` commit `b35701d88d904e2f602164ff2eae0fc879772078` **does not share its hash with its Git tree**. Original Git REST `git/commits/{sha}` reports tree SHA **`38bdb12d180303f1738b7c5b6d99f34f157c26f9`**. A full `git/trees/{tree}?recursive=1` read returned `truncated=false`, 56 blobs; **all 56 source receipt paths, content blob SHA1s and byte sizes matched**. Both pinned source-world receipts have been corrected; the source runtime now refuses commit/tree conflation. This pays repository-source inventory **provenance**, not original NIfTI study measurements.

The [Dewey/Ibrahim/snowball/Pareto acquisition dossier](DMT2023DeweyIbrahimAcquisitionDecision20261024.json) provides six typed producer/consumer research search bundles, four currently non-dominated source targets, and no invented precise DDC or QID coordinates. The [restricted model cards](DMTRestrictedModelCards20261024.json) specify M0/M1/M2 against matched held-out observations and preserve the separate unapproved M3 information channel and unidentifiable M4 ontology claim. These are DASHI-designed **future tests**, not original authors' published findings, fitted models, or completed preregistration.

**Executed local audit:** `python -m pytest -q tests/test_dmt_source_world_search.py tests/test_dmt_paired_fc.py tests/test_dmt_original_motion_cohort.py tests/test_dmt_source_acquisition.py tests/test_dmt_research_phase_audit.py` returned **48 passed in 0.80 seconds** from locally Git-hash-matched source files. The source-world snapshot records current file hashes and corrects outdated unrun-test assertions. Original 16-person motion identities, original cleaned voxel NIfTI and atlas, effective MATLAB execution state, source-permitted use and participant-data effect reproduction remain **open**.
