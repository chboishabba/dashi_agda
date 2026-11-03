# Wong et al. (2022) D-lysergic-acid evidence crosswalk

> **Current scope: DASHI Biology/Chemistry only (3 November 2026).** No SensibLaw, SLR, ITIR, external ontology connector, review store, or cross-repo runtime handoff is required for this tranche. Previous companion work is deferred, not an acceptance dependency.

**Primary source:** Garrett Wong, Li Rong Lim, Yong Quan Tan, Maybelle Kho Go, David J. Bell, Paul S. Freemont and Wen Shan Yew, *Reconstituting the complete biosynthesis of D-lysergic acid in yeast*, Nature Communications **13**, 712 (2022), DOI [10.1038/s41467-022-28386-6](https://doi.org/10.1038/s41467-022-28386-6). Credit experimental observations and article authorship to this team, not to DASHI.

**Scope:** Non-operational, provenance-first formalisation of source-reported analytical and outcome evidence. This module does **not** reconstruct a wet-lab route, assemble an organism, supply sequence/plasmid or process parameters, optimize production, claim a validated commercial process, or establish pharmacological/clinical effects.

## Exact source-scope claims

- The paper reports reconstitution of D-lysergic-acid biosynthesis in engineered baker's yeast.
- It reports product-identity checks by mass spectrometric analysis and NMR and a stable-isotope origin experiment. The work remains source-reported until independently checked.
- It reports endpoint titres of **1.7 mg/L at 1 L** and **1.4 mg/L at 4 L**. These are two experimental observations, not a scale law, not a per-cell rate, and not a downstream fermentation forecast.
- PubChem gives lysergic acid CID **6717** (C16H16N2O2). The existing Kluver source atlas identifies lysergic acid **diethylamide** as CID **5761** (C20H25N3O). Similar vocabulary or molecular relationship does not license same-compound substitution.
- The paper's ability to produce a precursor does not itself demonstrate 5-HT2A receptor activation by the product, any psychedelic subjective effect, or therapeutic efficacy.

## Golden versus adapter ownership

- `DASHI.Biology.Wong2022LysergicAcidFiniteCore` is the self-contained `{-# OPTIONS --safe #-}` finite grammar. The four disjoint-constructor proofs live there. It imports only the Agda builtin equality definition.
- `DASHI.Biology.Wong2022LysergicAcidEvidenceExact` is the source-linked adapter. It imports legacy Biology, Chemistry and attribution owners that are not all marked safe. It does **not** claim its entire import graph is a Golden safe graph.
- No kernel acceptance is claimed until the commands in W22-07 run on the exact head. A safe option on the isolated core cannot prove independent source science or certify a legacy module's dependencies.

## Existing owners reused, without duplicate mathematical or ontology authority

| Task | Existing owner | Connection in this PR |
|---|---|---|
| Source authorship, DOI, role and no-promotion invariant | `DASHI.Core.AttributedSourceCore`; `Docs/SourceAttributionPolicy.md` | Typed article and PubChem citations; non-promotion proofs |
| Molecular identity and related receptor context | `DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact`; `Kluver5HT2AMolecularProteinInstantiationExact` | Reuses existing LSD identity; explicitly forbids DLA/LSD tag collapse or receptor-efficacy transfer |
| Tryptophan / serotonin pathway disambiguation | `DASHI.Biology.MonoamineBiosynthesisPathSeparationExact` | Reuses tryptophan vocabulary; distinct biological claim domains |
| Open cellular metabolism | `DASHI.Biology.Cell.OpenMetabolicNetwork` | Parametric unpaid network-consumer gate; no invented flux or state |
| Chemistry transition and quantitative obligations | `DASHI.Chemistry.TransitionKernel` | Existing solver-neutral kernel is the future consumer; no source-backed kinetic measurements are asserted |
| BH4 / Rhea / ChEBI and external ontology | [DASHI #1159](https://github.com/chboishabba/dashi_agda/pull/1159), [#1226](https://github.com/chboishabba/dashi_agda/pull/1226), [#1454](https://github.com/chboishabba/dashi_agda/pull/1454) | Separate biochemical source/kinetic/ontology programs; do **not** infer a shared network or import unmerged branches |
| Scientific mechanism evidence | `DASHI.Core.ScientificMechanismEvidenceBidiExact` | Existing observation/source interpretation and independent-evidence reverse obligations |
| Stoichiometric theorem reuse | `DASHI.Biology.Cell.MetabolicStoichiometricConservation` | Conditional existing conservation certificate; no new paper-specific physical flux witness |

## Minimal exact remaining cut

1. **W22-01: Source reproducibility.** Pin the article version and source-data file digests. Retain figure/table/analytical-evidence locators. A DOI by itself does not prove that the downloaded supplement was inspected.
2. **W22-02: Registry same-object identity.** Confirm stereochemical and charge/formulation qualifiers for the specific DLA assay. Map PubChem and ChEBI IDs through reviewed external identifiers. Never equate precursor and derivative.
3. **W22-03: Observation normalization.** Add source-pinned scale, endpoint timing, replication and uncertainty for each value if the paper's source data support them. No interpolation or optimizer.
4. **W22-04: Independent analytical evidence.** Review raw source-data rows against the paper's claims. Treat a paper-described assay as author evidence, not new DASHI validation.
5. **W22-05: Cellular network bridge.** Only instantiate the existing `OpenMetabolicNetwork` or chemistry transition kernel after source-grounded organism/compartment/time, rate-unit, transport and calibrated-flux witnesses exist. No such witness is asserted here.
6. **W22-06: DASHI-only scientific and stoichiometric owner reuse.** `Wong2022ScientificMetabolicBridgeExact.agda` reuses `ScientificMechanismEvidenceBidiExact` and `MetabolicStoichiometricConservation`. Source-written bridge complete; kernel execution remains W22-07. Physical flux remains W22-05; no external connector is needed.
7. **W22-07: Exact-head execution.** Run `python3 scripts/check_wong2022_scientific_evidence.py`, `python3 -m pytest tests/test_wong2022_scientific_evidence.py -q`, then `python3 scripts/check_wong2022_scientific_evidence.py --agda` for Golden core, source adapter, ledger, scientific bridge and Biology root. Record exact revision, checker version, and result.

## Source-to-proof ceiling

The Golden finite-core terms `dLaTagDistinctFromLsdTag`, `productionEvidenceNotReceptorEvidence` and `reportedStatusNotIndependentValidation` prove **disjoint constructors in DASHI's finite evidence grammar**, not experimental correctness of chemical identity, metabolic same-object correspondence, or industrial performance. The source attribution core proves only that citation is not a theorem or authority.

Original experiment/figures belong to Wong and collaborators; the stable identifier entries belong to PubChem and their database curators; all newly authored finite evidence types and bridge terms are DASHI source code. The original biochemical discovery and receptor literature owners remain independent.

This work deliberately contains **no assembly protocol, gene list, reaction recipe, culture settings, or output-improvement instructions**.

## 2026-11-03 max-cut continuation: source locators and native world projection

Primary-article text was checked against the publisher's public article page. This supports the *source-reported* reading only:

| Paper object | Source locator | Evidence claim | Present receipt |
|---|---|---|---|
| Analytical product comparison | Fig. 5; Supplementary Fig. 14 | Article reports comparison of detected product with reference | Article text indexed; raw analytical files not reanalysed |
| NMR comparison | Supplementary Table 11 (cited in paper text) | Paper reports chemical-shift comparison | Source-data binary still not downloaded/verified |
| Isotope origin | Article isotope-tracing results | Paper reports labelled-input origin evidence | Article statement observed, not independently reproduced |
| Endpoints and replicate scope | Fig. 6 and Supplementary Table 12 | 1.7 mg/L (1 L), 1.4 mg/L (4 L); Fig. 6 caption reports three biological replicates | Numeric means, standard deviations and underlying worksheet rows not independently checked |
| Registry cross-reference | PubChem CID 6717 public identity and external reference listing | Formula C16H16N2O2, external identifier CHEBI:6604 | Registry *candidate* only; assay specimen same-object and source release independently unverified |
| Related but nonidentical chemistry | PubChem CID 5761, existing Kluver owner | Lysergic acid diethylamide is a distinct substance | No product identity or receptor efficacy transport |

Exact typed source-locator, registry and unresolved-object owner: `DASHI.Biology.Wong2022EvidenceLedgerExact`, imported by `DASHI.Biology.Everything`. The isolated Golden core remains `Wong2022LysergicAcidFiniteCore`.

**Deferred historical companion:** SensibLaw PR #513 was separately drafted as a candidate-only runtime adapter. The current DASHI-only work does not depend on or advance it. W22-06 is now a native scientific/metabolic bridge obligation.

**Exact remaining source/execution cut after this continuation:**

- W22-01: publisher source-data XLSX and Supplementary Information PDF authenticated by cryptographic digest and revision; no bytes were received in this connector session. The DOI/version-of-record is pinned, the binary hashes remain absent. Article license does not replace byte provenance.
- W22-02: verify detailed chemical identity/stereochemistry/charge and original analytical sample against appropriately revised PubChem/ChEBI records. A displayed PubChem cross-reference is not an independently approved same-object weld.
- W22-03: source-data endpoint row IDs, replicate-specific values and uncertainty estimates. The caption's replicate count must not be substituted for per-run data.
- W22-04: independent raw-data and standard-comparison review, with reviewer and instrument/analysis provenance. The paper's description is evidence but not a second experiment.
- W22-05: physical same-organism, compartment, time, exchange/kinetic units, absolute flux measurements and justified transport to `OpenMetabolicNetwork`/`Chemistry.TransitionKernel`. Neither chemical names nor source-reported titres pay these conditions.
- W22-06: check the native scientific-evidence and conditional stoichiometric theorem-owner bridge in DASHI; no external ontology runtime.
- W22-07: run focused Golden core, source adapter, evidence ledger, scientific-metabolic bridge and Biology root Agda checks, plus DASHI-only Python regressions. No kernel or pytest acceptance is claimed by GitHub readback.

Attribution: paper discoveries and measurements belong to Wong and colleagues. Molecular registry assertions belong to PubChem/ChEBI curators. Existing formal/ontology machinery retains its original DASHI, SensibLaw, SLR and ITIR owners. The new finite guards, candidate projection and documentation are DASHI/SensibLaw integrations and make no new wet-lab or biological-discovery claim.

## 2026-11-03 DASHI-only scientific/metabolic continuation

The evidence and chemistry bridge is now `DASHI.Biology.Wong2022ScientificMetabolicBridgeExact`. It imports the preexisting `ScientificMechanismEvidenceBidiExact` scientific status vocabulary and the `MetabolicStoichiometricConservation` theorem owner. Article endpoints are experimental reports, while the paper's larger-scale discussion is a source interpretation rather than a measured industrial result.

The new Golden finite-core review-tier and identity-carrier gates prevent paper-only evidence from inhabiting an independent-validation receipt, and prevent a registry-only identity tag from being treated as an experimental specimen or receptor-ligand identity. These are finite syntactic type distinctions. They are not chemical identity or replication proofs.

`scripts/check_wong2022_scientific_evidence.py` is a fail-closed static source-integrity checker with an explicit optional Agda execution flag. `tests/test_wong2022_scientific_evidence.py` exercises positive and negative cases. Neither file is a substitute for a real Agda acceptance receipt.

`W22-01` now has local binary-fingerprint *infrastructure*, not authenticated publisher bytes: `scripts/audit_wong2022_source_bytes.py` hashes an explicitly supplied XLSX or supplementary PDF and records container checks, optional caller-provided expected-hash agreement, and separate `false` flags for publisher identity, figure/sample identity, raw-data reanalysis and independent experimental verification. `tests/test_wong2022_source_bytes.py` exercises valid container stubs and rejected mismatched hashes. This creates no source-data values and does not close W22-01. Run `python3 -m pytest tests/test_wong2022_scientific_evidence.py tests/test_wong2022_source_bytes.py -q`; then `python3 scripts/check_wong2022_scientific_evidence.py --agda` on the exact branch when Agda is installed.

Active research residuals: verified source-data and supplement hashes; exact replicate values and uncertainty; external analytical adjudication; stereochemical and experimental sample same-object evidence; justified same-organism/compartment/time rate and transport data; exact-head Agda/Python execution. The separate runtime connector is excluded from this cut.

**W22-02 source discrepancy newly indexed:** PubChem CID 6717 displays InChIKey `ZAGRKAFMISFKIO-QMTHXVAHSA-N`, whereas IUPHAR/BPS ligand 139 displays `ZAGRKAFMISFKIO-IAPIXIRKSA-N` while linking to PubChem CID 6717 / ChEBI:6604. `Wong2022EvidenceLedgerExact.registryDescriptorReview` preserves the independently attributable strings and leaves both stereochemical normalization and original assay-sample identity false/unpaid. This does **not** conclude that these are chemically distinct compounds. Compare source revisions, normalized representation and stereochemistry before equality; do not use the misleading shortcut `same CID => verified sample identity`.


## Patent prior-art extension: Robinson / Panaccione (2014–2015)

**New independently attributable sources:**

- **2014 research:** Sarah L. Robinson and Daniel G. Panaccione, *Heterologous expression of lysergic acid and novel ergot alkaloids in Aspergillus fumigatus*, Applied and Environmental Microbiology **80**(20):6465–6472, DOI [10.1128/AEM.02137-14](https://doi.org/10.1128/AEM.02137-14), PMID 25107976. Scientific authorship and original observations remain with Robinson and Panaccione. The article's acknowledgment explicitly associates the work with US provisional patent application **62/012,658**.
- **2015 patent:** Inventors Daniel G. Panaccione and Sarah L. Robinson, original assignee **West Virginia University**, *Production of lysergic acid by genetic modification of a fungus*, [WO2015195535A2](https://patents.google.com/patent/WO2015195535A2/en), family PCT/US2015/035784. Google Patents displays claimed priority **2014-06-16**, filing **2015-06-15**, WO A2 publication **2015-12-23**, and international publication/family status **Ceased**, with an explicit legal-status disclaimer.
- **2022 yeast study:** Wong et al. as already cited above, DOI 10.1038/s41467-022-28386-6, published **2022-02-07**.

**Chronology matters:** the patent's *claimed priority* predates the 2014 article's online publication (**2014-09-19**), while the 2014 research publication predates the WO patent's **2015-12-23** publication. Do not collapse priority, filing, disclosure, research conduct, journal acceptance, published evidence or legal enforceability into one date.

| Comparison coordinate | Robinson & Panaccione, 2014 | WO2015195535A2, 2015 | Wong et al., 2022 |
|---|---|---|---|
| Source role | Original scientific research article | Published patent disclosure and claims | Original scientific research article |
| Host reported/claimed | Filamentous fungal study | Filamentous fungal invention context | Engineered yeast |
| Scientific evidence ceiling | Source-authored experimental observations | Patent disclosure; patent claims are **not** independent experimental reproduction | Source-authored analytic and outcome observations |
| Species/compound relationship | Ergot alkaloids and lysergic-acid-related chemistry | Related patent technical field | D-lysergic-acid pathway reconstitution |
| Same-host / same-experiment witness | **Not paid across sources** | **Not paid across sources** | **Not paid across sources** |
| Quantitative cross-study flux equivalence | Not derived | Not derived | Not derived |
| Novelty / IP clearance | Not assessed | Jurisdiction-specific family/claim status **not reviewed** | Not assessed |

**Prior-art implication:** the 2022 article is not the first authored observation of heterologous lysergic-acid production *in any fungal system*: the 2014 original paper establishes relevant earlier scientific work. This does **not** contradict the later yeast-specific reconstitution claim. Host-level novelty and pathway completeness require claim-by-claim, organism-specific evidence. A patent citation also does not automatically make every dependent claim experimentally verified.

**New DASHI modules:**

- `DASHI.Biology.LysergicPriorArtFiniteCore`: isolated `{-# OPTIONS --safe #-}` source, host, claim-type and legal-conclusion constructor barriers. A patent claim cannot inhabit the author's observation type, nor can a database status label inhabit a territory-specific legal opinion or freedom-to-operate witness. These are **syntactic** no-promotion rules only.
- `DASHI.Biology.LysergicPriorArtAttributedCrosswalkExact`: reuses `AttributedSourceCore`, `ScientificMechanismEvidenceBidiExact`, the existing `Wong2022LysergicAcidEvidenceExact` source and `Wong2022ScientificMetabolicBridgeExact` observation owner. Keeps original academic authors, inventors, assignee, identifier and distinct date coordinates. Imports no native external ontology or SensibLaw connector.
- Both modules are imported by `DASHI.Biology.Everything`. The Python-focused `check_wong2022_scientific_evidence.py` includes static source contracts for both and optional Agda checks. `test_wong2022_scientific_evidence.py` includes patent/2014-author attribution, legal firewall and claim-versus-evidence regression cases.

**Remaining exact max-cut for this prior-art link:**

1. **PA15-01 — Exact patent source revision:** authenticate the filed PCT publication/claim-set revision and official WIPO/PCT/US national records, not only an indexed Google Patents rendering.
2. **PA15-02 — Claim chart:** source-write a **bounded claim-number reference check** in `LysergicPatentClaimGraphExact.agda`: the Google Patents HTML renders 35 numbered claims and claim 28 as referring to 26, 27 and 28. The Golden proof `htmlClaim28SelfReference` establishes only that `28` occurs in the captured list; the HTML-derived self-reference is **not** a legal-defect conclusion. Remaining: authenticate original filed claim text, determine if transcription or original-document discrepancy, compare official amendment lineage and develop reviewed claim-level scope comparison against the 2014/2022 papers. No operational protocol.
3. **PA15-03 — Observed versus asserted:** identify paper-supported experiments, provisional hypotheses and patent claim language as separate source observations. Do not use a patent assertion as a second independent replication.
4. **PA15-04 — Context-sensitive comparison:** distinguish the 2014/patent filamentous fungal system from the 2022 yeast host; require exact product, analytical, organism, context and scale witnesses before same-object quantitative comparison.
5. **PA15-05 — Legal-status boundary:** independently verify any relevant national-family legal status in official registers if needed. The Google Patents `Ceased` label does not establish universal expiration, validity, noninfringement or freedom to operate.
6. **PA15-06 — Exact-head acceptance:** execute both Agda modules and their imported owner graph, and run the updated Python negative tests. Source-written/imported does not mean Agda-kernel accepted.

**Safety and attribution:** The original research belongs to Robinson and Panaccione (2014) and Wong et al. (2022); the patent invention is attributed to Panaccione and Robinson, originally assigned to West Virginia University. This integration does not reproduce sequences, construct designs, step-by-step production methods, compound synthesis or experimental optimisation. Patent claims and chemical precursor nomenclature are not clinical, manufacturing or legal permissions.


### PA15-02 source-indexed self-reference receipt

The third Golden module `DASHI.Biology.LysergicPatentClaimGraphExact` uses only Agda builtin equality, natural numbers, lists, strings and booleans. It records `htmlObservedClaimCount = 35` and `htmlClaim28Dependencies = 26 ∷ 27 ∷ 28 ∷ []` from the *public HTML rendering*. Its witness `htmlClaim28SelfReference = there (there here)` is a fully explicit finite membership proof, not a legal conclusion.

This is a potentially important source-text anomaly: Google Patents presents claim 28 as depending on itself. It might arise in the filed claim, an amendment, a typographical mistake, or the HTML transcription. `originalClaimFileCompared = false` and `legalDefectConcluded = false` stay recorded. Do not infer invalidity, design-around, or any production method from the anomaly.

The exact-head checker now covers three isolated/new Golden modules (Wong finite core, prior-art finite core, patent claim graph) and all corresponding non-Golden attributed adapters. The negative regressions detect unintended removal of the self-reference or assertion of a legal conclusion. Agda execution and exact official claim-file authentication remain open.


## Fourth source: Wong-associated 2023 patent family (2021 priority)

An additional patent source links the 2014–2015 Robinson/Panaccione family to the later Wong yeast paper:

- **International patent:** [WO2023096577A2 — Production of D-lysergic acid](https://patents.google.com/patent/WO2023096577A2/en). Filed as **PCT/SG2022/050840** on **2022-11-18**; claims **2021-11-26** priority; WO A2 publication **2023-06-01**. Google Patents lists the original applicants as **National University of Singapore** and **Imperial College Innovations Ltd**. The associated patent record cites the earlier West Virginia family (EP3155093A4).
- **Six listed inventors:** Wei Jie Garrett Wong, Li Rong Lim, Maybelle Darlene Kho Go, Wen Shan Yew, Paul S. Freemont and David John Bell. The 2022 Nature Communications research article has **seven authors**, including Yong Quan Tan, who is **not listed as an inventor** on WO2023096577A2. **Do not equate patent inventorship and academic authorship.**
- **Date ordering:** the 2023 patent's claimed priority (**2021-11-26**) predates the public 2022 scientific article (**2022-02-07**), though its international A2 publication (**2023-06-01**) postdates the article. Priority dates and public disclosures are different chronology coordinates.
- **Status ceiling:** Google Patents labels this WO application **Ceased** and individually lists several national-family applications (including US, EP, AU, CA, CN and JP) as **Pending**. These are indexed database observations, not an official up-to-date jurisdictional legal opinion; a WO label cannot discharge national family status or freedom to operate.

**Formal owner:** `DASHI.Biology.LysergicPriorArtAttributedCrosswalkExact` now retains `wongAssociatedPatent2023`, a four-source attributed atlas, `yeastPatentFamilyLineageReceipt`, `laterPatentWOStatusAsDisplayed` and explicit non-promotion. The isolated `LysergicPriorArtFiniteCore` also distinguishes `yeastPatentPublication2023` from `yeastArticle2022` and proves that the source-only patent claim type cannot be transported to the research-article claim type.

**Resulting source graph (four distinct evidence objects):**

`Robinson–Panaccione 2014 article` ↔ `WO2015195535A2 (2015 WO publication; 2014 priority)` → *cited prior-art patent family* → `WO2023096577A2 (2023 WO publication; 2021 priority)` ↔ `Wong et al. 2022 journal article`.

These arrows encode **source acknowledgments, inventor overlap and bibliographic/patent-family citation**, not a validated scientific derivation or a legal finding of patent priority, infringement, novelty or inventor entitlement.

**New source-specific remaining gates:**

- **PA23-01:** official original 2021 priority and 2022 filed 2023 published patent text; verify exact source identities and revisions.
- **PA23-02:** separate six patent inventors from seven article authors and verify any assignment/license facts independently if legally needed.
- **PA23-03:** perform a genuinely reviewed claim comparison at host/system/chemical-evidence level; patent claims do not replace separate science.
- **PA23-04:** independently verify national-family legal status from the official registers, instead of assigning blanket status from WO metadata.
- **PA23-05:** run the expanded exact-head Golden + attributed Agda checker and the DASHI-only Python negative tests. No SensibLaw integration is required.
