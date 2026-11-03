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
