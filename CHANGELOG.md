# Changelog

This changelog is append-only. Older mentions of `false` are historical wave
records unless the entry explicitly states it is describing the current live
monitor surface.

## 2026-07-19 — Wetsuit seam optimisation boundary

- Added `DASHI.Geometry.WetsuitSeamOptimisationBoundary`, a fail-closed typed
  carrier for body-zone design priors, material/panel budgets,
  manufacturability evidence, weighted seam cost, admissibility, relative
  optimality, validation gates, and split advice.
- Added `DASHI.Geometry.WetsuitSeamOptimisationRegression` with canonical
  underarm/inner-leg preference and shoulder/spine avoidance prior receipts,
  while keeping continuum optimality and manufacturing authority explicitly
  unpromoted.
- Added the compact aggregate `DASHI.Geometry.WetsuitSeamOptimisation`.
- The module formalises the optimisation and obligation surface only; it does
  not claim universal biomechanics, continuum-mechanics closure, or certified
  manufacture. `DASHI.Everything` was not run in this connector-backed pass.

## 2026-07-13 — P06 duplicate-free valid-walk enumeration

- Added and focused-checked `P06GeneratedWalkUniqueness.agda`.  Under the
  canonical neighbour adapter it proves extension-block `NoDuplicates`,
  recursive block disjointness, and
  `generatedWalkVertexListsNoDuplicates` without postulates or proof-heavy
  `WalkObject` equality.
- Added `GeneratedWalkVertexListSemantics`, packaging generated valid-walk
  lists, extensional completeness, duplicate-freedom, and the single
  `countWalks ≡ length` bridge.
- Added focused-checked additive `P06ConcreteEnumerationEndpoint.agda` and
  `P06SkeletonEnumerationSurface.agda`.  The former makes DFS membership an
  explicit field of a membership-indexed map; neither module touches the
  legacy total-index API.
- Added focused-checked `P06ConcreteSkeletonWitness.agda`, which proves all
  individual-candidate chooseN facts and packages the remaining skeleton list
  obligations (`complete`, vertex-list uniqueness, and count agreement)
  without pretending they are derivable from an arbitrary list.
- Added focused-checked `P06DFSValidWalkSurface.agda`.  It packages the
  minimal per-skeleton `WalkObject` plus equality to `dfsWalkRange`, derives
  generated-list membership and soundness, and adapts map witnesses to the
  membership-indexed endpoint.  It deliberately does not infer path validity
  from `DFSCover` coverage alone.
- `Everything.agda` was not run.  The remaining P06 mathematical blocker is
  now the genuine DFS-valid-walk membership witness; the legacy total-index
  record remains compatibility-only.

## 2026-07-13 — Corrected P06 walk status

- Corrected the P06 record: recursive walk completeness has landed through
  `walkObjectsCompleteByVertices`, and successor-membership inversion has
  landed through `walkObjectsSucMemberByVertices` and
  `walkObjectExtendMemberByVertices` in
  `DASHI/Physics/YangMills/GraphCombinatorics.agda`.

## 2026-11-08 — CCDCOE P3 G20/COP21 institutional cross-case original-source cut

- **Source authority and attribution:** original G20 Brisbane ¶19 (2014), Antalya ¶24 (2015), COP21 decision 1/CP.21 (2015), treaty Article 4.2 (operative from 2016), and Hamburg (2017) speakers are attributed to their actual original institutions. The 2017 US withdrawal position and other G20 leaders' continuing support remain DIFFERENT speakers and position scopes. Original C20 Turkey 2015 civil-society communiqué and B20 Turkey 2015 submission catalog remain their own organisations' documents, not leaders' adopted commitments.
- **DASHI proof attribution:** new `DASHI/Cognition/CCDCOEP3G20COP21AttributionExact.agda` instantiates EXISTING `DASHI.Core.IntersectionalNonFactorability` and `DASHI.Core.DiscriminatorSynthesisExact` proofs. External authors do not receive DASHI theorem attribution; DASHI gains no claim to their historical authorship/endorsement.
- **Original evidence:** `Docs/research/ccdcoe_p3_g20_cop21_attribution_manifest.json` retains nine original source identities, ten selected claims, exact author and legal speech act, separate source dates and original-source locators, null actual lobbying/doc-drafting transmission, no fabricated full-original-byte hashes or statistical effect measures.
- **Fail-closed checks:** `scripts/check_ccdcoe_p3_g20_cop21.py` validates original speaker/claim joins, Hamburg split, civil/business submissions versus adopted text, Paris adoption-versus-entry-into-force and dated withdrawal announcement, plus optional original bytes SHA256 / reviewed extracted passage receipts. Synthetic negative tests do not constitute original source review.
- **Golden governance:** imported into `DASHI/Cognition/Everything.agda` and `CCDCOEP3CausalTrialecticRegressionExact.agda`; wired into `scripts/check_ccdcoe_cognition_agda.sh` via the existing `parallel_checker`. This commit records source-written mathematical claims, **NOT** an exact-head Agda kernel acceptance receipt or reproduced causal influence.
- **Roadmap and source atlas:** `Docs/research/CCDCOEP3G20COP21PrimarySourceAttribution20261108.md`; `Docs/roadmaps/CCDCOEP3CausalTrialecticSourceMaxCut20261106.md`. Remaining gates I0–I5: original source bytes/review, full corpus and coder reliability, actor-to-draft transmission, country-level compliance/implementation, causal identification, independent replication and kernel acceptance.

## Independent measured follow-through: G20 Research Group, not G20 leader self-assessment

This case now has a **real independent selected-commitment evaluation** alongside the original adopted texts. Do NOT attribute the measurements to the communiqués, any member's press office, B20/C20, GCC/Harrison or ExxonMobil.

**2014 Brisbane original evaluation:** G20 Research Group, University of Toronto, and IORI HSE; original authors Krystel Montpetit, Theodora Mladenova, Mickael Deprez, Jonathan Tavone, Phil Gazaleh, Taylor Grott, Antonia Tsapralis, Andrei Sakharov, Andrey Shelepov and Mark Rakhmangulov; final report dated 12 November 2015, actions 16 November 2014–1 October 2015, **17 assessed commitments of the summit's 205**. On the research group's original scored scale (−1, 0, +1), published selected commitment topic scores include climate **+0.10 (55%)**, clean energy **+0.90 (95%)** and fossil-fuel subsidies **−0.45 (28%, rounded)**. https://www.g20.utoronto.ca/compliance/2014brisbane-final/index.html

**2015 Antalya original evaluation:** Sarah Scott, Alissa Wang and G20 Research Group, with Mark Rakhmangulov and the RANEPA Center for International Institutions Research; final report dated 3 September 2016, revised 10 December 2016; actions 16 November 2015–5 September 2016, **17 selected of 113 summit commitments**. Its selected fossil-fuel subsidies commitment was **−0.35 (33%, rounded)**. https://g20.utoronto.ca/compliance/2015antalya-final/index.html

The 2014→2015 comparison 28%→33% is **five percentage points between two original topic-specific report values**, not a controlled trend in fossil subsidies, physical energy use, aggregate emissions or all countries. Both selection frames and commitment specifications differ, and researchers explicitly state their findings only evaluate the **particular selected G20 commitments**. Score conversion is research-specific `P = 50(S + 1)`. The printed whole percentages may differ by half a percent from the displayed decimal score owing to rounding.

Source-new `DASHI/Cognition/CCDCOEP3G20ComplianceObservedExact.agda` owns ONLY DASHI transcription, typed source and scope guards, arithmetic and validation interfaces; **all original research measurement and methodology remains credited to its G20 Research Group/IORI/RANEPA authors**. Agda original generic mathematical donors remain unchanged. The formal module and regression use distinct `brisbaneFinal2014` and `antalyaFinal2015` report owners, 17/205 versus 17/113, measured time windows, four published score summaries, and explicit no-industry-causal or no-emissions-measurement boundaries.

`ccdcoe_p3_g20_cop21_attribution_manifest.json` now retains both independent studies with names, revised publication date, report URIs, selected denominator, topic score and original inferential limitations. `check_ccdcoe_p3_g20_cop21.py` asserts these original values and refuses to present an independent compliance evaluation as adopted-leader wording, authored stakeholder influence, treaty status or emissions effects.

**Higher-alpha next empirical acceptance:** original item-by-item member scores and supporting sources for the assessed commitments; harmonise country/commitment/time units before longitudinal inference; connect Paris national NDC files and emissions to their own original action/dates; use documented B20/C20/industry-draft version trails to test any influence. Do not expand generic Agda interfaces before a real recorded-data failure requires one.

## 8 November 2026 — original October G20 Energy Ministers and B20 Forum temporal disambiguation

**Supersedes the prior B20 index-only limit for one specific source:** the **original B20 Energy Forum Statement, dated 12 October 2015**, is publicly readable as a primary PDF: https://g20.utoronto.ca/b20/B20-Energy-Forum-Statement-121015-final1.pdf. The first PDF page has been visually inspected and its text checked. Original author statement: prepared by **B20 Energy Forum participants and G20-B20 interaction participants**, building on an interaction at the **2 October 2015** Energy Ministers' meeting, with **inputs** from the IEA, OECD, ICC and the 2015 B20 Infrastructure/Investment Taskforce. Those inputs are source credits, not individual co-authorship of particular recommendations or proof each organisation endorses every policy assertion. Its annex reports speakers including BP Turkey, Dow Chemical, Glencore/World Coal Association; **listed participation is not evidence a named speaker authored any particular recommendation**.

Selected original B20 recommendations: carbon pricing to support investment confidence; reform of inefficient energy subsidies; formal B20 representation in the G20 Energy Sustainability Working Group; clean technology/energy access. Each remains B20 participant proposed action, not a G20 leaders' legal act. Original PDF sections: proposals 1–5, PDF text lines 47–154.

The independently published **G20 Energy Ministers' Communiqué of 2 October 2015**, original-source reproduction https://www.g20.utoronto.ca/2015/151002-energy.html, has its own institutional author (energy ministers), **not the November leaders**. Paragraph 11 explicitly links efficiency/clean energy, UNFCCC and COP21 negotiations. These original ministry statements are temporally **earlier** than the October 12 B20 statement. There may have been interaction and earlier drafts at the October 2 meeting, but one cannot backdate *published October 12 words* into the earlier ministers' adopted communiqué without a source-specific original contemporaneous draft and author witness.

**Typed original chain, no causal shortcut:**

- 2 October 2015 — G20 Energy Ministers adopted their own communiqué (ministerial speech act).
- 12 October 2015 — B20 Energy Forum participants published recommendations arising from a separate interaction (business speech act).
- 16 November 2015 — G20 leaders adopted Antalya communiqué ¶24 (leaders' speech act).
- 12 December 2015 — UNFCCC COP21 Parties adopted the Paris Agreement (COP decision and separate treaty text).

`DASHI/Cognition/CCDCOEP3G20COP21AttributionExact.agda` now has **distinct original owners** for the ministers, B20 Forum participants, B20 catalog-only material, C20 civil society, leaders and COP Parties. It implements source-kind/speaker nonfactorability using existing DASHI mathematical donor modules (their original proof ownership unchanged), a dated October-to-Paris record, explicit participant/quote/endorsement limitations and separate non-inference to lobbying causality. The case manifest now contains 11 source identities and 15 selected original-content/index clauses, plus precise attendance and temporal-provenance guards. `scripts/check_ccdcoe_p3_g20_cop21.py` adds source-bounded review and negative regression against reverse-dating B20 influence on ministers. Golden regression and research source ledgers updated. Full original-PDF raw bytes/revision hashes and independent negotiation-draft records remain OPEN.

**New discriminatory experiment:** document-level B20→Antalya/COP21 influence requires (1) an actual B20 version before the relevant negotiating draft, (2) a named representative-to-negotiator documented contact, (3) draft-version or minute-level uptake, and (4) counterfactual discrimination from already-existing G20 ministerial/UNFCCC views. The comparison cannot be resolved from carbon-pricing vocabulary alone.
