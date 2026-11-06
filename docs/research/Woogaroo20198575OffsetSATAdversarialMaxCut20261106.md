# EPBC 2019/8575 — offset SAT adversarial maximum cut (6 November 2026)

**Strict case boundary:** Cherish Enterprises, Springfield Residential Development **2019/8575**; not Scenic **2020/8651**, other Springfield approvals, Aroona Station, or unrelated political/financial adjacency. This is source-typed research, not independent ecology, legal advice, a filed proceeding, enforcement notice or judicial finding.

## Original ownership and prior-work reuse

This is an extension, not a new independent theory of the offsets. Reuse the existing:
- [EPBC Offset Adequacy Audit](../../Docs/SaveWoogarooForestEPBCOffsetAdequacyAudit.md)
- [Offset Landscape Counterfactual](../../Docs/SaveWoogarooForestOffsetLandscapeCounterfactual.md)
- [Landscape Risk and Maturity](../../Docs/SaveWoogarooForestOffsetLandscapeRiskAddendum.md)
- [Offset Candidate Identity](../../Docs/SaveWoogarooForestOffsetCandidateIdentityAudit.md)
- PR #1276 original seven-ground adversarial Agda and signed predicate fibres; PR #704 BIDI proof graph; PR #911 expert-production evidence integrity; original offset/attribution Agda owners.
- PR #1439 is separate source-nonpromotion/financial reasoning. SLR PR #59 is a distinct runtime consumer, not field-observation authority.

Attribution: **Saunders Havill** wrote the Mount Walker West survey/PD, **One Environment** the Avonvale plan, **BAAM** the Esk offset ecology, **QUT School of Law** and **Queensland Conservation Council** their respective original submissions, and **Commonwealth National EPA** the approval. The user-directed DASHI formalisation does not adopt those authorships or promote allegations to adjudicated facts.

## Exact source and version identity

1. User-acquired **signed approval**: 50-page Part 9 EPBC 2019/8575, signed **16 October 2026** by Mark Hall for Cherish Enterprises Pty Ltd; Annexure A conditions; approval to **16 October 2056**. SHA-256 **f9b591f230458939dbeafc8b6178c148dbbec3e68e5e75f66fd187e2a402b808**. The earlier **15 October** publication-status date is distinct.
2. January 2026 PD v5: **9612 Springfield Preliminary Documentation v5 EPBC 2019-8575 30012026 Part A.i** and **Part A.iii**, including **A15 One Environment** and **A16 Saunders Havill** 2025 field-survey reports.
3. The approval separately identifies **15 October 2026 versions of offset plans**. **DO NOT** equate them with the January PD appendices without a version/content comparison and agency acceptance records.
4. Section 95B(2) one-page notice reports **1,786 comments**; it is neither the full section 95B packet nor section 95C recommendation.
5. [Official Commonwealth project decision page](https://epbcpublicportal.environment.gov.au/all-notices/project-decision/?id=d951b5fa-9efb-ee11-9f89-00224892a860). SharePoint document API errors do not establish legal non-existence or an actual FOI filing.

## Finite, source-reported survey results

| Site, source | SAT scat-positive tree counts, each from 30 trees | Total positive tree slots /150 | Positive SATs | Classification |
|---|---|---:|---:|---|
| **Mount Walker West**, A16 Table 44, pp 101–102 | 0, 2, 0, 1, 0 | **3/150** | **2/5**; all low | proponent consultant report |
| **Avonvale**, A15 Table 33, pp 71–72 | 11, 5, 0, 0, 1 | **17/150** | **3/5**; one high | offset-provider report |
| **Esk**, A14 and main PD §6.3.3 | scats reported in treed AUs, low activity; exact equivalent table **not extracted** | OPEN | OPEN | proponent consultant report |

**TREE SLOTS ≠ KOALAS.** These five SATs at each site are not a randomly selected set of independent animals or hectares. Do not produce an ordinary binomial confidence interval or infer population size, viable breeding, corridor replacement or absence from a zero-scat result. Avonvale's report also says a koala was observed: attribute the observation to the source rather than either denying it or treating it as independently confirmed.

### Strong scoring/identity tests

**A16 Table 45:** the proponent reports the maximum **10/10 presence-on-or-adjacent-to-site score for all four assessment units** even though the five SATs identified scat-positive trees in only two. The 10/10 may be allowed by an on-or-adjacent **site-level** rubric; require the exact rubric and an AU-linked observation map before claiming mis-scoring. 10/10 presence is neither an AU population-density measurement nor proof of all-AU use.

**A16 source-internal table/prose conflicts:** A16 §6.1.3/Table 44 identifies **T1,T2,T3,T7,T8**, while later §6.2.1 prose names **T1,T6,T7,T8,T10**, matching A15 Table 33. A16 has a second **AU4 species-usage narrative versus Table 45** discrepancy (15/15 in the prose versus 5/15 in the table). Resolve against dated original raw SAT sheets, survey coordinates, AUs and approved version. Do not guess which version is correct or infer wrongdoing.

The same Mount Walker West source scores **0/6 for the ecological-corridor location coordinate** while acknowledging some koala use/dispersal. Those are different predicates; a site occurrence neither implies the site replaces Woogaroo’s urban corridor nor proves it cannot have conservation value.

## New exact formal implementation and its scope

**Golden Agda**: DASHI/Law/SensibLawWoogarooOffsetSATAdversarial20261106Exact.agda

- Native finite tally witnesses prove Mount Walker West **3** scat-bearing tree slots across **2** positive SATs, Avonvale **17** across **3** positive SATs. Inputs and source authors are explicit.
- Four reported **10/10** AU subcomponents sum to **40 raw points**. That is not weighted MHQA quality or a percent of legal offsets.
- **noUniversalAU1UseDecoder** constructs two hypothetical AU-use worlds with identical exposed survey evidence/scores but differing AU1 use, while at least one AU is used in both. The result is a rigorous **reduced-projection non-identifiability theorem**, not a conclusion that real AU1 is empty.
- **habitatGroundCountermodel** imports the existing seven-ground Woogaroo adversarial parent, not a second proof-search taxonomy.
- Python **scripts/check_woogaroo_offset_sat_adversarial.py** enumerates **16 binary latent AU assignments** (15 with any AU used) and **11^4 = 14,641** four-component integer-score vectors (raw totals **0–40**). These are **scenario spaces**, NOT statistical confidence intervals.
- Source-reported Mount Walker West contributions **50.02% Koala, 66.89% GHFF, 91.92% Swift Parrot, 37.40% Regent Honeyeater** are stored as input claims, **not recalculated** from SATs or independently verified.
- Avonvale consultant material reports no WildNet/ALA Swift Parrot or Regent Honeyeater records within 10 km, but missing database records ≠ absence/unsuitability.

## Material ecological comparator

The proponent's impact-site PD estimates **128 ha** critical habitat clearing, Koala MHQA **6.78**, GHFF FHA **7.47**. Mount Walker West has **225.6 ha** designated offset but envisages **155.4 ha** of recreation on historically cleared grazing land; the 2-ha building envelope is excluded. Esk's **280.2-ha offset** excludes proposed rural building envelopes. Avonvale's **168 ha** consists of variable grazing/regrowth land and a **reported agreement** with One Environment (contract terms/consideration not independently obtained). Future planted habitat is not immediate equivalent for the affected Woogaroo local koala population, even where it may improve a separate population or provide resources to highly mobile species.

## Exact remaining max-cut, no fabricated receipts

| Gate | Paid in this work | Unpaid decisive result |
|---|---|---|
| S0 — document identity | Signed **16 October** approval; Jan PD source and clear 95B(2) notice identity | Full section 95C, 95B packet; **final 15 October offset-plan versions** and approval/PD same-object version join |
| S1 — observation extraction | A15/A16 five-SAT counts and source provenance | **Esk A14 exact table**; original GPS/raw sheets, transect-to-AU mapping |
| S2 — score validity | uniform MWW 10/10 report; transect-ID and AU4 text/table discrepancies | Exact presence scoring rubric, weights, permissible site/adjacent rule, independently reconciled inputs |
| S3 — numerical sensitivity | 16 AU binary worlds; 14,641 raw subscore assignments | **Actual OAG/MHQA calculator** with weighted formulas, 20-year gain/confidence/risk parameters and numerical percent-change bounds |
| S4 — ecological effectiveness | existing/restore maturity and survey leads; explicit species differences | Same-function Woogaroo/offset baseline, genetics/connectivity, seasonal bird/flying-fox resources, independent non-iid detection model |
| S5 — registered offsets/conditions | Conditions 24–27, 48–49, 52–69 identified | Section 19F registered declarations, cadastral polygons, commencement, actual monitoring/annual records, verified breach if any |
| S6 — merits | prior seven-ground applicant/respondent logic reused | Original decision reasons and statutory transmission/consideration, standing, filing, court orders; **no actual filing/breach/judgment/payment shown** |
| V — verification | Python finite reference and Agda source contract executed in local model runtime | **Agda --safe kernel receipt NOT available** here; source-written is not theorem-kernel accepted |

### Reproduction

~~~sh
python3 scripts/check_woogaroo_offset_sat_adversarial.py \
  --agda-file DASHI/Law/SensibLawWoogarooOffsetSATAdversarial20261106Exact.agda
# Independent compiler receipt required at exact PR head:
agda --safe -i . -i /path/to/agda-stdlib DASHI/Law/SensibLawWoogarooOffsetSATAdversarial20261106Exact.agda
agda --safe -i . -i /path/to/agda-stdlib DASHI/Law/SensibLawWoogarooPreservationEverything.agda
~~~

**Non-promotion:** proponent source ≠ independent verification; survey lead ≠ four occupied AUs; source inconsistency ≠ fraud; site occurrence ≠ functional-equivalence finding; offsets ≠ actual ecological outcomes; approvals ≠ compliance; legal hypotheses ≠ filed cases/judgments; contractual mention ≠ financial transfer. No submissions, forms or enforcement reports were lodged.
