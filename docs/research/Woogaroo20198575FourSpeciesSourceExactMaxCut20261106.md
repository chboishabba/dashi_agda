# Woogaroo EPBC 2019/8575 — four-species original OAG source reconstruction

**6 November 2026 | Adversarial source ledger / original #1276 max-cut.**
This dated source-work extends, and does not displace, the original Woogaroo offset adequacy, landscape, QUT/QCC, BIDI logical-adversary and SLR #59 provenance. The 2019/8575 Springfield Residential Development is NOT Scenic 2020/8651. No forms, FOI, regulator reports, litigation, title mutations or legal findings were created.

## Original evidentiary owners

- 30 January 2026 Cherish/Saunders Havill PD v5 Part A.i **Tables A59 (overall), A62–A65 (Esk), A69–A72 (Avonvale), A76–A79 (Mount Walker West)**. The original detailed OAMP owners are **BAAM (Esk A14), One Environment (Avonvale A15), Saunders Havill (MWW A16)**.
- **2012 Commonwealth Offsets assessment guide**, original [how-to and normative methodology](https://www.dcceew.gov.au/sites/default/files/documents/offsets-how-use.pdf) Sections 2 A,C,G,H and Part A/B. Its actual NPV factor is **\((1+p)^{-20}\)**, not \((1-p)^{20}\). We verified this from published **Critically Endangered (6.8%)** feature OAG calculations, where the wrong formula makes material 9–10% changes.
- The original published outputs and literally printed input columns MUST be kept side-by-side: an internal PDF inconsistency is not automatically a corrected agency spreadsheet.

## Four-species arithmetic scope and exact output

**Four species × (Esk 4 + Avonvale 6 + MWW 4) = 56 species-AU rows** overall. The separate quality-gain branch uses **14 koala rows**, while this owner tests the **42 remaining rows** (14 each GHFF, Swift Parrot, Regent Honeyeater). Every numeric row is from the published source tables with explicit site, species, printed future-without and future-with input and reported percent. Independent exact Fraction code recomputes inverse-compounded percentage contributions:
- **Area/quality:** \(100\,A\, (Q_\mathrm{with}-Q_\mathrm{without})/10\times c /(89.6)\times (1+0.002)^{-20}\).
- **Preferred foraging features:** \(100\,(F_\mathrm{with}-F_\mathrm{without})\,c/N_\mathrm{impact}\times(1+0.068)^{-20}\), with impact features **9,983** Swift Parrot and **9,868** Regent Honeyeater.
- Published confidence \(c\) is typically 75% for bird planting gains and 75%/85% for area/quality; these are *proponent forecasts*, not observational probabilities. The source assumes 80% seedling survival before entering projected bird feature totals, not an 80%-success outcome observed on site.

Code:
- New golden [all-species source reconciliation](../../DASHI/Law/SensibLawWoogarooAllSpeciesOAGSourceReconciliation20261106Exact.agda).
- Independent executable [42-row regression](../../scripts/check_woogaroo_all_species_oag_reconciliation.py).
- [14-row exact koala and 2019/2022 status sensitivity](Woogaroo20198575OAGReconstructionAndStatusMaxCut20261106.md).
- [four-species printed-credit threshold owner](../../DASHI/Law/SensibLawWoogarooOffsetCreditRobustnessCut20261106Exact.agda).

The independent 42-row Fraction audit verified **38/42** printed row outputs within an absolute tolerance of 0.011 percentage points; **four AU outputs** disagree with the literal printed input values in a way that cannot be accounted for by that display rounding. These are *candidate source/worksheet identity conflicts*, not proof of the underlying author's intent.

## Four independent AU/worksheet disparities to reconcile

| Source row | Literal printed OAG quality/features | Computed output with correct factor | Published output | Main question |
|---|---|---:|---:|---|
| **Esk GHFF AU2**, A63 | 44.8 ha; baseline 4, future 8; confidence 75% | **14.4124%** | **10.81%** | Published output instead corresponds to a **3-point gain**, i.e., baseline 5, unlike printed baseline 4 |
| **Avonvale GHFF AU2**, A70 | 15.2 ha; baseline 3, future 7; confidence 75% | **4.8899%** | **6.11%** | Published output instead corresponds to a **5-point gain**, i.e., baseline 2, unlike printed baseline 3 |
| **MWW Swift Parrot AU3**, A78 | future without 30, future with 2708 | **5.3974%** | **5.04%** | Published output corresponds to future without approximately **207**, matching the original *start* value |
| **MWW Swift Parrot AU4**, A78 | future without 109, future with 117 | **0.0161%** | **0.20%** | Published output corresponds to future without approximately **20**, matching the original *start* value |

For MWW, a PDF/column extraction or transcription problem may explain the values; the original workbook and visually inspected PDF table are needed to decide. Do not silently replace input values to force the output, and do not cite an apparent inconsistency as intentional wrongdoing.

## Four additional hard source-total conflicts

1. **MWW Regent Honeyeater Table A79/A16 Table 19:** Future-with total printed **45,833**, but four AU future-with rows are **0 + 16,720 + 1,667 + 60 = 18,447**. The printed 45,833 coincides exactly with the nearby **Swift Parrot** future-with total (16,256+26,752+2,708+117).
2. **MWW Swift Parrot Table A78/A16 Table 17:** The *literal* future-without rows total **139** (0+0+30+109), but printed future-without total is **227**, matching the original start-value total (0+0+207+20). The **literal column** and printed aggregate cannot both be right.
3. **Esk bird feature Tables A64 and A65:** The printed per-AU areas (150.01,47.72,75.9,9.4 ha) total **283.03 ha**, not the table's printed **280.03 ha**. Another Esk site summary reports 280.2 ha. Without the source geometry and workbook, these cannot be forcibly equated.
4. **Esk Regent Honeyeater:** Part A.i Table A59 says **54.95%**; BAAM Esk A14 Table 7.3 says **54.96%**. Could be an ordinary rounding/revision difference; preserve both.

**These are stronger than generic finite adversarial countermodels because the contradictions are directly checkable in the original authors' own numeric rows.** They do not independently establish an excessive offset credit. Some discrepancies are conservative relative to the printed percent, others optimistic; assess actual downstream direction by formula and provenance.

## Most decision-relevant scenario cuts

### Koala: protected status and 20-year discount

The original proponent sheets use **Vulnerable / 0.2% annual extinction** based on the 2019 referral, whereas Commonwealth confirms the Queensland koala became **Endangered on 12 February 2022**. The 2012 OAG table assigns **1.2%** to Endangered. Under the SAME 14 quality-gain row inputs and approved-gain assumptions:
- 0.2% and inverse compounding: **108.345132619592...%**, reproducing 108.35%.
- Conditional 1.2%: **88.828757222414...%**, below the ordinary **90% direct-offset** threshold.
- Original 0.2% but MWW AU2 future quality 7→6: **99.924484785719...%**. Below 100% direct but above 90%.

This is not a court conclusion that old referral status was impermissible, that a different annual probability should have been entered, or that the delegate adopted a bad input. Exact **saved/transitional law and section 95C consideration** are still OPEN.

### Regent Honeyeater: dependence on predicted tree survival

The source uses 80% planted-feature survival in the future with-offset feature counts, with no directly credited risk-of-loss difference. In a **strictly conditional linear planting-gain scale** where *all species-specific credited improvements* scale in proportion to planting survival:
- At 80% as assumed, published three-site total = **104.42%**.
- At 75% survival, proportional scenario = **97.89375%**, below 100%.
- At 70% survival, proportional scenario = **91.3675%**, above 90% but not full direct coverage.
- Break-even survival for **100%** = \(80\times100/104.42≈76.61\%\); for **90%** = \(80\times90/104.42≈68.95\%\).

These are **conditioned sensitivity assumptions**, not a measured survival failure, ecological confidence interval, completed exact updated-OAG run, or proof that all credited gains are exclusively planted. They prioritize independent propagule establishment, juvenile-to-reproductive survival and seasonal nectar monitoring.

## Remaining exact physical/legal maximum cut

| Gate | Reproduced this round | Unpaid evidence/review |
|---|---|---|
| Numerical OAG | **56 source AU rows** across species; 14-row koala total and status perturbation; 42 other-row audit; four AU row mismatches and four total conflicts | Exact *approved* 15 Oct 2026 spreadsheets and all original unrounded cells/underlying formula (reconcile source discrepancies) |
| Robustness | Direct source-total margins, exact branch-specific koala discount, conditional future AU2 and bird planting-survival thresholds | Defensible empirical parameter intervals and joint/scenario correlation structure, not arbitrary hypothetical shocks |
| Ecological equivalence | Existing habitat/site OAG/SAT source leads, QUT/QCC and original landscape/koala genetics owner reuse | Independent impact-vs-offset habitat function, species occurrence/detection, local population corridor/seasonal maturation and counterfactual site ecology |
| Standing/merits | Original signed Part 9 and pre-existing seven-ground adversary, 2012 OAG and 2022 listing source | Correct saved/transitional EPBC/OAG listing-status applicability, s95C, s95B original packet, actual comments considered, standing clocks; counsel/court interpretation |
| Conditions | Legally binding 16 Oct 2026 Annexure A pre-commencement declarations and monitoring | Actual registered section 19F title/declaration copies, 2019/8575-specific works, agency notifications and any compliance receipts |
| Verification | GitHub readback and independent exact rational finite tests | **Agda --safe and parallel_checker** real acceptance at exact PR head; SLR runtime admission still requires canonical source-revisions and reviewer |

**Non-promotion:** No assertion about a Federal Court filing, actual breach, agency misconduct, cash transfer, the success of any planting, or guaranteed equivalent habitat is produced. Original authorship and original project identity are fixed throughout.

## Professional/ecological primacy correction, 6 November

The original 56-row proponent worksheet reconciliation is necessary arithmetic, but **insufficient even if every cell were correct**. The controlling original critical feedback is QUT School of Law's 12 March 2026 challenge to mature canopy, thermally buffered gullies, movement networks and cumulative effects, alongside QCC's 12 March 2026 challenge to the Woogaroo Creek–Opossum Creek corridor and incomplete surveys. New primary RSPCA Queensland 2025 original articles substantiate named koala care/return in the wider Woogaroo landscape; original QCC-commissioned *Holding the Line* Table 8 supports Ipswich LGA 21% remnant vegetation on 2021 mapping. All original authors and exact source limits are maintained in the [professional/community adversarial audit](Woogaroo20198575IndependentProfessionalCommunityAdversarialCut20261106.md).

**Therefore:** a numerical 108.35% OAG score does NOT certify local corridor continuity, mature canopy, hollow structure, thermal/evaporative refugia, breeding viability or same-functional replacement of Woogaroo wildlife by remote future plantings. Those are independent **ecological and legal consumers** with original observation/95B/95C/approved-OAMP gates. The 2022 Endangered-vs-2019 Vulnerable alternative remains CONDITIONAL until saved statutory requirements and actual decision reliance are established.
