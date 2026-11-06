# EPBC 2019/8575 — source-exact OAG reconstruction and endangered-status max-cut

**6 November 2026.** Parent: original Woogaroo offset adequacy, adversarial BIDI, #1276 legal seven-ground and original QUT/QCC source work. All authorship retained. *No FOI request, agency representation, legal filing, compliance determination, or accused misconduct.*

## Precise source inventory

1. **Decision instrument:** signed 16 October 2026, Part 9, Cherish Enterprises, Mark Hall, Annexure A; user-supplied SHA-256 f9b591f230458939dbeafc8b6178c148dbbec3e68e5e75f66fd187e2a402b808. Distinct from the portal's **15 October** publication status.
2. **Original proponent input:** Springfield PD v5 **30 January 2026**, Part A.i **Tables A59/A62/A69/A76**, Esk BAAM A14 / Part A.ii Table 7.3, Avonvale One Environment A15, Mount Walker West Saunders Havill A16. These are consultant source-reported, not independent ecological outcomes. The **final 15 October 2026 OAMP versions** referred to by the operative approval still require direct source-to-source version joining.
3. **Method owner:** original **2012 Commonwealth** [How to use the Offsets assessment guide](https://www.dcceew.gov.au/sites/default/files/documents/offsets-how-use.pdf), §§2 A,C,G,H and Part A, and [National EPA current OAG information](https://www.nationalepa.gov.au/epbc/approvals/offsets/guidance/offsets-assessment-guide). Distinguish policy guidance from binding statute/approval.
4. **Koala official listing:** [DCCEEW: QLD/NSW/ACT koala Endangered from 12 February 2022](https://www.dcceew.gov.au/environment/biodiversity/threatened/species/koalas/listing-under-national-environmental-law). The PD expressly says **Vulnerable at the 2019 referral** and its annexed koala OAG sheets use **Vulnerable, 0.2% annual probability**. The 2012 OAG table says **Endangered 1.2%**. These are a genuine ORIGINAL-DOCUMENT INPUT DISCREPANCY across time, not yet an established legal misapplication: saved/transitional rule and decision-file reliance need counsel/source verification.

## 1. The published four-species compensation matrix (Part A.i Table A59)

All figures are percentages of overall modeled impact compensation, NOT guaranteed ecological success:

| Species | Esk | Avonvale | Mount Walker West | Printed sum | Margin above 100% |
|---|---:|---:|---:|---:|---:|
| Koala | 27.06 | 31.27 | 50.02 | **108.35** | **8.35** |
| Grey-headed Flying-fox | 63.44 | 60.59 | 66.89 | **190.92** | **90.92** |
| Swift Parrot | 54.58 | 53.49 | 91.92 | **199.99** | **99.99** |
| Regent Honeyeater | 54.95 | 12.07 | 37.40 | **104.42** | **4.42** |

**Additional source conflict:** Esk's original BAAM A14 Table 7.3 and narrative report **54.96%** Regent Honeyeater (vs main Part A.i Table A59 **54.95%**). 0.01 percentage point disagreement; require original worksheet/revision reconciliation. Do not mix a score from another project or claim a substantive failure from rounding alone.

The separate [four-species exact finite credit cut](../../DASHI/Law/SensibLawWoogarooOffsetCreditRobustnessCut20261106Exact.agda) checks all 12 values, margins, and conditional per-site credit loss thresholds. It does NOT equate haircuts of already-computed outputs with input modifications of actual OAG.

## 2. Reconstruct the ORIGINAL 14 koala rows, not just hypothetical reported-credit haircuts

The original OAG quality-only branch (using the source-reproducing inverse-compounding discount) (with proponent-reported **risk of loss 0% both without and with offset**) has this source-reconstructible form, measured in percentage points of total assessed impact:

\[
C_i(p)=100\frac{A_i}{89.6}\frac{Q_{i,\mathrm{with}}-Q_{i,\mathrm{without}}}{10}
\frac{c_i}{100}(1+p)^{-20}.
\]

- \(A_i\): AU area in hectares. Impact quantum **89.60 adjusted ha**, from impact **128 ha × quality 7/10**.
- \(Q_{i,\mathrm{without}},Q_{i,\mathrm{with}}\): the INTEGER ROUNDED start/future-without and future-with OAG quality inputs in Tables A62/A69/A76; NOT the higher-precision ecological forecasts.
- \(c_i\): original estimated future-quality confidence, **75%** for most nonremnant AUs and **85%** where separately assigned by the worksheet.
- \(p\): OAG annual extinction probability; reported **0.002** for a vulnerable koala, alternative endangered **0.012**.
- 20-year time to benefit. This is an explicit source input, not 20 years of observed habitat growth.

Rows:
| Offset | AU areas ha | Rounded without→with quality | Quality confidence | Published AU credit % |
|---|---|---|---|---|
| Esk | 150.1, 44.8, 75.9, 9.4 | 6→7, 5→7, 6→7, 6→7 | 75,75,85,85% | 12.07,7.21,6.92,0.86 |
| Avonvale | 49.3,15.2,2,86.8,11,3.7 | 4→7,3→7,6→7,5→7,7→7,6→7 | 75,75,85,**75**,85,85% | 11.90,4.89,0.18,13.96,0,0.34 |
| MWW | 50.8,104.7,62,8.1 | 3→7,3→7,7→7,7→7 | 75,75,85,85% | 16.34,33.68,0,0 |

**Avonvale AU4:** The generic proponent narrative describes 85% confidence for some remnant/regrowth units, but the **published 13.96% AU4 output reproduces using 75%**, not 85%. This requires worksheet-source inspection. The present model reconstructs the reported output; it does not certify that the 75% is the accepted original cell.

The **exact rational numerical sum** (before separately rounding AU rows) is **108.345132619592...%** at p=0.002, approximately the printed **108.35%** after the per-AU publication rounding. Every AU output matches to within about 0.011 percentage points. Source-reported AU percentages are rounded and not a substitute for source-exact cell contents.

The [new golden Agda owner](../../DASHI/Law/SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact.agda) computes the exact finite coefficient **1,010,350**, with area in tenths and confidence percent, and proves via exact natural-number equalities: (i) the vulnerable-source total exceeds 100%; (ii) the endangered-input total is strictly below 90%; (iii) one point less projected MWW AU2 future habitat quality gives a total strictly below 100% but above 90%. It explicitly imports the existing original credit/adversary owner; it is not a second ontology or legal pipeline.

Executable companion: [check_woogaroo_koala_oag_status_sensitivity.py](../../scripts/check_woogaroo_koala_oag_status_sensitivity.py). No fabricated kernel or official spreadsheet run.

## 3. Decisive conditional results, NOT findings of legal wrongness

| Test (all other values fixed) | Calculated total koala compensation | Status |
|---|---:|---|
| Reported OAG input **Vulnerable 0.2%** | **108.336465%** | Reconstructs the reported 108.35% |
| Same source rows with **Endangered 1.2%** | **88.828757%** | **Below 90%**, if that extinction parameter is legally applicable |
| Reported Vulnerable 0.2% with MWW AU2 projected **quality 6 instead of 7** | **99.924485%** | Below 100%; still above 90% |

The endangered correction is a common twenty-year inverse-discount multiplier **\((1.002/1.012)^{20}≈0.819868\)** over the quality-only rows. This is source-exact discount arithmetic, but NOT an independently validated future gain nor a decided transitional-status issue.

**The 2012 OAG distinguishes a normal minimum of 90% direct offsets from the balance of other compensatory measures**, and requires consistent habitat-quality assessment on impact and offset sides. **Do not equate “below 100% direct” with automatic approval invalidity**. The alternative 88.57% instead has potential relevance even to the ordinary 90% direct threshold; identify any applicable exceptions and the actual final accepted worksheet.

## 4. Additional ecological, legal and mathematical checks

- **Present vs future:** The 50.02% MWW koala compensation is entirely attributable to AU1+AU2 (155.5 ha of the Table A76 rounded area inputs), both rated 0/30 existing koala density. Their 3→7 gain, confidence 75% and 20-year lag are modelling assumptions, not real observations.
- **Source contradictions:** MWW A16 Table 45 AU4 components total 30/70, printed 40/70; prose has usage 15 versus table 5. A16 SAT ids differ between prose and table. A16 Table 2 127.02 ha vs main PD A26 128.00 ha. None proves intentional false reporting or affects 50.02% without tracking actual source input cells.
- **Koala site occurrence:** MWW SAT 3 scat-positive tree slots out of five 30-tree searches, Avonvale 17/150. These are not animal counts, occupancy probabilities or iid binomial trials.
- **Other species:** 3-site printed-source credit matrix and exact conditional credit haircuts are complete, but **physical OAG reconstruction of all GHFF/parrot/honeyeater inputs** remains a distinct real gate. Their site-specific source worksheets have different species/feature parameters and 6.8% annual extinction for critically endangered birds. No substitution of koala formula.
- **Legal causality:** A different model input does not demonstrate the Commonwealth actually used, considered or was required to use it. Obtain current approved final OAMPs, the section 95C recommendation, decision brief, relevant saved EPBC transition law and specific written consideration of 2022 koala listing/conservation advice.
- **Ecological effect and enforcement:** Underlying 2025 field observations and 20-year forecasts are consultant reports; actual external field validation, registered section 19F declarations and commencement records remain open.

## 5. Exact remaining Pareto max-cut

| Gate | Closed now | Still open |
|---|---|---|
| M0 — original four-species source matrix | 12 published amounts, sum/margins, BAAM 54.96 vs main 54.95 conflict | final **15 October 2026** approved plan/worksheet revision identity |
| M1 — koala OAG numerical branch | 14 printed row inputs, exact 0.2% discounted reproduction, 1.2% and AU2 perturbations | official macro workbook execution and unrounded input provenance |
| M2 — four-species OAG | conditional reported-credit rectangles, exact threshold; koala quality component | three other species' 2012 OAG native input/calculator reconstruction and approved status/version |
| M3 — proper 2026 listing/status | official 2022 Endangered listing vs 2019 Vulnerable OAG input; exact <90 conditional | legal saved/referral status, duty and actual delegate/95C acceptance (not a judgment yet) |
| M4 — ecological population/functional equivalence | old Woogaroo landscape and SAT source conflicts reused | independently calibrated AU mapping, detection/corridor, mature habitat, viability, future gain and climate risk |
| M5 — secure/implemented/monitored offsets | operative 16 Oct Annexure A requirement identified | legal VDECs, exact polygons and existing prior offsets, actual works/monitoring, site condition breach if any |
| M6 — review/standing and filing | original seven-ground source-gated model reused | section 95B/95C and advice considerations, OFT standing, filing/furnishing clocks and actual court records |
| V — proof trust | native Agda source with exact Nat witnesses and independently executed rational finite reference | exact-head **Agda --safe and parallel_checker kernel receipt OPEN** |

No filing, FOI, courtroom, agency decision or ecological transfer performed. QUT/QCC original submissions and existing DASHI/SLR credits unchanged. Scenic EPBC 2020/8651 and financial/asset adjacency explicitly outside the 2019/8575 action.


### 6 November later same-round correction: inverse-compounding and four-species crosscheck

The explicit MWW/Esk/Avonvale feature-based sheets show the **2012 OAG uses inverse compound discount \((1+p)^{-20}\)**. The earlier \((1-p)^{20}\) approximation is **superseded**. With correct discount the 14-row koala reconstruction is **108.345132619592...%**, the conditional Endangered case is **88.828757222414...%**, and MWW AU2 future quality 7→6 gives **99.924484785719...%**. The golden and Python sources were updated accordingly.

The original per-AU worksheets for the flying-fox, Swift Parrot and Regent Honeyeater expose further arithmetic/input disagreements requiring explicit row-level reconciliation, not fabricated values. The same-round full-species addendum will be recorded in the subsequent cross-species audit. This is still *source-authored numerical auditing* and not a result that decides applicable transitional law or independent ecology.
