# EPBC 2019/8575 — exact Mount Walker West gain threshold (7 November 2026)

**Original source owner:** proponent Cherish/Saunders Havill January 30 2026 Springfield PD v5, Part A.i Tables A62 (BAAM Esk), A69 (One Environment Avonvale), A76 (Saunders Havill MWW); original QUT Taylor/Maguire/Lewis, QCC Gough and first-party RSPCA independent objections in previous PR #1276 owners. The paper's claims are not independently verified habitat outcomes or automatically the operative October approved worksheet.

## Exact question and transparent assumptions

With **all other reported koala AU quality values, site areas and confidence levels fixed**, at the original proponent Vulnerable discount p=0.2%, time to benefit 20 years, impact quantum 89.6 adjusted hectares, no positive risk-of-loss benefit, ask: *what common OAG habitat-quality improvement in Mount Walker West AU1 and AU2 would produce 90% or 100% direct offset compensation?*

\[
C(g) = \frac{543850 + 116625g}{8960}\left(\frac{1000}{1002}\right)^{20}.
\]

The *other* original site/AU coefficient is 543,850. The two MWW credit-bearing units have area/75%-confidence coefficient \((508+1047)\cdot75=116625\) per quality improvement point. These are source OAG integer inputs, not populations or actual probabilities. More generally if AU1/AU2 gain differ, use \(508\cdot75g_1+1047\cdot75g_2\).

| Common MWW AU1/AU2 gain | Calculated koala compensation | Threshold |
|---:|---:|---|
| 1 | 70.82620029% | Below 90% |
| 2 | 83.33251107% | Below 90% |
| 3 | 95.83882184% | Above 90%, below 100% |
| 4 (the published claim) | 108.34513262% | Above 100% |

**Exact rational break-even:**
- \(g_{90} = [90\cdot 8960\cdot1002^{20}/1000^{20}-543850]/116625 \approx 2.533129957404\).
- \(g_{100} = [100\cdot 8960\cdot1002^{20}/1000^{20}-543850]/116625 \approx 3.332726271594\).

Hence the submitted four-point gain has to survive serious science-based scrutiny. A supported equal gain of three would still achieve the *ordinary* 90%-direct benchmark but not full 100% compensation; a gain of two does not. **90% direct is a general policy threshold, not itself proof of lawfulness or legal invalidity**; a valid residual other measure and exceptions must be checked. These are conditions on *calculated* credit using the proponent's own sources, **not estimates of real forest recovery**.

## Exact proof implementation

New golden [SensibLawWoogarooMWWGainThreshold20261107Exact.agda](../../DASHI/Law/SensibLawWoogarooMWWGainThreshold20261107Exact.agda) proves (via normalized Nat equalities) the exact 90/100 relations for g=2/3/4. [Exact rational checker](../../scripts/check_woogaroo_mww_gain_threshold.py) computes non-rounded break-even points and tests g=2,3,4. Independent local Python verification **was actually executed** in this conversation and numerically checked the four giant integer witnesses: local exact-rational JSON receipt `mww_gain_threshold_independent_20261107.json` generated in the conversation runtime (not an in-repository certified artifact). The Agda --safe kernel and in-repository parallel_checker **were NOT run**. Do not promote source-written Agda into kernel acceptance.

## What changed, and what's still actually missing

**Closed at conditional source arithmetic:** original 14-row coefficient, direct interpolation break-even thresholds, no automatic full-coverage claim at three points. Earlier separate score-precision test is consistent: MWW AU1 actual proponent-unrounded 3.40→6.86 and AU2 3.44→6.71 move conditional coverage to ~99.9918% instead of 108.3451%, while official OAG precision/rounding permissibility remains unknown.

**Unclosed primary input:** exact final **15 October 2026** OAMPs and approved XLSM sheets; real scientific methodology for six source rows claiming >1 quality point, particularly MWW AU1/2 four-point gains; original source tables' internal errors and version crosschecks; independent growth/soil/fire, koala food, maturity and climate data, and 75% confidence calibration. The current National EPA official OAG guidance expressly requires **strong scientific evidence for unusual >1-point quality change in most cases** (exceptions allowed); neither a management promise nor an annualized model is itself direct observed ecological success.

**Unclosed original legal/physical evidence:** real section 95B comment bundle and 95C recommendation; prior section 75 instrument (the EPBC s158A status firewall remains active); section 19F registered offsets and actual works/monitoring; standing/court/agency case records. Note the *Queensland State Offsets Register* [official](https://www.qld.gov.au/environment/management/environmental/offsets/registers) **explicitly excludes offsets required under Commonwealth legislation**: no entry there cannot prove absence of an EPBC 2019/8575 offset covenant. Use original Queensland VDEC/title instruments and the Commonwealth EPBC condition/offset registers separately.

All original QUT/QCC, RSPCA, BAAM, One Environment and Saunders Havill attribution preserved. Scenic EPBC 2020/8651 and other nearby actions remain distinct. No filing, FOI submission, site breach, financial transfer or judicial finding has been fabricated.


## 9 November version-identity supersession and live publication proof

The source-exact 90%-direct break-even \(g\approx2.5331\) and 100% break-even \(g\approx3.3327\) remain **correct conditional arithmetic for the 30 January 2026 PD v5 14-row assumptions**. The signed approval, however, expressly defines the operative PD as **Issue F, 3 July 2026**, and October OAMP revisions as **One Environment Avonvale Oes1:v1.2(e)**, **BAAM Esk 0102-059 v6**, and **Saunders Havill MWW 9612-E Issue D**, all dated 15 October 2026. Do NOT report \(g\) thresholds as final *approved-workbook* results before completing the [primary operative revision crosswalk](Woogaroo20198575OperativeInstrumentAcquisitionCut20261109.md). Conditions 48–49 make those specified plan versions public-access evidence with ordinary publication deadline **6 November 2026**, absent Minister written exception. Stockland lists downloads; actual matching file hashes/version checks not completed. Distinct C24/C25 VDEC and clearing prerequisites remain not paid. No site breach/judgment inferred.
