# Woogaroo EPBC 2019/8575 — exceptional habitat-quality gain evidence cut (6 Nov 2026)

This is **not** a new project, a new conclusion of illegality or an approval-condition breach. It extends original QUT Taylor/Maguire/Lewis, QCC Gough, other independent field and project-specific objections under existing DASHI PR #1276 and SLR #59, preserving their actual authorship.

## Authority and source identity

- Proponent's *Springfield Preliminary Documentation v5* (30 January 2026), Part A.i Tables **A62 (Esk), A69 (Avonvale), A76 (Mount Walker West)**, 14 koala quality-gain AU rows. Original consultant/offset owner: BAAM, One Environment, Saunders Havill respectively.
- [National EPA official Offsets assessment guide guidance](https://www.nationalepa.gov.au/epbc/approvals/offsets/guidance/offsets-assessment-guide), section **Quality score changes**: *in most cases*, future-with-minus-future-without habitat-quality change is normally limited to **1 point**, **unless strong scientific evidence shows a greater improvement is possible**. This is an **express exception**, not a hard ban or automatic legal invalidation of any 2–4-point claim.
- [Original Commonwealth 2012 How to use the Offsets assessment guide](https://www.dcceew.gov.au/sites/default/files/documents/offsets-how-use.pdf), section 2C–G, including §2G: confidence must reflect both likely ecological improvement AND the proponent's delivery track record, and very large quality improvements are generally harder to achieve and should attract lower confidence; section 3 step 15 specifies the inverse compounded discount \`1/(1+p)^t\`.
- The actual Commonwealth Part 9 approval dated **16 October 2026** references final **15 October 2026** OAMP versions; their exact original worksheets and any express expert justification for unusual gains **remain unacquired**. Do not substitute earlier consultant plans silently.

## Exact source-typed model

Proponent source coefficient for 14 koala rows: **1,010,350** (areas in tenths of hectares, quality gain integer and confidence in percent). Under the original January PD model: impact quantum **89.6 adjusted hectares**, 20 years to ecological benefit, annual extinction p=0.002 (2019 vulnerable assumption), zero gain from averted-loss branch. All original source inputs held fixed except an EXPLICIT hypothetical maximum on each AU quality-gain difference. Source-exact rational formula:

\[
C(\theta)=\frac{\sum_i A_{i,\mathrm{tenths}}\times\min(\Delta Q_i,\theta)\times c_i}{8960}
\left(\frac{1000}{1002}\right)^{20}.
\]

| Conditional max gain | Exact integer coefficient | Koala percent of impact compensated | Relative to 90% direct |
|---|---:|---:|---|
| None: literal reported AU gains up to four | **1,010,350** | **108.34513262%** | Above |
| Three | **882,325** | **94.61634002%** | Above |
| Two | **717,325** | **76.92252413%** | **Below** |
| One | **453,625** | **48.64458929%** | **Below** |

**Six** of the 14 source rows have claimed gains above one; **four** exceed two; **three** exceed three. The certificate is a **sensitivity of the published OAG**, not a scientific claim that gains must be restricted to one/two/three. It also does not establish that any particular consultant failed to attach a justification; that needs source-receipt checking.

### Highest-alpha locality: Mount Walker West 155.5 ha

The two nonremnant/open-paddock MWW AUs **50.8 + 104.7 = 155.5 ha** (separate from the 155.4 ha restoration headline) carry all of its claimed **50.02%** koala offset. Both score **0/30 current koala density** and project OAG gain **3→7**. With all Esk and Avonvale inputs fixed at proponent claims:
- MWW source gain four: full package **108.3451%**.
- MWW gain three: full package **95.8388%**.
- MWW gain two: full package **83.3325%**.
- MWW gain one: full package **70.8262%**.

Thus **the proponent's Mount Walker West improvement must be justified at a level substantially exceeding two OAG points if the other original model outputs are kept unchanged and the ordinary 90% direct-offset benchmark is tested**. This turns the proponent's 20-year planting, flowering, canopy structure, koala use and confidence assumptions into decisive targeted evidence. It does not say the source is barred from claiming more than one point: the official guidance expressly permits higher improvement if supported by strong scientific evidence.

## Adversarial exception evidence certificate demanded, not presumed supplied

For **each of the six above-one-point quality gains** obtain: original sampling start date / raw GPS AU baseline; explicit future-*without* as well as future-*with* counterfactual; full 20-year vegetation/growth, soil/climate, drought/fire, koala food tree and actual surviving maturity model; independent site-specific expert methods and uncertainties; historical outcome and accountable responsible party; exact one-to-one 15 October final approved worksheet cell and 95C consideration evidence. A proponent's own forecast is not independent validation.

QUT/QCC's mature-canopy/thermal-refuge/corridor critique is **separate and survives even if exceptional vegetation-quality forecasts are accurately justified**. The 2012 guide calls for site condition, site context, stocking/density and connectivity relevant to species viability, with the same impacted attribute represented on both sides. RSPCA originals corroborate wildlife treatment/return to named Woogaroo landscape, not all four AU occupancy or particular approved clearing GPS.

## Implementation and reproducibility

- Golden Agda: [SensibLawWoogarooQualityGainEvidenceCut20261106Exact.agda](../../DASHI/Law/SensibLawWoogarooQualityGainEvidenceCut20261106Exact.agda), native Nat 14-row coefficient witnesses at caps 1/2/3 and original source coefficient. **Source-written, no Agda --safe acceptance established.**
- Python: [check_woogaroo_quality_gain_evidence_cut.py](../../scripts/check_woogaroo_quality_gain_evidence_cut.py), exact Fraction arithmetic and original source provenance. A separate independent local Python reconstruction was executed, checked source and three cap coefficients, and saved a JSON receipt in this conversation. **The repository script is not itself claimed to have run on repository CI/parallel_checker.**
- Both \`SensibLawWoogarooPreservationEverything\` and \`Law/Everything\` roots import the new golden.
- Previous QUT/QCC, source-typed 56-row OAG reconstruction, fourteen decisive tests and SLR source-persistence gates remain canonical. No new approved OAMP, original 95C/95B, offset declaration, or field trial is fabricated.

## Exact remaining maximum cut

**P0 scientific exception**: final original 15 Oct 2026 OAMP **and** raw OAG xlsm + scientific evidence underwriting six >1 gains, specifically MWW AU1/AU2's 4-point uplifts, independent ecological justification and actual 20-year confidence.

**P0 decision consideration**: actual 95B 1,786 comments, original QUT/QCC treatment and 95C recommendation; full applied current law of the listing status (Vulnerable 2019 vs Endangered 2022), including saved/transitional provisions and actual accepted calculator.

**P0 actual ecology**: same-function Woogaroo habitat/corridor/refuge impacts from original field/GIS and original 2019/8575 action polygon; comparator with offset population/time ecology and no double count of prior conserved areas.

**P1 statutory security**: Queensland section 19F declarations, original mapped title/dealing dates, real commencement/clearing and annual monitoring records. No actual condition breach is evidenced.

**V exact kernel**: parallel_checker and Agda 2.9 --safe at actual branch SHA; no CI or independently verified compiler result is claimed here.

**Scope firewall:** Scenic EPBC 2020/8651, Peninsula EPBC 2020/8629, nearby historical clearing, asset/political adjacency and financial transfer speculation are not same-action legal facts.
