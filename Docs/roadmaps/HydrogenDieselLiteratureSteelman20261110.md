# Literature-grounded hydrogen/diesel combustion steelman — quantitative source audit

Prepared 2026-11-10. User-directed research, ChatGPT-authored numerical model and DASHI integration. All original research findings, measurements, and mathematical/engineering methods retain their source attribution. This report is **not** an observation of any McLaren/XFuel device.

## Primary published research and exact scope

1. **Karlis Amatnieks, Ruslans Smigins, Tomasz Skrzek, Jonas Matijošius, Aivars Birkavs (2026).** “Combustion Phasing, Performance and Emissions of a Single-Cylinder Diesel Engine with Intake Manifold Hydrogen Addition Under Varying Load and Speed.” *Energies* 19(17), 3951. DOI **10.3390/en19173951**. https://www.mdpi.com/1996-1073/19/17/3951
   - AVL 5402, 1200/1500/2000/2500 rpm, 5–25 Nm. At *different selected conditions*: peak pressure increases up to approximately 20%, pressure-rise rate increases up to 56%, CA50 advanced by up to 3.5° at 2000 rpm/25 Nm, and combustion duration increased by up to 46%. Some lower-load modes **reduce** peak pressure.
   - These reported extrema **must not be combined as if measured simultaneously**. Hydrogen addition is not monotone, and high cylinder pressure does not imply a proportional increase in brake/shaft efficiency.
2. **L. Estrada, E. Moreno, A. Gonzalez-Quiroga, A. Bula and J. Duarte-Forero (2022).** “Experimental assessment of performance and emissions for hydrogen-diesel dual fuel operation in a low displacement compression ignition engine.” *Heliyon* 8(4), e09285. DOI **10.1016/j.heliyon.2022.e09285**. https://pmc.ncbi.nlm.nih.gov/articles/PMC9039835/
   - Table 1: 78-mm bore, 62.57-mm stroke, 296 cm³ stated displacement, CR=20:1; single-cylinder small generator.
   - Table 3: 20 L/min H2 flow, 13.45 V, 15.1 A listed cell electrical parameters; AC-fed electrolyser and storage/bubbler setup reported separately.
   - Table 5: H2 density 0.0899 kg/m³ (293.15 K, 101.325 kPa), LHV 119.7 MJ/kg; diesel LHV 42.5 MJ/kg.
   - **Source reconciliation:** reported-flow H2 power = (20 L/min)/1000 × 0.0899 kg/m³ × 119.7 MJ/kg ÷60 s/min = **3587.01 W LHV**; listed cell DC V×I = **203.095 W**. The ~17.66x mismatch means we cannot identify those values as the same continuous complete input/output boundary. Possible differences: measurement window, stored gas, electrical supply/staging, cell array, instrument or documentation. This is not proof of misconduct or excess-energy physics.
   - **Metrics firewall:** Eq. (9) “Brake Fuel Conversion Efficiency” uses BP/(diesel energy + hydrogen energy), whereas Eq. (10) “Brake Thermal Efficiency” references diesel-only baseline fuel. Relative percentage claims must be distinguished. Hydrogen energy share in this study was **18–37%**: this is not a tiny-H2 dose regime.
3. **Ksenia Siadkowska, Grzegorz Barański, Rafał Sochaczewski and Mirosław Wendeker (2022).** “Experimental Investigation on Indicated Pressure and Heat Release for Direct Hydrogen Injection in a Dual Fuel Diesel Engine.” DOI **10.12913/22998624/149300**. https://www.astrj.com/Experimental-Investigation-on-Indicated-Pressure-and-Heat-Release-for-Direct-Hydrogen%2C149300%2C0%2C2.html
   - Distinct four-cylinder 2636-cm³ ADCR test engine; hydrogen dose 0–160 L/min, 1500 rpm, indicated pressure and heat release. Results are **not** taken as a McLaren apparatus calibration.
4. **Engine heat-release physics:** published ideal single-zone first-law pressure relation \(dQ/d\theta = \gamma/(\gamma-1)\,p\,dV/d\theta + V/(\gamma-1)\,dp/d\theta\), with heat transfer and changing \(\gamma\) omitted here. See DOI **10.3390/en19071657** and DOI **10.3390/en19071657** https://www.mdpi.com/1996-1073/19/7/1657.
5. **Wiebe mass-fraction-burned function:** \(x_b = 1-\exp[-a((\theta-\theta_0)/\Delta\theta)^{m+1}]\) with source-selected parameters and combustion duration; DOI **10.3390/jmse8030204**, https://www.mdpi.com/2077-1312/8/3/204. Wiebe parametrisation is conventional modelling, not a measured fuel property.

## Conditional theoretical reconstruction

The executable local model is distributed as `hydrogen_literature_physics.py` in the conversation deliverables. It uses *Estrada* geometry only; the additional rod/crank=3.5, \(\gamma=1.35\), 1-bar BDC, 400 J/cycle apparent heat release, initial SOC=−10°, burn duration 50°, \(a=5\), \(m=2\) are **user-directed model assumptions, not reported by Estrada or Amatnieks**.

Modelled indicated work from \(\oint p\,dV\) (compression+expansion only; no friction, heat loss, pumping or generator losses):

| Conditional scenario | Peak pressure (bar) | Ideal indicated cycle work (J) | Relative work |
|---|---:|---:|---:|
| Assumed baseline | 65.249 | 234.684 | reference |
| Shift CA50 3.5° earlier at same heat and burn shape | 74.683 | 240.826 | +2.617% |
| Shift CA50 3.5° later | 58.753 | 227.515 | −3.055% |
| Increase assumed burn duration by 46% | 58.467 | 206.184 | −12.144% |
| Decrease burn duration by 12.5% | 72.994 | 241.428 | +2.874% |

**Interpretation:** pressure peak can increase much more than ideal work. These scenario shifts come from *different publications and/or different operating modes* and must not be represented as a joint empirical diesel/H2 observation. This is an **illustrative sensitivity calculation**, not a fitted predictive model, and model indicated work is not brake thermal efficiency.

## Exact energy-share identity for 30% diesel reduction

If baseline chemical diesel input is \(F_0\), hydrogen energy fraction of *engine* fuel is \(h=H/(F+H)\), and true engine efficiency ratio is \(r=\eta_1/\eta_0\), fixed useful output gives:

\[
F/F_0=(1-h)/r,\qquad
H/F_0=h/r,\qquad
E_{el}/F_0=h/(r\eta_{el}).
\]

Thus a 30%-diesel-only reduction requires \(r=(1-h)/0.70\).

| H2 engine chemical share | Efficiency ratio needed for 30%-diesel cut | Interpretation |
|---:|---:|---|
| 0% | 1.4286 | 42.86% relative improvement required |
| 2% | 1.4000 | 40.00% relative improvement |
| 5% | 1.3571 | 35.71% relative improvement |
| 10% | 1.2857 | 28.57% relative improvement |
| 18% | 1.1714 | 17.14% relative improvement |
| 37% | 0.9000 | Diesel can fall 30% even with 10% lower conversion efficiency |

At H2 share=10%, \(r=9/7\) (e.g. 35→45% efficiency), 100 kWh baseline diesel gives 70 kWh diesel, 7.7778 kWh H2 and 11.111 kWh external electricity assuming 70%-HHV electrolysis. All-external-input saving under those assumptions is only about 18.89%, before auxiliary/heat/storage costs.

**No fixed pressure/CA50 measurement entails a particular value of \(r\).** True conversion efficiency is determined by full crank-angle pressure and pumping/friction/heat-release/heat-transfer effects; fitting kinetics and testing predictions against independent data remain open.

## Source and attribution firewall

- Original experimental observations: named original author groups and exact DOI, engine, test state, operating point and measurement definition.
- Classical thermodynamics/Wiebe: original engine-literature sources, not McLaren or ChatGPT original discoveries.
- DASHI: earlier module/theorem owners remain credited.
- New source comparison: user-directed question and ChatGPT-authored implementation, not externally replicated physics.
- Patent/corporate statements and the 2026 grant: separate authority; never inferred from existing research.
- No Agda kernel acceptance asserted (K0 not prioritised).
