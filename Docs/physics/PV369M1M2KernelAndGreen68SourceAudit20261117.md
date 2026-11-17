# PV369 M1 acceptance repair and M2 real 2026 conventional source audit — 17 Nov 2026

Original user goals: **(A)** independently measured more than 50% **NET** solar-to-electric energy under a common source/aperture/time, driver and auxiliary deductions; **(B)** a genuinely **369-derived PHYSICAL** advantage beyond a mere C3v / p-triplet change of basis. Maintain original P1 Bahder GaAs QW, P3 actively driven/RF, P4 multiplication, P5 optical multijunction, P6 BH4 biologically generated carriers, heat only auxiliary.

## M1 critical actual-code corrections in PR #1523

A repository source audit found `scripts/check_pv_g173_same_sample_optics_eqe_iv_weld.py` had literal backslash-n characters inserted inside executable Python between `wl=spec[:,0]`, its conditional full ASTM G173 source parser, and an adversarial selftest case. That made the module syntactically invalid. The final selftest also used an undefined `ivs` name where the actual fixture is `iv`. These are patched in place in source commit `677a4f36`, **not** presented as formerly passing tests.

Formal gap: `PV369UnsampledIVPowerEnvelopeExact.agda` contained `sampledRectangleProducts` as an additional ASSUMED record field, which made the natural-number upper bound circular. This was replaced (commit `0c31f419`) with `rectangleProductBound` derived by converting source-owned `Circuit36927RecoveryEnergyBoundExact._≤_` into standard `Data.Nat._≤_` and applying the existing published stdlib `Data.Nat.Properties.*-mono-≤`, then converting back. The `rectangleForSegment` result now follows from only two physical component-order premises. **Native Golden Agda kernel check remains OPEN**; this is a source-level kernel candidate, not a proof assistant acceptance receipt. Attribution to Agda standard library and original motor Nat order retained.

New dedicated local Golden runner `scripts/check_pv_369_m1_local_acceptance.py` uses Python `py_compile` on exact checked-out scripts, runs 6 exact original selftest/fixture suites, accepts both the historic `passed` and `checks_passed` counter names, and checks all 7 new/modified Agda source roots. `--require-agda` fails with code 2 if the native compiler is absent, never silently marks all formal gates complete. It reports JSON `all_formal_gates_passed` only if **both** exact checked-out Python suites and native Agda succeed. **Not executed from the remote repository checkout in the current tool environment**: GitHub hostname unavailable from local container; `agda` and Nix not installed. Thus M1 status is SOURCE FIXED / exact local acceptance OPEN.

Reproduce on host with pinned versions:

```bash
python scripts/check_pv_369_m1_local_acceptance.py --require-agda \
  --output m1_pv369_exact_local_acceptance.json
```

A previously reported 36/36 synthetic mathematical sampling audit is independent of exact committed program execution and cannot replace M1.

## M2 real-source 2026 photovoltaic control

Primary publication: **Martin A. Green, Ewan D. Dunlop, Masahiro Yoshita, Nikos Kopidakis, Karsten Bothe, Gerald Siefer and Jessica Yajie Jiang**, *Solar cell efficiency tables: Version 68*, *Joule* 10(7), 102494, published July 2026, [DOI](https://doi.org/10.1016/j.joule.2026.102494). This open-access 2026 source reports independently confirmed one-sun PV results and source/EQE–JV data in supplement **Data S1 (Excel graphs)**. It explicitly notes that multijunction plotted JV sweeps are **not** the original quasi-steady-state measurements from which PCE was independently certified. Data S1 raw spreadsheet was not fetched in this round, and **no actual same-sample raw multi-channel 4T optical/JV dataset is present**.

New `scripts/check_pv_v68_published_multijunction_table_identity.py` executes exact `fractions.Fraction` identities on original printed, reported one-sun 2T photovoltaic table values (not fabricated model values):

| Published type | Voc (V) | Jsc (mA/cm2) | FF (%) | Printed efficiency (%) | Reconstructed (%) | Difference (pp) |
|---|---:|---:|---:|---:|---:|---:|
| LONGi perovskite/Si 2T, ESTI Feb 2026 | 1.998 | 20.55 | 85.2 | 35.2 ± 1.1 | 34.982183 | −0.217817 |
| NREL GaInP/GaAs(mqw) 2T, Jan 2020 | 2.500 | 15.36 | 85.7 | 32.9 ± 0.5 | 32.908800 | +0.008800 |
| NREL GaInP/GaAs(mqw)/GaInAs 3J, Sep 2021 | 2.997 | 15.44 | 85.3 | 39.5 ± 0.5 | 39.471449 | −0.028551 |

Formula for same-source one-sun standard denominator 1000 W/m2: PCE[%] = Voc[V] × Jsc[mA/cm2] × FF[%] / 100. The source's reported `±` uncertainty is not a bounded worst-case power interval. **No adjustment to an independently certified figure is justified** by multiplying rounded printed numbers. The first row's 0.218 percentage-point mismatch may arise from distinct source/area/spectrum/Jsc/reference measurement conventions or reporting precision; it requires **primary footnote and measurement receipt** verification. It is flagged OPEN, not labeled wrongdoing or corrected.

**Older published 4T reference:** `InGaP/GaAs // Si`, 33.7 ± 0.7% at AIST Feb 2023, printed contact-group `Voc=(20.3,2.83)V`, `Jsc=(1.25,1.93)mA/cm2`, `FF=(86.5,78.0)%`. These are separate electrical contacts / potentially differing source and areal normalizations; directly applying ONE 2T VJFF formula or summing nominal contact results would be unsound. The M2 script explicitly blocks this promotion and requires actual multiple-contact specimen/area/illumination records.

**Why this is high-alpha:** P5 and P7 previously assumed that a 4T/5T *model* could be joined to measured terminal output if someone supplied a spreadsheet. The source control gives actual independently verified reference device results to constrain what the importer may claim, and flags the exact missing physical normalization/steady-state footnotes before accepting any independently contacted or 369-specific source. The original Data S1 source is a future ingest/visualization target and cannot validate a 4T stack just because it contains tandem EQE/JV curves.

## Next route by priority

1. **M1** native pinned Golden and exact Python runner. Fix any real traceback; no CI-only shortcut and do not edit `*ESD*` / `digital_esd` sources.
2. **M2** retrieve official Version 68 Data S1 original, identify actual physical sample, cell area, irradiance, test centre, measured vs plotted EQE/JV, original quasi-steady-state MPP. Never turn plotted sweep maxima into independent certification. Seek separately sourced **true 4T4J/4T5J** same-aperture channel files rather than piecing unrelated devices together.
3. **M3** source-match full corrected Bahder 1990/1992 8-band Γ basis against QW spectroscopy, and formulate a **genuinely different 369 physical operator** whose predicted polarized absorption/terminal response is distinguishable from conventional Td/C3v. A basis label is not sufficient.
4. **P3/P4/P6** continue independently; account for drive input, carrier multiplication at useful voltage, redox/electron/fuel products with no conversion of chemical work to an electricity numerator.
5. **P7** only after original measurement source + instrument bounded uncertainty: robust lower net output strictly exceeds half the upper incident solar, and lower proposed-369 net output strictly exceeds conventional upper under the same source. Both experimental endpoints are still OPEN.
