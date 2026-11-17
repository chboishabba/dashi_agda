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


## 17 November M2 four-terminal same-aperture and M3 exact p² scalar obstruction

### M2 new REAL published four-terminal comparator

Green et al., *Solar cell efficiency tables: Version 68*, Joule 10 (2026), 102494, DOI https://doi.org/10.1016/j.joule.2026.102494, reports an independently verified **35.9 ± 0.5% one-sun GaInP/GaAs//Si 4-terminal mechanical stack** (NREL 02/2017, designated illumination area 1.002 cm²). Unlike the AIST 775 cm² module notable-exception entry, this cell's two contact groups have printed pairs that permit a coherent *same-aperture* published-number identity:

| Subcell contact group | Voc V | Jsc mA/cm² | FF % | Derived source-printed PCE contribution % |
| --- | ---: | ---: | ---: | ---: |
| GaInP/GaAs top tandem | 2.520 | 13.6 | 87.5 | **29.988000** |
| Si bottom | 0.681 | 11.0 | 78.5 | **5.880435** |
| Combined, same source aperture | | | | **35.868435** |
| Independently reported PCE | | | | **35.9 ± 0.5** |

The delta is −0.031565 **percentage points**, consistent with source rounding and explicitly NOT an error/correction to certification or a worst-case calibrated instrument bound. For a 4T stack, sum *separately extracted* component powers per one COMMON incident aperture; never sum 2T voltages/currents or independently illuminated unrelated device cells. It is a 3-material-junction physical stack with two independent electrical groups, **not** a 4J4T physical measurement. Original individual IV raw curves, steady-state MPP and spectral/EQE/actual aux-source files are not present in this round; therefore it **cannot** inhabit the new P5/P7 metrology acceptance and cannot claim any 369 improvement.

Implemented `scripts/check_pv_v68_published_multijunction_table_identity.py` with source-specific exact rational 4T two-group components (and previous 2T/QW controls), and `DASHI/Physics/Photovoltaic/PVGreen68FourTerminalPublishedSourceExact.agda` with exact Nat 29.988000+5.880435=35.868435 and 0.031565pp reporting delta, plus source-specific open metrology interface. Imported through the original `DASHI/Unified/PVPrimaryTOESpliceExact.agda`. Local independent Fraction arithmetic reproduced the four source identities; the committed script itself and native Agda have not been executed from an exact checkout.

### M3 original atomic result rules out a false 369 solar mechanism

The existing owner `DASHI/Physics/Chemistry/AtomicPeriodicTable369P2CoulombExecutionExact.agda` already **exactly computes** hydrogenic common-spin antisymmetric 2p² selected Coulomb `Vee = (21/128)I₃`. Its off-diagonal entries are zero, diagonal entries all identical, and it commutes with the existing finite C3 action. Those are REAL formal calculations of a selected interaction, but the scalar operator **cannot itself generate a p² subspace level splitting**, distinguished oscillator strength, improved EQE, or actual photovoltaic benefit. This is a sharp **negative control**, not a claim the entire real atom/semiconductor is degenerate.

New `DASHI/Physics/Photovoltaic/PV369P2CoulombSolarNonPromotionExact.agda` *imports* the original interaction producer and C3 proof and checks equality of all three selected diagonal entries, off-diagonal zeros and symmetry. No arbitrary 369 wavelength bins, no copying original Coulomb theorem as novel, and full attribution retained. It is part of the original TOE import graph. **Actual live M3 physical cut remains the same-object continuum/Hilbert projection plus environmental crystal, corrected Kane/Bahder 8-band, spin–orbit, [111] strain/piezo, optical transition and carrier-extraction operator**. A changed physical spectrum/polarization/EQE versus conventional C3v must be predicted and observed before attributing 369 to real efficiency.

### M1 existing-source reuse verified, not kernel-accepted

The repaired Nat rectangle proof uses `Data.Nat.Properties.*-mono-≤`, independently present in `DASHI/Physics/ClaySupportingResidencePipeline.agda`, `DASHI/Core/FiniteBlockSurvivalCountDecayExact.agda`, and other original modules. Align its imports with the existing `open import Data.Nat ...` and `open import Data.Nat.Properties ...` repository conventions. Run the updated M1 runner on the pinned local checkout; it now includes the two new M2/M3 original-source Agda modules. **No Agda binary or locally cloneable GitHub DNS was available in this runtime; do not report local Golden PASS.**


## 17 Nov M1 fail-closed acceptance and M2 topology/precision max-cut

**M1 fail-closed source correction:** `scripts/check_pv_369_m1_local_acceptance.py` must **always exit 2 when the native `agda` executable is missing**, not zero without `--require-agda`, regardless of whether the exact committed Python test suites pass. It reports `exact_checked_out_python_passed` independently of the Agda availability/error, and only claims `all_formal_gates_passed` for both native and original-source execution acceptance. The runner now includes seven direct Python suites and **ten** Agda entry roots including the new published-source topology. It is still unexecuted from exact remote checkout, so do not invent a pass.

**M1 Agda performance correction:** Original `PVGreen68FourTerminalPublishedSourceExact.agda` used `Bound.≤-append 35,900,000 14,100,000`, requiring 35.9 million recursive unary-order constructors. Preserve the precise `35,900,000+14,100,000 ≡ 50,000,000` identity with `refl`, but derive an explicitly coarse **one-decimal-percentage-unit** proof `Bound.≤-append 359 141` (359≤500). This is an execution-relevant proof-performance repair, not a replacement of source numerical values.

**M2 original Table 4 publication rounding closure:** For the source NREL (02/2017) one-sun GaInP/GaAs//Si mechanical 4T stack, source fields are `Voc=(2.52,0.681)V`, `Jsc=(13.6,11.0)mA/cm²`, `FF=(87.5,78.5)%`. Printed exact central per-group 4T contributions sum **35.868435%**. Under an **explicit, declared rounding-to-nearest LAST PRINTED DIGIT model**—not instrumental error—multiply each parameter's rational lower/upper display intervals. The exact separate-terminal aggregate is:

```
published-field lower  35.6471117625 %
central reconstructed   35.8684350000 %
published-field upper  36.0904685375 %
independent report      35.9 ± 0.5 %
```

Published 35.9% lies in the printed-field precision interval; the alleged reporting discrepancy of −0.031565 percentage points does NOT justify challenging the certified efficiency or converting the publication rounding interval to an uncertainty confidence bound. Executable source `scripts/check_pv_v68_printed_4t_rounding_interval.py` uses `fractions.Fraction` exact rational arithmetic and 14 checks (source written; not exact-checkout run). Independent in-session Python `Fraction` numerical cross-check confirmed the exact lower, upper and center. Source is 2026 Green et al., *Joule* DOI [10.1016/j.joule.2026.102494](https://doi.org/10.1016/j.joule.2026.102494), itself reporting the 2017 NREL conventional 4T.

**M2 crucial TOPOLOGY source correction:** A four-terminal **GaInP/GaAs//Si** stack does NOT have four optical junctions. It has exactly **three optical absorbers** (GaInP, GaAs and Si) and **two independently loaded electrical groups**: a GaInP–GaAs series-connected upper tandem and an independent Si output. New `DASHI/Physics/Photovoltaic/PV369NREL2017ThreeJunctionTwoGroupTopologyExact.agda` types this exact source anatomy and proves the GaInP/GaAs shared output and Si group distinction. New `scripts/check_pv_nrel_2017_4t_group_topology.py` enforces wavelength-local exclusive absorber partition `R+A_GaInP+A_GaAs+A_Si+T=1`, and under a **non-multiplication, one extracted electron per absorbed photon** baseline, each independently observed group current must satisfy the appropriate absorption-current upper bound: `Jsc_top<=min(Jabsorbed_GaInP,Jabsorbed_GaAs)` for the series tandem and `Jsc_Si<=Jabsorbed_Si`. Adversarial cases reject invented fourth absorber, false three-independent-output topology, wavelength reorder, duplicate photon energy, missing photons, and over-cap current. It does **not** infer a real GaInP/GaAs EQE from summed absorptions, and **does not fabricate actual measured original JV**. A separate P4 multiplication mechanism would need its own source and charge/energy evidence rather than bypassing the upper bound.

The topology module imports the existing formal 4T source and semiconductor continuity and was attached to `DASHI/Unified/PVPrimaryTOESpliceExact.agda`; no ESD owner edits. The original P5 source parser still models a set of *independently loaded outputs* as `numberOfJunctions` in some paths. A future genuine physical source producer must disentangle `numOpticalJunctions` from `numElectricalGroups`, with source-owned intra-group series-matching, before accepting the NREL group data as per-junction 4T IV.

**Current empirical gates:** externally authenticated original steady-state raw IV for each electrically independent output, original per-absorber spectral R/A/T/EQE, same actual device/collimated illumination/aperture, and calibrated entire IV/auxiliary/converter uncertainty remain OPEN. No 369-specific predicted physical operator/positive observation or measured >50% device. P1 corrected Bahder, P3 driven, P4 multiplication, P6 BH4 continue as independent physical cuts. M1 actual native Agda acceptance remains OPEN.
