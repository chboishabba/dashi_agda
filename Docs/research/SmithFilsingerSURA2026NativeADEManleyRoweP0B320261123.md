# P0-B3/P0-B4 — native Filsinger Maxwell–ADE checkout verification and SURA conditional three-wave energy gate

**Date:** 23 November 2026 (Australia/Brisbane). **Status:** two existing GitHub source blobs and the new exact triad script are independently matched to their Git blob SHA-1 identifiers; all executed locally using Python 3.13.5 / SymPy 1.14.0. **No CI, Agda kernel, original ionospheric array, SI plasma simulation, input-power metering, or ground receiver-power measurement.**

**Original source:** A. A. Chernyshov et al., *HF Heating Effects as Seen From Below and Above: First Results of Joint SURA–Ionosfera-M Experiment*, *Geophysical Research Letters* 53, e2026GL123503 (first published 22 August 2026), [DOI 10.1029/2026GL123503](https://doi.org/10.1029/2026GL123503). **Experiment:** 20 August 2025; 5.350 MHz HF pump, 8 minutes on/4 minutes off; paper describes satellite electrical/magnetic 8–9 and 17–18 kHz bands as consistent with lower-hybrid and whistler-mode processes, and makes the physical interpretation conditional. **Original energy-relation donor:** J. M. Manley and H. E. Rowe, *Some General Properties of Nonlinear Elements—Part I: General Energy Relations*, *Proceedings of the IRE* 44 (1956), 904–913, [DOI 10.1109/JRPROC.1956.275145](https://doi.org/10.1109/JRPROC.1956.275145). **Ionospheric mechanism donor:** *Generation of whistler waves by continuous HF heating of the upper ionosphere*, *Radio Science*, [DOI 10.1002/2015RS005892](https://doi.org/10.1002/2015RS005892) (original parametric excitation and irregularity conversion). This DASHI consumer neither claims original discovery of those mechanisms nor identifies the actual SURA waves from its algebra.

## 1. Genuine repo-native ADE reproduction: prior gap closed

The two files were retrieved from the **live PR #1540 branch through the connected GitHub repository** and independently recreated byte-for-byte in the local Python execution directory. The local git hash-object values exactly match the connected GitHub blobs:

| Existing source | Git blob | Local execution |
| --- | --- | --- |
| scripts/smith_filsinger_lorentz_ade_sympy.py | `af7a88e58ff300837db3cf42c1a6f51509444244` | **Exact Git blob**, not an excerpt |
| scripts/smith_filsinger_sura2026_ade_source_weld_sympy.py | `6a126da7e41e8838112867a943519a936859c000` | **Exact Git blob**, not an excerpt |
| New scripts/smith_filsinger_sura2026_three_wave_energy_sympy.py | `7064beefbf404d6b1e517a5658e7247fe313f26e` | **Exact Git blob**, local PASS |

The exact original ADE file provides generator, exact_midpoint and synthetic_cycle_work_receipt, **imported directly** by the SURA adapter. The SURA adapter reports 12/12 finite step energy identities zero, total work residual zero, pump-off controller work zero, four-state return false, real source meter absent. This is now a genuine exact-blob local execution receipt of the **code**; it does not validate the choice of plasma coefficients, a Maxwell radiation boundary or empirical field transfer. The earlier source-equivalent-only audit remains as historical provenance but its native-code-execution debt is superseded by this receipt.

## 2. Essential gap in the physics: linear ADE alone is not the frequency converter

The existing Maxwell–Lorentz ADE is a fixed-coefficient linear time-invariant (LTI) field/material model. For a **steady single-frequency** source and with transients excluded, the phasor response at omega satisfies Z(omega)=(i*omega*I−A)^(-1)B J(omega). There is no separate steady spectral output at an unforced frequency, barring an explicitly frequency-changing source/material term. A physically imposed finite-time gate can create transient/broadband response and sidebands; this no-go is **not** a global theorem of zero off-frequency transients.

The current 12-step SURA adapter injects a low-frequency **synthetic** current into an existing passive port under the published 8-on/4-off clock. Therefore **the ADE proves conservation after injecting this current**, NOT generation of the published 8–9 kHz lower-hybrid/whistler signal from a 5.350 MHz pump. That conversion requires an attributed anisotropic nonlinear/parametric plasma source (plus phase matching and dispersion) that has not yet been constructed or calibrated.

## 3. Exact conditional Manley–Rowe three-wave energy partition

Consider **one ideal lossless three-wave decay event**: one HF parent of frequency f0 creates an HF daughter f1 and a lower-hybrid daughter fL, under the standard equal-action Manley–Rowe relation, where f0=f1+fL. At f0=5350 kHz and the observed **candidate** fL=8–9 kHz:

- f1 must lie within **5341–5342 kHz** (5.341–5.342 MHz), if this exact triad is applicable.
- The fraction of *depleted HF pump-wave energy in that one triad* allocated to the LH daughter is **fL/f0 = [8/5350, 9/5350] = 0.149533%–0.168224%**, while the rest goes to the HF daughter.
- The reported 17–18 kHz second band is compatible with twice a subset of the first band, namely **8.5–9 kHz**, but **a harmonic is not an additional independent energy reservoir**.
- A secondary passive LH→whistler conversion efficiency eta, propagation fraction rho, plasma damping and receiving load must be **separately metered**. Exact energy identity: E_pump_depleted = E_HF_daughter + E_plasma_loss + E_propagation_loss + E_receiver, with nonnegative passive shares under 0<=eta,rho<=1.

The [new script](../../scripts/smith_filsinger_sura2026_three_wave_energy_sympy.py) proves all identities with **exact SymPy algebra**, includes rational test cases (lossy and ideal) and a pure-harmonic fixed-LTI negative control. Local execution is PASS and matches the committed file exactly.

**Strict limitation:** this conditional one-event ratio is **not** the observed HF→VLF power conversion efficiency, **not** a bound for the entire ionospheric heating apparatus, **not** an invariant of cascades, multiwave interactions or natural ambient current reservoirs, and **not** an upper limit on externally metered receiver power from a system with additional independently sourced energy. The source paper has not measured the action rates, actual frequency/phase/wavevector matching, mode conversion eta, source work or electrical receiver load. **150 MW antenna ERP cannot be multiplied by the ratio to obtain inferred received watts**: ERP is not the depleted internal plasma pump power.

## 4. Original-data acquisition status and newly recovered archive locator

Original 2026 manuscript data availability links to [https://links.cosmos.ru/87-3f-d4-49](https://links.cosmos.ru/87-3f-d4-49), which the web reader follows to **https://disk.cosmos.ru/d/3a0ad689ac1e4d37bef9**. The destination is inaccessible in the web reader, and the local Python container cannot resolve either Cosmos host (it likewise cannot resolve raw.githubusercontent.com). This shows a **redirect/access limitation**, not that the study's data do not exist or are withheld. **No original optical/ionogram/SEE/NVK/LAERT/MAYAK bytes obtained, no checksums confirmed, no source time-series or spatial plasma fit replayed.**

The original paper itself also reports background VLF spectral variation **before the satellite entered the heated flux tube** and a separate ~21 kHz line associated with **LAERT sounding pauses**. Thus source pump status, LAERT instrument state and satellite orbit/flux-tube placement must be separate when constructing a causal inverse, and one pump-on pass is not a complete crossed experiment. The current toy rank 3/6 versus full factorial 6/6 is a mathematically valid *proposed design*, not the original authors' measured regression.

## 5. Priority, testing and attribution

1. **Empirical P0-B first:** recover original Cosmos archive via its redirected share, preserve file bytes, license, hashes and clock metadata. Demand actual field E/B spectra, pump, LAERT, NVK, background and geometry.
2. **Construct only source-appropriate physics:** re-use Smith/Filsinger ADE as passive receiving *numerical donor*; construct an identifiable causal three-wave nonlinear plasma port only with source-defined nonlinear coefficients, dispersion, pump energy and loss, then waveguide/spatial propagation to a measured receiver.
3. **Negative controls:** source off, different geomagnetic conditions, LAERT sounding/pause, flux-tube outside, harmonic vs independent spectral mode, and finite stored-energy depletion. A 21 kHz instrument-associated line cannot be promoted to a pump harmonic without direct discriminating evidence.
4. **Filsinger physical gate:** exact selected original netlist and real terminal source/load/return metering must precede an original apparatus efficiency claim. No attribution or priority reassignment to the independent earlier Manley–Rowe, SURA, or existing Filsinger/ADE authors.

**Related original owners:** [SmithFilsingerSunEarthCoupledGlobalCircuitMaxCut20261116.md](SmithFilsingerSunEarthCoupledGlobalCircuitMaxCut20261116.md), [SmithFilsingerSURA2026OriginalIonosphereHeatingWeld20261123.md](SmithFilsingerSURA2026OriginalIonosphereHeatingWeld20261123.md), [RadioBio/SURA P0 roadmap](../roadmaps/RadioBioHumanAlphaBetaBioelectricFieldCrossDomainRoadmap20261122.md), [Source Attribution Policy](../SourceAttributionPolicy.md), [Scientific Source Attribution Rule](../support/reference/ScientificSourceAttributionRule.md).

**Verification statement:** original repository code blobs + new conditional algebra **locally executed** (Python 3.13.5, SymPy 1.14.0); no GitHub CI; no new Agda type-check; NO physical plasma or receiver validation. 
