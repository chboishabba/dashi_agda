# Smith/Filsinger golden-Fibonacci phase maximum cut — 12 Nov 2026

## Exact source re-read
User PDF: Darrer (ed. 2022), based on Kelly's compilation. Separate original Smith narrative, Kelly/editor interpretation, Filsinger reels and new mathematical models. Kelly warns that most devices were not independently built or tested. An exact Smith-origin 1.618 plate prescription was **not located in the parsed text**; Filsinger calls for the 1:1.618 rectangle in his proposed portable antenna. User's 1.68 was a typo, not an independent aspect ratio.

* **PDF pp47–51, Figs 27–29:** L1-to-L2 **wire length** ratio **1:4**, tunable movable winding, two L2 sections of 17 turns each, example of 5⅔ turns with physical angular end offset 240°, L1 100nF-tuned capacitor (two 47nF caps in parallel reported for photographed setup), optional L2 tuning capacitor. Winding angle ≠ electrical phase.
* **PDF pp80–82 Figs 53–55:** opposed/out-of-phase L2 branches, diode arrangement and two Earth grounds. Opposed **collinear** branch currents ≠ demonstrated orthogonal surface-current vortex. A mutual-coupled network is source- and wiring-dependent.
* **PDF pp10–16:** source claims driven dipole + perpendicular capacitor plates. This supports investigating anisotropic electromagnetic coupling, not an independently established energy-gain observation.

## Physically separate geometric hypotheses
- Historical Smith 1:4 wire ratio suggests **possible rational-harmonic matching**. Under ideal distributed waves with same phase velocity and endpoint boundary conditions, a four-times-longer guide has a quarter fundamental frequency and can share a harmonic. Coil modes generally depend on self inductance, interturn capacitance, material and coupling, so this is only a toy calculation.
- 17+17 winding branches can support equal-magnitude opposite-phase **terminal** signals if wiring/excitation admit them. There is no automatic orthogonal current rotation.
- Filsinger proposed φ plate can support different orthogonal resonant responses. A **single incident coherent linearly polarised electromagnetic wave** couples to both orthogonal modal channels if its field projection is nonzero on each. The two modal transfer functions alone can create near-quadrature with suitable split resonances, feed, damping and reactive tuning. The φ ratio alone does NOT ensure quadrature.
- Fibonacci ratios 3/2, 5/3, 8/5, 13/8, 21/13 and 34/21 converge toward φ. Exact φ is irrational, thus no exact finite p:q locking; approximate rational p:q can lock only if actual nonlinear coupling exceeds combination detuning. Comparing ratios is a *new mathematical model*, not a claim that Smith specified Fibonacci tuning.

## Local max-cut Python receipts (NO CI, NO Agda kernel claim)
`/mnt/data/smith_golden_maxcut/single_wave_modes.py` ran **16/16 PASS**. Two *orthogonal components of ONE coherent plane wave*, each incident channel carrying half of 1 normalized unit; fixed-area mode frequencies f_x=1/√r,f_y=√r, response a_j=√(γe)/(γtot+i(f_j−1)) with γe=.04, intrinsic=.02, load=.04. Extractable load power is 2γload Σ|a_j|²≤1; circularity is 2 Im(conj(ax) ay)/Σ|a_j|². Synthetic results:
|ratio|untuned |circularity||untuned useful fraction|
|---|---:|---:|
|1 square|0|0.640|
|1.500 (3:2)|0.784|0.126|
|1.600 (8:5)|0.708|0.0993|
|φ=1.618|0.695|0.0955|
|1.625 (13:8)|0.691|0.0941|
|1.667 (5:3)|0.664|0.0864|

Under a **conditional independent reactive modal tuning** to f_x=.9 and f_y=1.1 with damping width γtot=.1, φ requires +14.48% x-frequency, −13.52% y-frequency shifts. It gives circularity magnitude 1 and extracted useful fraction 0.32: single coherent input produces quadrature but not extra net energy. The 1–4MΩ HV bleeders do not by themselves establish those reactive shifts.

`/mnt/data/smith_golden_maxcut/phase_lock.py` ran **6/6 PASS**, p:q combination detuning for a further *separate* hypothetical f_x=7800Hz,f_y=φf_x. E.g. 21:13 requires ~269Hz combination-pulling strength in a simple Adler-type law; this is NOT the few-Hz wandering of Filsinger's *acoustic* 7.8kHz carrier, and the electrical clock is still unmeasured. A geometric 240° winding-end angle cannot be imported as a measured electrical 240° phase.

Outputs: `single_wave_ratio_comparison.png`, `source_figures_47_82.jpg`, `golden_fibonacci_modes.csv`, `fibonacci_locking_requirements.csv`, `modal_results.json`, `MaxCut_2026-11-12.md`, and executable scripts are available as local artifact package `smith_golden_maxcut.zip`.

## Formal ownership
New `SmithFilsingerRatioSourceBidiExact.agda` represents Smith 1:4 lengths and split-secondary claims separately from Filsinger φ plate, with forward predicted observables, reverse same-object Maxwell/source admission obligations and finite non-confusion proofs. The full antenna Maxwell boundary eigenproblem, actual source-to-surface-current Poynting flux and physical resonant-locking coefficient remain **OPEN**. Existing `Circuit36927`, symbolic Maxwell exterior calculus and boundary-spectrum BIDI owners are the reusable carriers; ZVS is replaceable driver technology, not canonical circuit identity.

## Highest-value next physical cut
1. Digitise Smith Figure 28 pin-level transformer/diode/capacitor/return schematic with figure-specific provenance; measure/retain unknowns.
2. Select actual Filsinger driver, 1/2/4MΩ shunt endpoints and Earth/blue/green/white capacitor circuits for each separate reel.
3. Choose real rectangle material, dimensions, thickness, feed and counterpoise; solve full Maxwell boundary modes with complex fields and load, then sweep φ vs Fibonacci approximants under ONE identical incident plane wave and source power budget.
4. Fit any nonlinear modal coupling and phase attraction to actual voltages and electronic frequencies; acoustic ±5Hz alone cannot identify this mechanism.
5. Independent Earth/atmospheric/RF/ionizing and powered source-port real-work metering; prove measured gain versus existing driver to establish supplementary environmental extraction.
6. Agda 2.9/Nix same-revision kernel verification is pending; no CI inference.
