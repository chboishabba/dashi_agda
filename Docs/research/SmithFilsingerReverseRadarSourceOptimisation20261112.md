# Reverse-radar / EM attractor — source-physical maximum cut (2026-11-12)

**Original claim provenance:** Smith's loaded-dipole / transverse capacitor and multi-pickup environmental supply conjecture are in the user-supplied Kelly/Darrer 147-page compilation. Filsinger's powered ZVS, variable megohm bleeders, Earth-electrode contacts and hypothetical portable midpoint/golden plate are *different* source claims/occasions. Do not identify their circuits merely from names.

**Engineering steelman:** a tuned, actively controlled electromagnetic **receiver/absorber** that reduces impedance mismatch, couples multiple orthogonal resonant modes and extracts energy from finite, characterised source ports. Synthetic aperture by signal processing raises detection/angular resolution but **does not** increase rectified received watts. Physical antenna arrays increase effective reception by intercepting fields over their physical aperture, with directional gain and losses. Earth, galvanic, atmospheric DC/ion, RF and ionising particle sources must have independent field and conversion models.

## Local Python physical-source optimisation (no CI)
`/mnt/data/reverse_radar_maxcut/optimize.py` (self-contained) executed **19/19 PASS**, with `results.json`, `source_scenarios.csv`, `aspect_sweep.csv`, `aspect_optimisation.png`. Local artifacts are not same-object experiments. No Agda kernel receipt.

* Finite Earth Thevenin source: P=Voc² Rload/(Rs+Rload)². Maximum P=Voc²/(4Rs) at matched load. **48V is a reported capacitor-bank voltage, not proven Earth Voc**. Conditional 48V Earth Voc and Rs=1440Ω yields 0.4W; Rs=10000Ω only .0576W.
* Powered 3.8V return example: Rs=2Ω, Rload=20Ω, variable Rground. Rground=10Ω gives .282W load; Rground=0 gives .597W load. Exact source work pays all load and ground/internal heat. This identifies a ground-dependent *return-path mechanism* without introducing ambient energy.
* Finite RF field: assumed incident density 63µW/m², ηrectifier=.7, ηmatching=.9. 0.4W requires 10,078m² **effective** aperture; 159988W requires 4.03e9m² effective aperture. This is not a geometric footprint, an experimentally measured Filsinger field or an upper bound on purposely beamed/near-field WPT. Beamforming redistributes pattern under a fixed total incident power budget.
* Two-mode rectangular receiver, fixed area, synthetic two-band field: the aspect-ratio optimum follows the input spectral ratio. Incident ratio 1.3 -> optimum 1.3, golden captures .2079 fraction vs theoretical optimum .7 in the selected lossy model. Incident ratio golden -> optimum golden. This is not a real Maxwell antenna eigenmode.
* Extractive load coupling must be finite: η=4γsource γload/(γsource+γload+γloss)²; for γsource=.04, γloss=.02, best γload=.06. Trapped current circulation alone does not optimise useful output.

## Highest-alpha remaining (real original physical mechanism)
P0: source-selected Smith/Filsinger pin-level diagrams (Smith fig10/11/40, original powered Earth and hypothetical portable network).
P0: signed actual Earth open-circuit and loaded dynamic V/I with electrode chemistry/meter reference; simultaneity with input drive and other supplies.
P0: frequency-pulling electrical waveform vs acoustic ~7.8kHz ±few Hz and actual resistance, temperature, core state.
P1: measured local RF/atmospheric/DC/particle source spectra; physical antenna effective height/aperture, alignment, feed, rectifier and loss. Actual Maxwell/Poynting port flux and calibrated output real power.
P1: nonlinear driver/rectifier/ground coupling and finite source depletion/dynamic model; compare reflected-load behaviour and measured incremental output.
P2: only if observed, coherent ELF source coupling; a global cavity or Schumann numerical resemblance is not an energy-transfer receipt.
P2: Agda 2.9 same-object kernel check. Reuse current Circuit36927 and Maxwell/Hodge BIDI owners; ZVS is a replaceable driver, not the canonical device.

Sources for physical mechanisms: IEEE rectenna review DOI 10.1109/MAP.2020.3012872; 2026 RF rectifier/matching review https://onlinelibrary.wiley.com/doi/10.1155/je/4227736; original PDF supplied in conversation. No validated environmental energy extraction claimed.
