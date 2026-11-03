# Tesla-tower emitter: claim audit and exact max-cut (2026-11-03)

## Scope and provenance

Primary analyzed input: `transcript-2026-11-03.srt` (00:00–02:29).
The proposed *large emitter* is Tesla's **Wardenclyffe-scale tower**, not a
microtubule ensemble. Source-written finite invariants and external empirical
claims must never be promoted interchangeably.

Historical primary source: Nikola Tesla, US patent 787,412 (1905),
https://patents.google.com/patent/US787412A/en . Tesla described an
Earth-conduction/standing-wave design and reported wavelengths of about
25–70 km. These are patent claims, **not independent demonstrations** of
global power transmission or any mental effects. If one uses free-space c
merely for comparison, those observed lightning-disturbance wavelengths are
approximately 4.3–12 kHz: the VLF Earth–ionosphere waveguide regime, not
the **fundamental** Schumann mode. Critically, the *same patent also explicitly*
proposes a resonant driving range below 20 kHz, naming **6 Hz as its
suggested lower limit**. That operating proposal includes the measured
first Schumann mode near 7.8 Hz. It was incorrect to treat Tesla's quoted
25–70 km lightning observations as the exclusive range for his transmitter.
Actual ground phase velocity is an independent unknown. Do not attribute
modern quantum-mind claims to Tesla.

## Source-owner reuse and exact legal promotion boundary

- `DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary`:
  historical rotating-field/polyphase context vs modern DASHI extensions.
- `DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact`:
  field/source/medium/validation reference socket.
- `DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope`:
  Maxwell curvature, sourced field equation and gauge obligation.
- `DASHI.Promotion.MaxwellHodgeSourceConservationObligations`:
  source current and Hodge conservation; promotion not yet paid.
- `DASHI.Physics.Foundations.RFCalibrationSourceAtlasExact` and
  `RFArrayManifoldSourceAtlasExact`: finite RF source/receiver
  calibration and geometry owners.
- `DASHI.Cognition.QuantumMindRetypingBoundary`:
  never assume microtubule qubits or causal quantum consciousness.
- `docs/research/psychotronics-phase1-lineage-edges-20261025.csv`:
  prior lineage ledger; historical source genealogy is not efficacy.

## Claim register, matching uploaded SRT

| SRT timestamp | Claim | Verification status |
| --- | --- | --- |
| 00:00–00:10 | Hidden Tesla discovery, psychotronic scalar tower | Patent shows electrical transmission proposal, not psychic use |
| 00:10–00:24 | Tower tunes quantum potential, projects apparitions/thoughts | Unsupported; Bohmian quantum potential is not Maxwell scalar potential |
| 00:24–00:38 | Bearden/Puharich nonlocal information devices | Speaker attribution only; no reproducible measured channel identified |
| 00:38–01:02 | Soul/information matrix/nuclear plasma | Not a defined independently measured physical plasma |
| 01:02–01:18 | ELF scalar links and a hidden Tesla machine | Real ELF electromagnetic modes do not establish a new scalar carrier |
| 01:18–01:22 | Tesla used magic | No verified causal engineering relevance |
| 01:22–01:46 | 'Lorentz gauge squares' and potential-only transmission | Lorenz condition is divergence of A plus time derivative of phi; alleged quadratic is incorrect; pure-gauge configurations in Maxwell cannot transmit an independent ordinary observable |
| 01:46–01:55 | Hameroff/Puthoff private conversation | Reported, not independently verified |
| 01:57–02:08 | Microtubules are Josephson receivers/carrier of consciousness | Hypothesis; neither current-phase relation nor RF brain decoding established |
| 02:08–02:18 | Ingo Swann transmits through shielding | No reproducible shielding-proof controllable information channel established |
| 02:18–02:29 | Program speculation implies exotic EM physics | Speculation is not a measurement or experimental acceptance |

## Three physical branches that must NOT be equated

1. **Classical RF radiation or Earth-conduction coupling**. Large phase-coherent
   oscillating charges are possible; a classical coherent radio source does
   not thereby demonstrate a macroscopic nonclassical quantum state.
2. **Schumann cavity modal excitation**. Schumann resonance is a known
   dissipative Earth–ionosphere electromagnetic eigenmode, with Q around 4–6
   in typical reviews, but not automatically an RF-to-ELF frequency converter.
3. **Extended Aharonov–Bohm scalar/gauge-wave proposals**. Minotti & Modanese
   (EPJ C 83, 1086, 2023, DOI 10.1140/epjc/s10052-023-12274-4) present a
   theoretical extended model with anomalous nonconserved effective currents
   and proposed probes. Its paper states no experimental data are listed.
   It is NOT evidence that Wardenclyffe produced these modes.

## Quantitative receipts and constraints

`scripts/tesla_tower_emitter_maxcut.py` implements these toy checks:

**Ideal short monopole (57 m height, perfect ground; not ground electrode):**
`R_rad = 40*pi^2 * (h*f/c)^2`. At 7.83 Hz this is approximately
`8.75e-10 ohm`. A purely hypothetical 1000 A RMS current would radiate
`0.875 mW` in the antenna approximation, before ground return and source losses.
At 100 kHz the same approximate resistance is `0.1427 ohm`. These
parameters are not established Wardenclyffe operating figures.

**Amplitude modulation gate:**
`(1+m cos(2*pi*8*t)) cos(2*pi*100000*t)` has source spectral lines at
99,992, 100,000 and 100,008 Hz, not at 8 Hz. Linear propagation does not
supply a new 8 Hz oscillation. An ELF source or identified conversion process
is a separate physical obligation.

**Conditional single Schumann mode, not a Maxwell simulation:**
`P_mode = eta*P_in`, `U = P_mode*Q/omega`, and for an assumed
uniform equivalent volume `V=4*pi*R_earth^2*h_eff`, with equal mean
electric/magnetic mode energy, `E_char = sqrt(U/(eps0*V))`.
With *hypothetical* `P_in=1 MW`, `eta=1%`, `Q=5`,
`h_eff=80 km`, `f=7.83 Hz`:
`P_mode=10 kW`, `U≈1016 J`, `E_char≈1.68 mV/m`.
The actual mode field is nonuniform; this is not a measured surface or neural
field. Receiver transfer is additionally unknown.

**Inverse/identifiability:** for exactly the same tower height, a scenario with
zero source-to-mode coupling has zero selected mode power, whereas a scenario
with nonzero coupling can have a nonzero mode. Receiver amplitude transfer
can independently vanish. Therefore geometry/size alone cannot decide
received signal. The Agda finite counterexample
`towerHeightDoesNotDetermineSignal` expresses the structural impossibility.
The Agda three-bin model proves `noDirectEightHzLine` only *within its
linear AM frequency ledger*; it does not prove an analytic cosine identity
or empirical propagation.

## Exact remaining physical cut: explicit non-promotion

| Gate | What would pay it | Status |
| --- | --- | --- |
| T0 original historical parameters | Calibrated tower drive frequency/current/voltage and original contemporary measurement | OPEN |
| T1 tower + ground source | Original conductor/electrode geometry, ground conductivity, Maxwell current distribution | OPEN |
| T2 phase/mode matching | Actual boundary-value field solution and overlap with Earth–ionosphere eigenmode | OPEN |
| T3 power and loss | Coupling, dissipation, spectral purity, realistic modal Q | OPEN |
| T4 conversion | Actual low-frequency source or *selected* measured nonlinear frequency mixing; artificial 7.8–8.0 Hz excitation via ionospheric heating was shown experimentally in 2014, but is not a Wardenclyffe bridge | OPEN for Wardenclyffe |
| T5 conventional receiver | Calibrated received E/B, impedance, SNR and information bandwidth | OPEN |
| T6 biological receiver | Same-field inside-tissue exposure and reproducible neurophysiological decoding | OPEN |
| T7 novel physics | Competing ordinary-EM null model, measured anomalous-source/probe response, replicated exclusion of ordinary EM | OPEN |
| F0 finite-source impossibility | Countermodel of same tower geometry, distinct coupling worlds | SOURCE-WRITTEN; Agda kernel pending |
| F1 AM example bookkeeping | Three frequencies and absent 8 Hz bin, analytic premise explicit | SOURCE-WRITTEN; Agda kernel pending |
| P0 local numerical budget | Python checks and illustrative inverse | EXECUTED; NOT physical validation |

## Citable original/technical references

- Tesla patent 787,412: https://patents.google.com/patent/US787412A/en
- Schumann resonance Q and modes: https://doi.org/10.1029/2011GL049668
- Schumann cavity technical review: https://www.mdpi.com/2073-4433/7/9/116
- Minotti/Modanese extended theory: https://doi.org/10.1140/epjc/s10052-023-12274-4
- Biological UV tryptophan work: https://pmc.ncbi.nlm.nih.gov/articles/PMC11075083/

## Verification

Run `python scripts/tesla_tower_emitter_maxcut.py`.
The in-repo Agda file has `{-# OPTIONS --safe #-}` and contains no postulates,
holes or termination pragmas, but **no independent Agda kernel acceptance was
obtained in this workspace**. Do not promote it to a golden accepted theorem
until `agda --safe` executes against this exact revision. Do not promote
Wardenclyffe-to-brain communication at all absent physical validation.

## Correction/addendum: Schumann excitation, damping versus coherence

Tesla's patent 787,412 contains *both* the 25–70 km **observational
lightning-wave estimate** and the explicit **6 Hz suggested low-frequency
operating bound** (with suggested frequency below 20 kHz). Schumann's first
resonance at ~7.8 Hz therefore sits in his contemplated operating band,
although no contemporaneous Wardenclyffe 7.8 Hz excitation or corresponding
measurement has been verified.

Two physically distinct electromagnetic regimes remain admissible:

- VLF propagation around Earth (4.3–12 kHz from Tesla's observed wavelengths
  if converted at free-space c): a real guided electromagnetic propagation
  regime, but **not** the low-order 7.8 Hz Schumann resonance.
- A transmitter with **actual drive spectral support and nonzero source-to-mode
  overlap near 7.8 Hz** could maintain a planet-scale forced Schumann response.
  Grounded tower geometry alone does not provide either datum.

**New experimental lead:** Streltsov et al., *Artificial excitation of ELF waves
with frequency of Schumann resonance* (2014), DOI
https://doi.org/10.1016/j.jastp.2014.07.004 . HAARP's modulated HF ionospheric
heating yielded observed 7.8–8.0 Hz ELF waves in 8 of 46 cases.
The relevant current-modulation/conductivity response is **nonlinear**,
so this does not contradict the *linear AM spectrum counterexample* and
does not establish Wardenclyffe's direct ground-coupling efficiency.

For a single **linear damped resonator** with f0=7.83 Hz, Q=5:
`Delta f=f0/Q≈1.57 Hz`, `tau_energy=Q/(2*pi*f0)≈0.102 s`,
`tau_amplitude=2*Q/(2*pi*f0)≈0.203 s`.
These are **free ringdown** measures after drive removal, not limits on
driven phase coherence. Continuous phase-stable driving can maintain a forced
phase coherent response, at the cost of ongoing dissipation. Actual observed
Schumann peak frequency is variable; 7.83 Hz is an illustrative center.

**Quantum scope:** a spatially extensive coherent electromagnetic field is not,
by itself, a nonclassical entangled field. Ordinary coherent quantum states
may be separable between modes; linear mixing of coherent inputs does not
produce entanglement. `Q` alone does **not** prove or disprove entanglement.
At T=300 K, `k_B T/(h f0)≈8e11` sets a high thermal occupation scale
for 7.83 Hz, implying stringent noise/isolation requirements for
nonclassical witness tests. No such experiment is supplied by the transcript.

**Critical correction to physical toy budget:** The hypothetical 1%-coupled,
1-MW source yielding 1.68 mV/m under a *uniform cavity-equivalent volume*
is neither a historical estimate nor a plausible coupling certificate.
With the separate short-57m-monopole **far-field** approximation at 7.83 Hz
and 1000 A RMS, the illustrative far-field radiated power is only ~0.875 mW.
Those deliberately different coupling models must **not** be silently joined.
A grounded-Earth-mode overlap is not established by that antenna result.

Additional primary research and reviews:
- https://doi.org/10.1016/j.jastp.2014.07.004 (artificial ELF excitation)
- https://doi.org/10.1029/2011GL049668 (Schumann modes, Q)
- https://doi.org/10.1002/2015RS005683 (Earth–ionosphere ELF/VLF waveguide)
- https://doi.org/10.1103/PhysRevA.71.062319 (coherent states vs entanglement)

Status: source-written correction; no actual receiver or Schumann-mode tower
source-coupling measurement, and no kernel acceptance claimed.
