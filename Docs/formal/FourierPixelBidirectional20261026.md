# Fourier pixels: source-bound optical formalisation and physical gates (26 October 2026)

## Primary source roots and credit

- **Original peer-reviewed research:** Yannik M. Glauser, Sander J. W. Vonk, David B. Seda, Hannah Niese, Boris de Jong, Matthieu F. Bidaut, Erwan Bossavit, Daniel Petter, Gabriel Nagamine, Nolan Lassaline, David J. Norris. *Fourier pixels for bidirectional light control.* **Nature 655, 87–92 (2026)**; received 20 December 2025, accepted 20 May 2026, published 24 June 2026. https://doi.org/10.1038/s41586-026-10681-7. The 13 January 2026 arXiv preprint, https://arxiv.org/abs/2601.09022, has earlier title *Fourier pixels for reciprocal light control*. These are **one research lineage, not independent replications**.
- **Social-media interpretation:** ScienceNow Instagram screenshot supplied by the user (26 October 2026): one-colour static prototypes, 2-by-3 array, external SLM dynamism, speculative future camera/display. Treated as a derivative description, **not** an empirical source independent of the Nature paper.
- **Original DASHI contribution (this branch):** finite phase-readout no-go/identifiability Agda source, exact Gaussian-rational Python Fourier and spectral fixtures, this claim-to-obligation ledger. **No original authorship of the underlying photonics or optical theory is claimed.**

## What the paper physically demonstrated

- Silver/plasmonic Fourier pixels with Fourier-derived shallow wavy profiles: Gaussian vortices of topological charge +1, +3, +5; holographic projections and foci; vector beams and polarization multiplexing; phase-gradient and Stokes readout; simultaneous phase sensing and focal generation in one pixel (Extended Data Fig. 10j–m).
- A silicon-nitride waveguide image-projection example (Fig. 1h), not a fully integrated tunable SiN camera/display.
- An **actual 2×3 array** of 10×10 µm full-field sensors (Extended Data Fig. 9f); not a large operational display or a demonstration that those six elements form a complete imaging-camera display.
- External liquid-crystal SLM in the microscope excitation path adjusted polarization and focal positions (Extended Data Fig. 10). It did **not** electrically reconfigure fabricated surface profiles.
- Paper reports >40% measured power throughput for specified 500–700 nm cases, 17% hologram speckle contrast and mean signal/background 68 for a particular example; **these are device/example-specific**, not population-wide guarantees. Estimated higher-order crosstalk suppression ~1e5 relative to desired outputs comes from the authors' shallow-relief model, not a universal experimentally demonstrated isolation theorem.
- Phase control under suitably coherent conditions; a spectrally/angle-filtered halogen lamp also produced an image. Arbitrarily broadband incoherent wavefront reconstruction is **not established**.

## Formal design model and exact scope

The authors' Methods equations (3)–(9) motivate:

    complex guided reference r(x,y) × complex transparency t(x,y)
              → sample-plane complex field f(x,y)
              → calibrated Fresnel/Fraunhofer forward operator P
              → target complex output g(x,y)
              → detector intensity and digitisation

In the ideal linear regime, inverse-design solves `f = P⁻¹g`; the target local transparency is `t = f/r` where `r ≠ 0`. A **real** shallow height profile is then constructed from the anti-Hermitian component of `f/r`. This construction creates target, guided-reference and conjugate/mirror Fourier terms. Interpreting the selected term as the radiating signal assumes spectral/light-cone separation, material dispersion, finite fabrication precision, coherent illumination and negligible higher orders. One cannot replace the physical selective outcoupling with an unqualified identity `radiated = g`.

Agda owner: `DASHI/Physics/Optics/FourierPixelBidirectionalExact.agda`:

1. A same-device calibrated optical model **record** whose fields are obligations, not theorems about the experiment.
2. A conditional inverse propagation record distinguishing a mathematical inverse from real-wave backpropagation.
3. Finite four-phase counterexample: bare intensities of `1,i,-1,-i` all coincide; therefore no universal bare-intensity phase decoder exists on that carrier.
4. A restricted two-quadrature witness: ideal `|E+1|², |E+i|²` readouts are `(4,2), (2,4), (0,2), (2,0)` and are injective on those four states; the `|E+1|²` channel alone is noninjective.

Python executable: `python3 scripts/check_fourier_pixel_exact.py`. Uses exact `Fraction`-backed Gaussian rationals, not floating-point claims:

- 4-site DFT/IDFT round trips and discrete Parseval on five synthetic vectors;
- physical-intuition quadrature arithmetic and finite collision;
- a **16-bin frequency group-ring fixture** for paper Eq. (8): with reference mode 4, mirror shift 8, desired modes `{0,1,15}`, a *stipulated* radiative projection on these three bins isolates one-half the desired field without mirror interference;
- a counterexample to universal spectral separation: desired mode 8 creates an unwanted conjugate ghost in radiative mode 0. Hence shallow-profile sideband decomposition **alone** does not imply unconditional emission of arbitrary fields in a finite model.

The 16-bin radiative projection is *by definition a synthetic routing hypothesis*, **not** a Maxwell radiation-cone derivation. The half-amplitude scaling is explicit, so no unearned 100% efficiency claim is made.

## Repository prior-art owners and cross-pollination

- `DASHI/Physics/Optics/DiffuserImagingObserverDynamicRangeExact.agda`: existing clipping/no-universal-decoder and restricted-inverse boundary; **reuse for noise and identifiability**.
- `DASHI/Physics/Optics/FresnelZonePlateDiffuserCodecBridgeExact.agda`: distinct coherent amplitude interference vs incoherent intensity addition; **no direct equality of the two models**.
- `DASHI/Physics/Optics/MultiscaleApertureSynthesisKernelBridge.agda`: Fourier aperture overlap and phase-gauge alignment; informs large-array stitching but does not prove it.
- `DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda`: explicit approximation regimes and physical calibration limits.
- Agda PR #1111 (Waller/DiffuserCam) is the quantitative inverse-and-measurement template; PR #1246 (Ferrocell) is the classical Fourier-null/quantum-claims separator; PR #1268 is the source-revisability precedent. No new generic evidence ontology or optics kernel is introduced.

## Pareto / snowball roadmap — high-value discriminators

| Priority | Objective | Acceptance receipt | Why it matters |
| --- | --- | --- | --- |
| P0 | Same-geometry calibrated forward model (including SPP propagation and outcoupling) | Nanometre topography, wavelength, amplitude/phase/polarization resolved measured transfer matrix; independent comparison of model to observations | Bridges mathematical inverse to a fabricated device |
| P0 | Phase/polarization identifiability | Selected-scene restricted singular values and robustness to photon/ADC/read noise, explicit gauge convention | Formal readout uniqueness must survive physical observation |
| P1 | Multifunctional interference/crosstalk | Measure intended/mirror/stray diffraction efficiencies and wavelength incidence sweeps, not only perturbative suppression estimate | Tests real spectral separation and mode interference |
| P1 | On-device electronic programmability | Actuator/material prototype that changes the *surface transfer operator* without an external SLM, with update rate/power/endurance | Distinguishes static passive pixel from display technology |
| P1 | Dense array and camera-display geometry | Larger independently addressable array with optical fan-out, detection readout, spacing, thermal budget and pixel crosstalk | Six pixels do not demonstrate a practical screen |
| P2 | 2D vectorial and broadband extensions | Measured same-device transfer matrices across incidence, wavelength, polarization, coherence | Tests scalability beyond tuned demonstrations |
| P2 | Quantum optics claim, only if proposed | Photon-state preparation, state tomography/correlation or entanglement witness with proper controls | Classical coherence does not establish quantum advantage |

### Steelman

The inventive contribution is **not** that a passive surface suddenly becomes a camera and an LED. The authors use structured guided-wave coupling to move Fourier optics and coherent measurement functions into a compact architecture. Even without autonomous tunability, combined sensing and shaping can matter to microscopy, adaptive optics, compact interferometry and photonic integrated circuits.

### Main no-go / implementation frontier

Neither exact finite DFT inverses nor calibrated single-pixel experiments establish an addressable, full-colour, high-refresh, high-fill-factor, energy-efficient bidirectional display. That requires an additional tunable transduction/readout architecture and same-device physical receipts. The most informative next experiment is not another image of a hologram; it is a **closed-loop same-pixel correction** under independently varied incoming complex fields, followed by scaling and independent pixel addressability.

## Verification / status

- Python exact finite tests: locally executed PASS on 26 October 2026.
- Agda code: **source-written proof candidates**, not kernel-checked in this environment (Agda compiler unavailable). No CI claim.
- No measurement/raw dataset, actual topography, numerical Maxwell simulation or independent replication retrieved. The Nature paper states underlying data available from corresponding author on request.
