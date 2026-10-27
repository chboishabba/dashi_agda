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


## 26 October continuation: native commuting squares and exact Fourier–Poisson / Jones/Stokes cuts

### The repository's commuting-square owners are **not** a visual metaphor

The generic models pre-exist this branch:
- `DASHI/Physics/Limits/PhysicsLimitCommutingSquare.agda` (path independence, residual-controlled and scale-indexed/asymptotic cases).
- `DASHI/Core/GovernedDiagramCore.agda` (typed witnessed square and nonpromotion).
- `DASHI/Core/ReopenableConsumerInterventionKernelExact.agda` (intertwiner and explicit consumer descent defect).
- `DASHI/Physics/Common/CoarseDynamicsCommutatorExact.agda` (additive defect interpretation).
- `DASHI/Core/ApproximateIntertwinerCompositionExact.agda` (only compose quantitative stage defects under the required metric/nonexpansiveness).
- `DASHI/Physics/CFD/BoundedDefectSparseTwistOperator.agda` (finite-iteration error propagation is not exact closure).

`DASHI/Physics/Optics/FourierPixelCommutingSquaresExact.agda` imports **actual** owners, not a duplicate declaration, and provides four classes of formal claims:

1. **Same-device forward/readout square**:
   `Input --physicalOutput(surface)--> Output --digitize∘intensity--> Recorded`
   equals `Input --measured(surface)--> Recorded` **only because**
   `SameDeviceFourierPixel.measuredWeld` is supplied. It produces both
   `PhysicsLimitCommutingSquare.ExactCommutation` and the existing
   `ReopenableConsumerInterventionKernelExact.Intertwiner`.
   This is a model-level theorem **conditioned on the physical weld**, not
   an independent experimental verification.

2. **Inverse design/execution square**:
   `Goal --makeSurface--> Surface --physicalOutput(excitation)--> Output`
   equals `Goal --targetField--> Output` only when a
   `SameDeviceDesignContract.designCorrect` witness exists. This
   correctly keeps the ideal inverse operator, fabricated profile and measured
   physical response distinct.

3. **Constructively inhabited four-state sensing square**:
   `Phase4 --quadratures--> QuadratureReadout --decodeFourPhase--> Phase4`
   equals `Phase4 --id--> Phase4`. The code supplies four explicit
   decoding cases and a restricted round-trip proof. This is **not**
   continuous Jones-field injectivity, nor a theorem about a particular
   fabricated sensor's measurements.

4. **Two quantified no-go results using the generic consumer/commutation
   theorem**:
   (i) bare intensity cannot factor the phase-sensitive quadrature
   observer; an input-output coarse sensor map would force `4 = 0`;
   (ii) clipping each quadrature at one merges the phase-0 and phase-90
   codewords, so universal decoding is impossible. Device-specific dynamic
   range calibration is therefore an independent prerequisite.

This matches the source/authority discipline seen in recent PR #1269
(SI-typed same-device NV calibration), #1266 (consumer-observer no-go), and
#1249 (operator intertwining; same cardinality is not the same physics).
The quantitative inverse/noise programme remains owned by optics PR #1111.

### Paper Methods (23)–(29): exact coherent Jones/Stokes witness

`scripts/check_fourier_pixel_stokes_exact.py` reuses the earlier file's
Gaussian-rational operations to verify the paper's particular calibrated
quarter-wave interference convention:

```text
Ix = |Ax|²/2, Iy = |Ay|²/2
I(phi) = |Ax + exp(i phi) Ay|² / 2
S0 = 2(Ix + Iy), S1 = 2(Ix - Iy)
S2 = I(0) - I(pi)
S3 = I(3pi/2) - I(pi/2)
```

Seven independent exact rational synthetic Jones fixtures all match the
direct `S0,S1,S2,S3` formulas, satisfy the pure-state identity
`S0² = S1² + S2² + S3²`, and remain unchanged under a common
quarter-wave global phase. A 50:50 incoherent horizontal/vertical mixture
has `S0=1`, `S1=S2=S3=0`; it is **not** a pure Jones field.
This prevents transferring a pure-coherent theorem to uncharacterised
partially coherent/incoherent illumination.

For the four-codeword phase readout `(4,2),(2,4),(0,2),(2,0)`,
the minimum pairwise **L-infinity distance is 2**, giving a
mathematical uniqueness margin under independent per-channel error
strictly less than `1` (in **synthetic intensity units**, not photons).
After clipping at one, only three distinct codewords remain.
Neither number is a measured optical SNR or sensor specification.

### Paper Methods (30)–(31): genuinely gauge-quotiented square

The paper reconstructs phase from gradient maps using a discrete
Fourier Poisson solve with the DC/constant mode fixed. We now distinguish:

```text
Phase --gradient--> MeasuredEdges --divergence/Poisson--> Phase
  |                                                |
  +------------------- gaugeFix --------------------+
```

The upper path equals `gaugeFix(phase)` only for a **compatible exact
gradient** in the same discrete operator and selected boundary geometry.
An absolute phase can never be determined from gradients alone: global
phase shifts are a fibre of `gradient`.

`DASHI/Physics/Optics/FourierPixelGradientPoissonSquareExact.agda`
specialises the repo's `ExactCommutation` to an explicit
`PhasePoissonModel` proof-obligation record and uses the pre-existing
`ConsumerDescentDefect` to express the no-universal-absolute-decoder
claim. For data supplied with an `ExactEdgeField` witness, reconstructed
gradients equal the measured edges. For an `IncompatibleEdges` receipt
(e.g. a proved nonzero loop circulation), **exact recovery is impossible**.

`scripts/check_fourier_pixel_phase_poisson_exact.py` numerically models
a **synthetic exact 4x4 periodic torus**, using only exact rational
Gaussian arithmetic and the DFT symbol
`2 cos(kx) + 2 cos(ky) - 4` with integer eigenvalues. Executed:
- exact 2D DFT/inverse round trip;
- a synthetic real phase map reconstructed exactly after zero-mean gauge fixing;
- global shift `7/3` gives identical gradients and identical reconstruction;
- exact gradient has zero plaquette curl;
- perturb one horizontal edge by `+1`: loop curl at origin becomes `+1`, exact edge recovery fails, and the divergence-free gradient-projection residual has exact squared norm **17/32**.

The positive residual and circulation obstruct the **unqualified** commuting
square on arbitrary measured edge data. They do not refute the paper's
regularised Poisson estimator. This toy uses a periodic grid and unwrapped
rational phase; the real apparatus may require other boundary conditions,
wrapped phase, weighting, heterogeneous noise and calibration.
Mathematical projection is not photon-noise calibration.

### Physical interpretation and severe-test gate

There are **three distinct senses of “bidirectional”**:
1. a device generates a prescribed outgoing optical field from guided input;
2. a device encodes incident-field information into multiple coherent
   readouts, whose inverse is identifiable only on a declared class;
3. under suitable reciprocal, linear materials, a **port-normalised**
   scattering matrix may obey an optical reciprocity relation.

(1) + (2) do **not** logically prove (3), and reciprocal scattering is
**not** an algebraic inverse of lossy intensity detection. Do not name
Lorentz reciprocity as a theorem of this source-written finite model.
Classical coherent interference is not entanglement/observer-induced
collapse, and no new quantum mechanism is demonstrated by these tests.

**Remaining max-cut boundary:**
- SAME fabricated structure: complex vector optical transfer matrix with
  wavelength/incidence/gauge, SEM/topography, and corresponding phase-intensity
  readings; proof-carrying calibration is separate from the paper's plots.
- Controlled `ResidualControlledCommutation`: choose meaningful
  detector-output metric, confidence/noise model, physical tolerances and
  measured same-device residuals before claiming a small defect.
- Restricted stable inverse / margin for the calibrated sensing matrix,
  with photon counts, detector clipping, crosstalk, nonuniform response,
  partial coherence, and phase wrapping; target includes relative phase,
  never a chosen-but-unobserved global gauge.
- Addressable dynamic operation: active material/electro-optic actuator,
  refresh rate, drive power, array routing, simultaneous optical throughput,
  thermal/crosstalk limits, and independently operated pixel number.
- Multiscale/rate-scaling requires the earlier native
  `AsymptoticCommutation` **with a genuinely vanishing residual**;
  a sequence of larger static devices does not automatically provide it.

### Repeatable local checks

```bash
python3 scripts/check_fourier_pixel_exact.py
python3 scripts/check_fourier_pixel_stokes_exact.py
python3 scripts/check_fourier_pixel_phase_poisson_exact.py
# Agda kernel status remains open:
# repo-pinned Agda checker on the three FourierPixel*.agda files
```

All three Python local counterparts executed successfully on 26 October.
All source files have been separately read back from the GitHub PR branch.
No claim of independent execution of the retrieved GitHub blob, CI success,
Agda kernel verification, measured-device validation, or physical display
product is made.

**Attribution:** physical experiment and Methods equations © original
Glauser/Vonk/Seda et al. research team (the Nature paper is the original
source root; arXiv is an earlier version). Standard mathematical Fourier,
Poisson, Jones/Stokes and Hodge ideas retain their historical owners.
Repository formalisation is derivative/independent mathematical analysis,
prepared with OpenAI ChatGPT assistance; it is not attributed to the
experimental authors and is not an experimental replication.
