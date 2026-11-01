# Diffuser imaging: source, observer quotient, and detector budgets

## Provenance boundary
Source: attached `transcript-2026-09-27 (2).srt` (17 cues, 0:00–1:41).
The speaker describes point-to-caustic mapping, translated superposition,
a pinhole-measured PSF and deconvolution, depth-dependent PSFs, and claimed
single-snapshot 3D imaging; the work is attributed to Laura Waller Lab.
The transcript **does not** mention DiffuserCam by name, wave diffraction as
the chosen physical approximation, ODT, a sparse-recovery algorithm, or
quantitative bit-depth and noise bounds.

The following operator model and detector analysis are **new reconstruction**,
not claims verified by that video.

## Optical forward model versus digitised observer
For lateral position `r`, depth `z`, and detector index `j`, use the
calibrated intensity-response operator `H[j,(r,z)] >= 0` under a mutually
incoherent, linear-intensity, unsaturated regime:

`lambda_j = sum_(r,z) H[j,(r,z)] v(r,z) + background_j`.

Depth-dependent PSFs identify a family of columns, not guaranteed recoverable
3D structure. On a restricted scene class C, a reconstruction theorem must
supply a decoder D and prove `D(Hv) = v` for `v in C`. Conversely, such a
decoder implies `H|C` injective. With noise, one additionally requires a
quantitative restricted inverse condition, e.g.
`||v-w|| <= kappa ||H(v-w)||` for `v,w in C`, and an explicit
error bound for the selected decoder.

A finite camera records *charge*, then clips/quantises. A more faithful
stochastic detector model is:

`N_j ~ Poisson(lambda_j)`

`Q_j = clip_ADC( gain_j * (N_j + read_noise_j), 0, W_j )`

with appropriate pixel-dependent gain, full-well, dark signal, and digitiser
definitions. Do not apply additive white Gaussian noise *after* clipping as a
stand-in for the actual ordering of the detector process.

Two sources contributing `q_1` and `q_2` charges to the same pixel produce
`q_1 + q_2` in the linear regime. If this exceeds the full well, the
recorded datum is saturated; other unsaturated sensor samples might still
constrain the scene, but the clipped datum itself does not distinguish
supra-threshold values.

For a Poisson-dominated pixel, the variance of accumulated counts is
`lambda_j`. A bright overlapping scene contribution therefore adds shot
noise even when the sought-after recovered voxel is dim. This is a
multiplex-disadvantage mechanism, not a universal theorem that a diffuser
camera has lower SNR or lower effective precision than every lens camera.
Spreading a concentrated bright spot across multiple wells can sometimes
*prevent* a focused-spot saturation.

Nominal ADC bit depth is neither recovered voxel precision nor a direct
claim about colour gamut. Spectral sampling, colour filter array response,
metamerism and colour-space output gamut must be treated separately.

## Exact finite Agda ownership

`DASHI/Physics/Optics/DiffuserImagingObserverDynamicRangeExact.agda`:

- Defines an explicitly law-bearing forward intensity encoder with depth PSF
  response and linear superposition.
- Separates pinhole calibration from actual inverse reconstruction.
- Proves that an admitted round-trip decoder implies identifiability.
- Computes a detector saturation collision: clip_1(1) = clip_1(2).
- Proves no universal decoder exists for that clipped scalar measurement.
- Proves any downstream postprocessing preserves this collision.
- Computes overlap-before-clipping: clip_1(1+1) = 1.

**No measured PSF, physical shot-noise distribution, all-scene 3D
injectivity, stable inverse, compressed-sensing guarantee, or CI kernel result
is claimed by these finite proofs.**

## Cross-pollination without physical conflation

- `DASHI/Foundations/HyperformObserverFactorisationExact.agda`:
  observation-fibre distinctions and postprocessing non-recovery are the same
  abstract obstruction as sensor clipping. The native observer API is a
  follow-on target if a consumer-specific witness is needed.
- `DASHI/Physics/Optics/CatastropheDiffractionNormalFormExact.agda`:
  geometric caustic -> wave diffraction is deliberately mediated by a
  local-scale physical receipt; it cannot be inferred from the reel alone.
- `DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda`:
  spectral/observer colour projection is distinct from physical intensity
  and ADC bits.
- `DASHI/Physics/Holography/AreaLaw.agda`:
  counts admissible states against area in an entropy-style abstraction.
  A 2D detector encoding 3D scene parameters is a useful *analogy* to
  observation/fibre compression, NOT evidence for a physical/gravitational
  holographic area law.

## Next mathematical wall

To obtain a *physical* theorem rather than a generic codec:

1. Calibrate or derive actual depth-indexed, spectrally resolved PSF columns
   with stated coherence, geometry, intensity and sensor assumptions.
2. Define a nontrivial admissible scene class C and prove a quantitative
   restricted inverse/stability estimate for those same columns.
3. Add a detector-specific probabilistic full-well/ADC/read-noise model and
   prove an estimator risk/dynamic-range bound.
4. Optimize the physical mask under both restricted separation and
   saturation/shot-noise constraints; compare it to a conventional lens under
   *matched throughput, pixel budget and scene distribution*.

An information-theoretic objective such as maximizing `I(V;Q)` must account
for the actual prior on `V`, photon statistics and the quantised saturated
observation `Q`. A nominal `M*B` output alphabet bound alone does not
provide per-voxel `B`-bit accuracy.
