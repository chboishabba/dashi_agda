# Ferrocell, sacred geometry, and quantum-claim audit (2026-10-24)

**Status:** Research/formalisation max-cut. The photo/video identification is tentative; none of the material calibration, original video metadata, spectral images, or independent magnetometry were supplied. The result below tests **an idealised null model**, not the user's screenshot.

## Source roots and attribution

- Alberto Tufaile and Adriana Pedrosa Biscaia Tufaile, *Horocycles of Light in a Ferrocell*, **Condensed Matter** 6(3), 30 (2021), DOI `10.3390/condmat6030030`. Original research on Ferrocell optical image formation, luminous horocycles, conic sections and inversion/Möbius analogies. The paper's geometric image interpretation does **not** establish that the magnetic field has hyperbolic spacetime geometry.
- Alberto Tufaile and Adriana Pedrosa Biscaia Tufaile, *Structural Color and Mueller Matrix Analysis in a Ferrocell*, **Magnetochemistry** 11(10), 86 (2025), DOI `10.3390/magnetochemistry11100086`. Original experimental and theoretical work on concentration, polarisation/retardance, nanoparticle ordering and chromatic effects. It motivates but does not calibrate the particular screenshots.
- Emanuel H. Knill et al., *Bell Inequalities for Continuously Emitting Sources*, **Physical Review A** 91 (2015), via NIST `https://www.nist.gov/publications/bell-inequalities-continuously-emitting-sources`. Direct reference for timing/coincidence loopholes and Bell experiments. A photograph of spatial texture is not pairwise Bell data.
- Repository reuse: `DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda`, `DASHI/Physics/Textile/TextileBirefringenceRetardanceExact.agda`, `DASHI/Physics/Foundations/PhysicalTheoryExperimentDiscriminationExact.agda`, `DASHI/Programmes/QuantumCHSHDiscriminatorExact.agda`, `DASHI/Cognition/QuantumMindRetypingBoundary.agda`. The new results do not claim to replace or supersede these.

**Attribution rule:** provenance of a source, what that source claims, externally corroborated fact, the authority/validity of the claimed law, and the formal/kernel verification status are separate entries. Similar geometry, terminology, or measurements do not establish causality or priority of a new theory. Do not interpret the source authors as advocating the metaphysical hypotheses in the audit.

## Observable stack and limitations

`magnet configuration -> B and H -> nanoparticle distribution / order tensor Q -> spatial spectral Mueller/Jones response -> illumination and analyser -> camera intensity/RGB -> interpretation`

A quantum-material description may be needed to derive the effective magnetisation, susceptibility, anisotropy or optical dispersion. A **classical effective forward model** can nevertheless predict macroscopic field-alignment images. Neither the number of bright lobes nor the existence of magnetic nanoparticles identifies bipartite entanglement.

Use Maxwell magnetostatics (`div B=0`, `curl H=J_free`) with calibrated material laws, boundary conditions and magnet geometry. The real problem includes polydispersity, thermal relaxation, nanoparticle interactions, absorption, multiple scattering, field geometry, finite optical thickness, polariser leakage, illumination nonuniformity and camera pipeline. The current code omits these. The structural-colour and photonic-crystal interpretations in the research papers are source-reported claims, not verified characteristics of this particular video.

## Exact ideal polariser prediction and novel counterexample

For a radial linear director orientation `alpha(theta)=theta`, uniform crossed polarisers, and wavelength- and radius-dependent retardance `delta`, an ideal pixel intensity on one radius is

`I(theta,lambda,r)/I0 = sin²(2(theta-beta)) sin²(delta(lambda,r)/2)`.

Writing `A=sin²(delta/2)`:

`I(theta)=A/2 - (A/2)cos(4(theta-beta))`.

Thus the only nonzero angular Fourier orders of this **specific null model** are `m=0,+4,-4`; for `A=1` and the normalised DFT the magnitudes are `0.5, 0.25, 0.25`. Three-, six-, and ninefold coefficients vanish *under these assumptions*. Changing the analyser orientation by 45 degrees exchanges maxima and minima; rotating the ideal pattern by 90 degrees preserves it. Reversing a headless director by 180 degrees produces the same pattern, so there is no unique reconstruction of its vector polarity from that image. Formal finite-sector statements reside in `DASHI/Physics/Optics/FerrocellQuantumClaimDiscriminatorExact.agda`.

`python3 scripts/ferrocell_symmetry_audit.py --self-test` checks all listed identities at 72, 96 and 144 angular samples. `--json out.json` writes an auditable result. In that code adding only a conventional angular illumination factor `1+0.25*cos(6 theta)` produces a nonzero sixfold coefficient; an analogous factor at `3 theta` produces a threefold coefficient. This refutes inference from a 3/6 peak **alone** to exotic field structure. It does not establish which nuisance is present in any given Ferrocell image.

## Quantum-claim matrix (operational burdens)

| Candidate interpretation | What is supported | Additional signature needed / non-promotion |
| --- | --- | --- |
| Magnetic quantum origin | Material spin/exchange and magnetic anisotropy can require quantum microphysics | Does not imply mesoscopic coherent phase across the Ferrocell |
| Quantum superposition | Quantum states can superpose, but images can superpose classically as light fields/intensities | Controlled phase preparation, interference with coherence controls, nonclassical discriminator |
| Entanglement/nonlocality | Actual bipartite correlations can violate Bell bounds in controlled arrangements | Two parties, independent settings, correlated event outcomes, setting and coincidence audit, statistics; *not* an image pattern |
| Quantum observer effect | Measurement interactions matter | No human awareness required; camera observation is not wavefunction-consciousness causation |
| Zero-point/casimir energy | Vacuum fluctuations and Casimir phenomena are real in their appropriate models | Calibrated vacuum-sensitive observable, distinct vacuum/thermal/optical perturbation, quantitative field prediction |
| Quantum tunnelling | A microscopic process with known regimes | Barrier/transport model, controlled energy or distance dependence, nonclassical excess vs thermal alternatives |
| 5D/KK, quantum gravity | Internally consistent higher-dimensional and quantum-gravity candidates exist | Same-object physical compactification/coupling plus GR/QFT recovery and independent novel observable |
| Quantum consciousness | An unsettled set of physical proposals and analogies | Operational physical neural implementation, controls, causal effects and explicit bridge to consciousness |

**Not all quantum signatures are CHSH:** a Bell test is specifically for suitable bipartite nonlocal correlations. Single-photon antibunching `g²(0)<1`, sub-shot-noise fluctuations, contextuality protocols, phase-sensitive spectra, or state tomography may be better suited to other precise hypotheses, with classical confounds controlled. Observing diffraction or interference alone is not automatically a quantum violation: Maxwell optics also interferes.

## Sacred-geometry steelman and tests

- **Flower of Life:** compare a sixfold circle-packing generator to extracted circle radii, centres, intersections, and a goodness-of-fit against null illumination/optical projections. Nested circles alone do not imply regular hexagonal packing.
- **Toroidal topology:** a 2D picture of an annulus or nested rings is not proof of a 3D toroidal field or toroidal surface (`pi1(T²)=Z²`, Euler characteristic `0`). Require 3D vector mapping or reconstruction and a topological invariant with noise confidence bounds.
- **C3 / 3-6-9:** project to angular Fourier characters with predeclared rotational covariance and distinguish *field* symmetry from *instrument* symmetry. A broad classical model may contain 3, 6, 9 components; absence is specific to the radial crossed-polariser null.
- **Möbius/horocycles:** an optical correspondence to conformal inversion is a mathematical description of image formation, not evidence of a physical spacetime transformation.
- **5D consciousness/unity:** specify a state space, dynamics, measurable coupling and distinctive intervention outcome; a suggestive embedding is not a predictive mechanism.

## Two genuinely discriminating experiments

1. **Polariser intervention:** hold magnet, illumination geometry, camera and temperature fixed. Acquire full polarimetry across several analyser angles and wavelengths; test `m=4` phase shift and delta-dependent contrast. Include a no-ferrofluid control and independent magnetometry. Model choice uses held-out images, likelihood and calibration uncertainty, not pattern resemblance alone.
2. **Polarity intervention:** keep optics fixed and reverse magnet polarity. Under an **even-only director-retarder null**, the frame is unchanged. An odd response refutes that restricted null, but ordinary nonreciprocal magneto-optics or experimental artefacts may also cause odd responses. The Agda candidate-language theorem makes this ambiguity explicit: an odd-permitting classical candidate and an odd-permitting new-mechanism candidate remain equivalent under only this experiment.

Optional quantum-specific study must **define the observable first**. If the claim is Bell nonlocality, design a legitimate two-subsystem Bell protocol rather than treating spatial Fourier peaks as Bell statistics. Pre-register settings, exclusion rules, uncertainty, negative controls, and evidence/provenance; do not reclassify a magnetometer image as an entanglement witness.

## Next roadmap, ordered by marginal evidence gain

1. Obtain original video, optical schematic, magnet type/orientation, two polarisers and camera processing; classify frame artefacts and persistent optical features. `NO DATA` at this cut.
2. Collect polariser angle sweep + monochromatic image stack + Hall map. Fit Mueller parameters/retardance jointly and quantify identifiability; incorporate LED/camera spectral response.
3. Reconstruct field-to-order-to-optics with relaxation, scattering and nuisance geometry. Compare against at least two ordinary physical alternatives, and test holdouts.
4. Preregister the strongest concrete metaphysical/quantum hypothesis as a **distinct** prediction with calibrated measurement and numerical cutoff. Untestable interpretations remain interpretations, not physically refuted assertions.
5. Add a physical carrier / empirical evidence binding only when actual measurements arrive. Exact finite Agda proofs establish toy-model theorems, not experimental validity. Kernel check of the new module remains required on a machine with Agda and repo libraries installed.

## Reproducibility receipts

- **Local Python audit:** `python3 scripts/ferrocell_symmetry_audit.py --self-test --json out.json`; observed `m0=0.5`, `m4=0.25`, `m3=m6=m9=0` in the uniform ideal model, and `m6=0.0625` with only sixfold illumination modulation (similarly `m3=0.0625`). Symmetry errors are `~1e-15` floating point.
- **Agda source state:** exact definitions/proofs supplied, but **no Agda kernel compilation performed in this session**; do not label them kernel verified.
- **Video state:** screenshots are visual observations supplied by the user; actual Ferrocell identity and internal optical structure remain **unverified**.