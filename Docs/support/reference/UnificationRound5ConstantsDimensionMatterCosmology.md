# Unification Round Five: Constants, Dimension, Matter, and Cosmological Emergence

This tranche implements the five supplied updates as a finite exact Agda spine. The replacement A--P constants text supersedes the earlier Sections 46--76 wherever the two conflict.

The implementation reuses the repository's constants registry, candidate-functional boundary, resource-limited crystallisation, odd/even trit adapter, Grassmann candidate lane, dimension/signature interfaces, GR clarification index, gauge/QFT parity surfaces, Standard-Model conformance interfaces, and paper-facing unification boundary.

It does **not** promote a numerical constants theory, a proof that spacetime is four-dimensional, a first-principles periodic table, a calibrated nuclear model, a literal cosmological codec, continuum general relativity, the Standard Model, or terminal unification.

## Constants, scale, and parameter geometry

`ParameterScaleTaxonomyExact.agda` implements the five explanatory levels:

```text
structural invariants
dimensionless dynamical parameters
dimensionful scales
conversion constants
numerical representatives in chosen units
```

It links `DASHI.Constants.Registry.ConstantsRegistryLink` rather than duplicating SI or CODATA authority data. It separates law, vacuum, boundary, and calibration origins; proves a finite nonzero scale-orbit obstruction; records explicit, spontaneous, anomalous, boundary, finite-size, and calibration scale breaking; and keeps dimensional transmutation dependent on a reference/integration datum.

`ParameterInformationGeometryExact.agda` gives two parameter charts whose coordinate components and metric weights differ while the metric tangent norm remains exactly equal. It also gives one declared finite gradient-flow case in which a scalar objective is a Lyapunov function, without identifying every RG flow with MDL.

`ScaleInvariantTheorySelectionExact.agda` adds:

- a Buckingham-style dimension kernel using numerator/denominator exponent vectors;
- an exact witness that speed times time has length dimension;
- spontaneous scale breaking as vacuum selection on a degenerate scale orbit;
- triadic relative scales with an explicitly free base calibration;
- finite global MDL/Bayesian selection over a declared theory class;
- reference-machine additive code offsets;
- a joint RG/selection/exhaustion flow with a frozen non-equilibrium state.

## RG, viability, phase chambers, and crossings

`RGMDLExhaustionChambersExact.agda` keeps three processes as distinct types:

```text
CouplingPoint
ModelCandidate
ExhaustionState
```

It proves finite examples of:

```text
weak RG point -> fixed point
static viability != formation before exhaustion
full viability = static ∩ reachable ∩ robust
```

The module also implements phase chambers, the corrected nonempty bound-state condition, and the avoided-crossing discriminant

```text
(E_old - E_new)^2 + 4 |v|^2
```

with exact canonical values `0` and `16`.

## Dimension, signature, and Lorentz emergence

`DimensionPowerCountingBoundaryExact.agda` contains a concrete countermodel to the claim that local finiteness, Lorentz candidacy, and dimension-relative boundary scaling uniquely select `D=4`: two- and four-dimensional profiles share all three flags.

Dimension estimation is distinct from dimension selection. The existing `DimensionFixedPointAxioms` and `SignatureDerivationAxioms` are imported as conditional interfaces rather than independent completed derivations.

Interaction-specific marginal dimensions are checked:

```text
phi^4             -> D = 4
phi^3             -> D = 6
ordinary Yang-Mills -> D = 4
```

Four-volume is available only after a four-dimensional Lorentzian completion witness.

`DiscreteLorentzEmergenceBoundaryExact.agda` separates finite internal alphabets from spacetime discreteness. A regular-lattice finite model is direction-independent in its declared infrared sector and direction-dependent in its ultraviolet sector. The exact dispersion residual is `0` in the canonical infrared datum and `2` in the ultraviolet datum. This is a bounded emergence witness, not a Poincare-invariance theorem.

## Atomic construction

`AtomicFermionShellExact.agda` separates nuclear charge from electronic configuration. Given orbital representation data, it proves:

```text
subshell capacity(l) = 2(2l + 1)
shell capacity(n)    = 2n^2
```

with checked values `2`, `6`, `10`, `2`, `8`, and `18`. Fermionic occupancy carries an explicit `occupied <= capacity` proof. The corrected `Z=18` signature is encoded as

```text
[0,0,1,1,1,1,1,1].
```

A toy parameter change reverses the `3d`/`4s` order. A separate interaction term reverses the one-body configuration preference. Valence is an active-energy-window classification rather than maximal principal quantum number.

`AtomicValenceFermionBridgeExact.agda` cross-pollinates the existing Grassmann lane. It implements antisymmetric exchange, duplicate-state vanishing, and valence equivalence classes while explicitly refusing to promote the existing Grassmann receipt to a completed exterior algebra.

`AtomicGenerationPipelineExact.agda` records the actual dependency chain:

```text
nuclear charge
nuclear stability
one-particle representation
antisymmetric many-electron space
interacting energy
state selection
valence equivalence
observable prediction
```

A concrete argon-like finite pipeline is implemented. Candidate enumeration remains distinct from Hamiltonian solution and quantitative chemistry.

## Nuclear shells, pairing, response, and shape instability

`NuclearShellPairingExact.agda` treats proton and neutron closures separately. Magicity requires saturation **and** a large gap. Composition can change the effective gap.

Pairing requires an attractive channel. The blocked-sector counts are:

```text
even-even 0
odd-mass  1
odd-odd   2
```

Odd-even staggering and separation-energy curvature are exact finite differences. The odd/even-to-trit bridge is used only as an encoding adapter.

`NuclearResponseComplexityExact.agda` adds:

- a proton-neutron asymmetry numerator `(N-Z)^2`;
- finite response suppression as the shell gap grows;
- pair-locking reduction of active occupations only under a pairing model;
- a model-dependent shell/unpaired/shape/correlation complexity;
- a joint energy-complexity score with explicit weights.

`NuclearShapeInstabilityExact.agda` proves that the leading Fermi term is extensive at fixed density under equal splitting. The split candidate has a larger surface witness and a smaller electrostatic witness. The joint finite cost is `16` for the compact candidate and `12` for the split candidate.

This encodes fission as deformation-energy competition and barrier crossing, not relief of Pauli pressure. Fissility is represented by dimensionless `Z^2/A`-type data. A metastable state has positive local curvature, a lower-energy channel, and a barrier, so local and absolute stability remain separate.

## Causal coding and cosmological observation

`CausalCodingCosmologyBoundaryExact.agda` types every coding context from decoded history plus shared side information. An offline encoder may inspect the complete source while the decoder remains forward sequential. Global code admissibility does not create retrocausal signalling.

Bitstreams, initial states, boundary data, CMB observations, law syntax, and visible histories are distinct types. Two early states map to the same CMB observation.

`CMBInformationChannelExact.agda` strengthens this into a finite information channel. It proves an exact distinguishability contraction from `2` to `0` for one pair of early states. Coding factorisation and physical transition factorisation remain separate types, and deterministic decoding is not promoted to deterministic physics.

CABAC is bounded to adaptive entropy coding. Global rate-distortion or MDL search belongs to the surrounding encoder. The CMB is a projected checkpoint, not a lossless global bitstream or Cauchy surface.

## Geometry emergence

`KernelGeometryEmergenceObligations.agda` proves that scalar density underdetermines pressure, anisotropic stress, and momentum flux. It defines a ten-component symmetric four-dimensional tensor carrier and records the required continuum cutset:

- continuum manifold;
- Lorentzian metric;
- tensorial source;
- Bianchi identity;
- covariant conservation;
- diffeomorphism invariance;
- equivalence principle;
- geodesic limit;
- gravitational radiation;
- Einstein dynamics;
- controlled corrections.

`FiniteStressConservationGeodesicExact.agda` adds an exactly conserved cycle current, a geometry-dependent path selector, and a closed two-way matter/geometry update. These are finite analogues, not the covariant Bianchi identity, Lorentzian geodesic equation, equivalence principle, or semiclassical Einstein equation.

## QFT, gauge structure, particles, and emergence hypotheses

`FiniteGraphGaugeScalarExact.agda` constructs an exact local `Z2` graph gauge theory. It proves the group laws, local transformation of edge connection and scalar field, loop-holonomy invariance, and preservation of an edge covariant-mismatch observable.

`FiniteFockExcitationExact.agda` constructs truncated bosonic and fermionic occupation sectors, blocked fermion creation at unit occupancy, an exact `5^2 = 3^2 + 4^2` mass-shell datum, stable/metastable/transient excitation classes, and an isolated finite spectral-weight analogue.

`KernelQFTEmergenceObligations.agda` imports the repository's QFT parity, Lie/gauge, gauge-group, spin/Clifford, and Standard-Model conformance surfaces. It records the remaining cutset:

- Hilbert completion and operator domains;
- Lorentz-covariant field limit;
- Clifford spinors;
- local gauge redundancy and connection curvature;
- Fock construction;
- stable excitations and spectral poles;
- `SU(3) x SU(2) x U(1)` content;
- chiral matter representations;
- Higgs and Yukawa sectors;
- anomaly cancellation;
- reflection positivity;
- controlled continuum limit.

`KernelEmergenceHypothesesExact.agda` types the geometry and QFT bridges explicitly as conjectural hypotheses. Finite correction tables decrease from microscopic to macroscopic scales, but the module refuses to turn those tables into continuum suppression theorems.

## Unified effective action and root integration

`UnifiedEffectiveActionBoundary.agda` distinguishes UV/IR scale regimes from theory labels. Its target terms are:

```text
microscopic kernel
Einstein-Hilbert
Standard Model
higher corrections
backreaction
```

A recovery receipt requires separate geometry and quantum limits, a common coarse graining, closed backreaction, and controlled corrections. The paper-facing unification interface remains terminally false.

The tranche is assembled in:

```text
DASHI/Physics/Foundations/Everything.agda
DASHI/Physics/Foundations/Round5FullBoundary.agda
DASHI/Physics/Foundations/Round5Regression.agda
```

and wired through `DASHI/Unified/Everything.agda`, which is already imported by the repository root.

## Provenance

`Round5SourceAtlas.agda` records title, authors, venue, year, DOI, imported role, and excluded promotion for seventeen sources. The added provenance covers dimensional analysis, RG, information geometry, Kolmogorov complexity, causal sets, electronic structure, nuclear shells, pairing, fission, CABAC, gauge theory, Fock space, Euclidean reconstruction, electroweak theory, and CMB cosmology.

Repository-original finite lemmas are not assigned invented external identifiers.

## Validation

The focused command is:

```bash
bash scripts/check_unification_round5.sh
```

It runs the complete Round Four checker, scans every Round Five Agda module and the unified root for holes, postulates, unsafe options, unsolved metas, and placeholder right-hand sides, and invokes the pinned Agda 2.9 checker on:

```text
DASHI/Physics/Foundations/Round5Regression.agda
DASHI/Unified/Everything.agda
```

No successful kernel result is claimed until a workflow or local pinned-toolchain run is observed.