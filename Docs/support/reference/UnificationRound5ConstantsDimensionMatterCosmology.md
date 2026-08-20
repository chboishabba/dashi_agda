# Unification Round Five: Constants, Dimension, Matter, and Cosmological Emergence

This tranche is stacked directly on PR #399 (`agent/conscious-access-round5-dashi-yijing-moonshine`). The current PR #399 head has been merged into the feature branch, so the implementation extends its latest completion surface rather than an earlier snapshot or a competing Round Five.
The replacement A--P constants text supersedes the earlier Sections 46--76 wherever the two conflict. The implementation reuses the repository's constants registry, candidate-functional boundary, resource-limited crystallisation, Grassmann and odd/even trit lanes, existing p-adic chart/residual/collapse modules, PR #399 hyperfabric/coarse-graining/spectral/NS--YM/SSP/moonshine modules, dimension/signature interfaces, GR clarification index, gauge/QFT parity surfaces, Standard-Model conformance interfaces, and paper-facing unification boundary.
It does **not** promote a numerical constants theory, a proof that spacetime is four-dimensional, a first-principles periodic table, a calibrated nuclear model, a literal cosmological codec, continuum general relativity, the Standard Model, a Monster representation, either Clay problem, or terminal unification.
## Constants, scale, and parameter geometry
`ParameterScaleTaxonomyExact.agda` implements five levels:
```text
structural invariants
dimensionless dynamical parameters
dimensionful scales
conversion constants
numerical representatives in chosen units
```
It links `DASHI.Constants.Registry.ConstantsRegistryLink`, separates law/vacuum/boundary/calibration origins, proves a finite nonzero scale-orbit obstruction, records explicit/spontaneous/anomalous/boundary/finite-size/calibration scale breaking, and keeps dimensional transmutation dependent on a reference datum.
`ParameterInformationGeometryExact.agda` gives two coordinate charts with different components and metric weights but equal tangent norm. It also gives one declared finite gradient-flow/Lyapunov example without identifying every RG flow with MDL.
`ScaleInvariantTheorySelectionExact.agda` adds a Buckingham-style dimension kernel, exact dimensional cancellation, spontaneous vacuum selection, triadic relative scales with a free base calibration, finite global MDL/Bayesian selection over a declared theory class, reference-machine offsets, and a joint RG/selection/exhaustion flow. It imports PR #399's `CarrierScale` surface rather than inventing a second hyperfabric scale type.
`RGMDLExhaustionChambersExact.agda` separates RG flow, model selection, and resource exhaustion. It intersects static viability, reachability before freeze-out, and robustness; implements qualitative phase chambers; corrects the bound-state condition to a discrete level below continuum; and checks
gap² = (E_old - E_new)² + 4 |v|².
## Causal p-adic charts and exact residual recovery
`PadicCausalChartLosslessExact.agda` implements the mathematical content of the p-adic hierarchy while deliberately excluding AV1, container, and engineering-performance claims.
It reuses:
DASHI/Biology/TriadicKernelLiftQuotientExact.agda
DASHI/Biology/TriadicCarryResidualExact.agda
DASHI/Biology/CausalHierarchicalChartResidualExact.agda
DASHI/Biology/FinitePadicCollapseExact.agda
The finite residual chart is the exact `Z/3Z` analogue
r = x - x_hat
decode(x_hat,r) = x_hat + r,
and proves the round trip for every predictor/target pair. The theorem is lifted componentwise to a sheet residual and packaged as a causal residual packet whose predictor is supplied independently of the current target.
The module also proves the existing support/orientation fold/unfold round trip, defines nested depth-one/depth-two/depth-three cylinders, reuses the existing chart-objective minimiser, and imports the surviving coarse residual from the finite collapse lane.
Losslessness remains separate from rate optimality: `decode (encode x) = x` does not by itself prove probability-model adequacy, side-information optimality, or minimal expected code length. The existing eight-source p-adic atlas is reused rather than copied.
## Modular projection and coarse quantisation
`ModularProjectionQuantisationExact.agda` formalises the mathematical content visible in the two attached projection comparisons without treating rendered images as proofs.
A four-dimensional witness pair has identical axis-aligned projection but different angled projection. Thus the angled chart retains one distinction lost by that axis chart, and a declared finite witness objective selects the angled candidate for that witness set.
Coarse quantisation is separately proved non-injective: two distinct fine coordinates map to one coarse coordinate. A triadic angled projection uses the existing exact cyclic addition on `Z/3Z`, rather than identifying modular and Euclidean arithmetic.
The authority boundary blocks:
one visual comparison -> global optimum
4D-to-2D angled map -> injectivity
coarse integer search -> preservation of every fine distinction
modular residue chart -> ordinary Euclidean projection.
## Dimension and Lorentz emergence
`DimensionPowerCountingBoundaryExact.agda` contains a concrete countermodel to the claim that local finiteness, Lorentz candidacy, and dimension-relative boundary scaling uniquely select `D=4`: two- and four-dimensional profiles share those premises.
It keeps estimation distinct from selection, makes four-volume conditional on a four-dimensional Lorentzian completion, and checks interaction-specific marginal dimensions:
phi^4                -> D = 4
phi^3                -> D = 6
ordinary Yang-Mills  -> D = 4
`DiscreteLorentzEmergenceBoundaryExact.agda` separates a finite internal alphabet from spacetime discreteness. A regular-lattice toy model is direction-independent in its declared infrared sector and direction-dependent in its ultraviolet sector. Its exact dispersion residual is `0` in the infrared datum and `2` in the ultraviolet datum; this is not a Poincare-invariance theorem.
## Atomic construction
`AtomicFermionShellExact.agda` separates nuclear charge from electronic configuration and proves, after supplying the rotational/spin representation,
subshell capacity(l) = 2(2l + 1)
shell capacity(n)    = 2n^2.
It checks the standard finite capacities, explicit fermionic occupancy bounds, the corrected `Z=18` signature `[0,0,1,1,1,1,1,1]`, a parameter-dependent `3d`/`4s` order reversal, interaction-dependent configuration selection, and energy-window valence.
`AtomicValenceFermionBridgeExact.agda` cross-pollinates the existing Grassmann lane with antisymmetric exchange, duplicate-state vanishing, and valence equivalence classes while refusing to promote the existing Grassmann receipt to a completed exterior algebra.
`AtomicGenerationPipelineExact.agda` records the dependency chain
nuclear charge
nuclear stability
one-particle representation
antisymmetric many-electron space
interacting energy
state selection
valence equivalence
observable prediction.
A concrete argon-like finite pipeline is checked. Enumeration remains distinct from Hamiltonian solution and quantitative chemistry.
## Nuclear structure
`NuclearShellPairingExact.agda` treats proton and neutron closures separately. Magicity requires saturation plus a large gap. Pairing requires an attractive channel. Blocked-sector counts are exactly `0/1/1/2` for even-even, the two odd-mass sectors, and odd-odd.
`NuclearResponseComplexityExact.agda` adds `(N-Z)^2` asymmetry data, gap-suppressed finite response, pair-locking under an explicit pairing model, a shell/unpaired/shape/correlation complexity profile, and an explicitly weighted energy-complexity score.
`NuclearShapeInstabilityExact.agda` proves the leading finite-density Fermi term is extensive under equal splitting. The split candidate has larger surface and smaller electrostatic witnesses; the joint finite costs are `16` for the compact candidate and `12` for the split candidate. This encodes deformation-energy competition and barrier crossing, not relief of Pauli pressure.
## Causal coding and CMB observation
`CausalCodingCosmologyBoundaryExact.agda` types context from decoded history plus shared side information. Offline source search is compatible with forward decoding; global admissibility does not imply retrocausal signalling.
Bitstreams, physical initial states, boundary data, law syntax, CMB observations, and visible histories are distinct types. Two distinct early states map to the same observation.
`CMBInformationChannelExact.agda` strengthens this into a finite information channel and checks a distinguishability contraction from `2` to `0`. Coding factorisation and physical transition factorisation remain distinct, and deterministic decoding does not determine the ontology of physical law.
## Geometry and QFT emergence
`KernelGeometryEmergenceObligations.agda` proves scalar density underdetermines pressure, anisotropic stress, and momentum flux. It constructs a ten-component symmetric tensor carrier and records the manifold/metric/tensor/Bianchi/conservation/diffeomorphism/equivalence/geodesic/radiation/Einstein/correction cutset.
`FiniteStressConservationGeodesicExact.agda` adds an exactly conserved cycle current, geometry-dependent path selection, and a closed finite backreaction step, while refusing promotion to continuum GR.
`FiniteGraphGaugeScalarExact.agda` constructs an exact local `Z2` graph gauge model with group laws, transformed connection and field, loop-holonomy invariance, and preservation of a covariant mismatch observable.
`FiniteFockExcitationExact.agda` constructs truncated bosonic and fermionic occupation sectors, blocked one-mode fermion creation, an exact `5^2 = 3^2 + 4^2` mass-shell datum, stable/metastable/transient excitation classes, and an isolated finite spectral-weight analogue.
`KernelQFTEmergenceObligations.agda` directly imports PR #399's classical quantum-like coarse-graining, spectral-grokking, and finite NS--YM gauge-gap surfaces. It also imports the repository's QFT parity, Lie/gauge, gauge-group, spin/Clifford, and Standard-Model conformance interfaces. The remaining cutset includes Hilbert completion, Lorentz covariance, spinors, local gauge connection, Fock construction, stable particles, spectral poles, exact Standard-Model representations, Higgs/Yukawa data, anomaly cancellation, reflection positivity, and a controlled continuum limit.
`KernelEmergenceHypothesesExact.agda` types the geometry and QFT bridges explicitly as conjectural hypotheses. Finite correction tables decrease from microscopic to macroscopic scales, but are not promoted to continuum suppression theorems.
## Latest PR #399 completion cross-pollination
`PR399FoundationsCrossPollinationExact.agda` imports both PR #399's original Round Five boundary and its completion boundary. It checks:
3^9 = 19683
siteCount(sheetThreeByNine) = 27 = scaleAtDepth(1,depth0)
siteCount(sheetThreeByThree) = 9 = scaleAtDepth(1,depth1)
54 = 1 + 53
196884 = 10 * 3^9 + 54
196883 = 10 * 3^9 + 53
47 * 59 * 71 = 196883
complete SSP/Ogg lane count = 15
geometric 54-1 presentation is minimal in the declared finite family
spectral cleanup component count = 3
finite NS--YM gap = 1
Born-rule derivation remains false.
These are exact finite arithmetic and minimisation statements. They do not construct a Monster representation, prove irreducibility of the 53-carrier, turn an Ogg-prime product into a group action, or promote the finite gauge gap to the Yang--Mills Clay mass gap.
`Round5CompletionRegression.agda` independently regresses the `54/53`, `196884/196883`, Ogg-prime product, SSP-lane count, canonical 53-presentation minimality, completion boundary, and completion source count.
## Combined Round Five root
`Round5FullBoundary.agda` contains:
DASHI.Biology.ConsciousAccessRound5FullBoundary
DASHI.Biology.ConsciousAccessRound5CompletionBoundary
DASHI.Physics.Foundations.Round5FullBoundary
The cumulative surface therefore carries PR #399's ternary/Yijing, braid, hyperfabric, Monster/FRACTRAN/SSP candidate arithmetic, natural-system, neural, and finite NS--YM results together with the p-adic, projection, constants, dimension, atomic, nuclear, cosmology, and GR--QFT tranche.
The feature branch was explicitly synchronized with the current PR #399 head before final validation. The unified roots are:
DASHI/Physics/Foundations/Everything.agda
DASHI/Physics/Foundations/Round5Regression.agda
DASHI/Physics/Foundations/Round5CompletionRegression.agda
DASHI/Unified/Everything.agda.
## Provenance
`Round5SourceAtlas.agda` records authors, full titles, venues, years, DOIs, imported roles, and excluded promotions for seventeen additional sources covering dimensional analysis, RG, information geometry, Kolmogorov complexity, causal sets, electronic structure, nuclear shells, pairing, fission, CABAC, Yang--Mills, Fock space, Osterwalder--Schrader reconstruction, electroweak theory, and Planck cosmology.
`Round5CombinedSourceBoundary.agda` checks four source populations without copying them:
17  new physics/foundations records
23  PR #399 extended records
29  PR #399 completion records
 8  reused Round Four p-adic records.
The PR #399 completion atlas includes title/author/venue/year/DOI or explicit no-DOI/ISBN markers for the added moonshine, exceptional-lattice, SSP, and analytic sources. Repository-original finite lemmas are not assigned invented identifiers.
## Validation
The focused command is:
```bash
bash scripts/check_unification_round5.sh
It first runs `scripts/check_conscious_access_round5.sh`, then rejects missing files, holes, postulates, unsafe options, unsolved metas, and placeholder right-hand sides in every added module. It invokes the repository-flake Agda 2.9 checker on:
The workflow resolves `.#agda-with-dashi-deps` from the repository lock file. A kernel pass is not claimed until an actual workflow or equivalent pinned-toolchain run has completed successfully.
This tranche implements the five supplied updates as a finite exact Agda spine. The replacement A--P constants text supersedes the earlier Sections 46--76 wherever the two conflict.
The implementation reuses the repository's constants registry, candidate-functional boundary, resource-limited crystallisation, odd/even trit adapter, Grassmann candidate lane, dimension/signature interfaces, GR clarification index, gauge/QFT parity surfaces, Standard-Model conformance interfaces, and paper-facing unification boundary.
It does **not** promote a numerical constants theory, a proof that spacetime is four-dimensional, a first-principles periodic table, a calibrated nuclear model, a literal cosmological codec, continuum general relativity, the Standard Model, or terminal unification.
`ParameterScaleTaxonomyExact.agda` implements the five explanatory levels:
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
CouplingPoint
ModelCandidate
ExhaustionState
It proves finite examples of:
weak RG point -> fixed point
static viability != formation before exhaustion
full viability = static ∩ reachable ∩ robust
The module also implements phase chambers, the corrected nonempty bound-state condition, and the avoided-crossing discriminant
(E_old - E_new)^2 + 4 |v|^2
with exact canonical values `0` and `16`.
## Dimension, signature, and Lorentz emergence
`DimensionPowerCountingBoundaryExact.agda` contains a concrete countermodel to the claim that local finiteness, Lorentz candidacy, and dimension-relative boundary scaling uniquely select `D=4`: two- and four-dimensional profiles share all three flags.
Dimension estimation is distinct from dimension selection. The existing `DimensionFixedPointAxioms` and `SignatureDerivationAxioms` are imported as conditional interfaces rather than independent completed derivations.
Interaction-specific marginal dimensions are checked:
phi^4             -> D = 4
phi^3             -> D = 6
ordinary Yang-Mills -> D = 4
Four-volume is available only after a four-dimensional Lorentzian completion witness.
`DiscreteLorentzEmergenceBoundaryExact.agda` separates finite internal alphabets from spacetime discreteness. A regular-lattice finite model is direction-independent in its declared infrared sector and direction-dependent in its ultraviolet sector. The exact dispersion residual is `0` in the canonical infrared datum and `2` in the ultraviolet datum. This is a bounded emergence witness, not a Poincare-invariance theorem.
`AtomicFermionShellExact.agda` separates nuclear charge from electronic configuration. Given orbital representation data, it proves:
shell capacity(n)    = 2n^2
with checked values `2`, `6`, `10`, `2`, `8`, and `18`. Fermionic occupancy carries an explicit `occupied <= capacity` proof. The corrected `Z=18` signature is encoded as
[0,0,1,1,1,1,1,1].
A toy parameter change reverses the `3d`/`4s` order. A separate interaction term reverses the one-body configuration preference. Valence is an active-energy-window classification rather than maximal principal quantum number.
`AtomicValenceFermionBridgeExact.agda` cross-pollinates the existing Grassmann lane. It implements antisymmetric exchange, duplicate-state vanishing, and valence equivalence classes while explicitly refusing to promote the existing Grassmann receipt to a completed exterior algebra.
`AtomicGenerationPipelineExact.agda` records the actual dependency chain:
observable prediction
A concrete argon-like finite pipeline is implemented. Candidate enumeration remains distinct from Hamiltonian solution and quantitative chemistry.
## Nuclear shells, pairing, response, and shape instability
`NuclearShellPairingExact.agda` treats proton and neutron closures separately. Magicity requires saturation **and** a large gap. Composition can change the effective gap.
Pairing requires an attractive channel. The blocked-sector counts are:
even-even 0
odd-mass  1
odd-odd   2
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
microscopic kernel
Einstein-Hilbert
Standard Model
higher corrections
backreaction
A recovery receipt requires separate geometry and quantum limits, a common coarse graining, closed backreaction, and controlled corrections. The paper-facing unification interface remains terminally false.
The tranche is assembled in:
DASHI/Physics/Foundations/Round5FullBoundary.agda
and wired through `DASHI/Unified/Everything.agda`, which is already imported by the repository root.
`Round5SourceAtlas.agda` records title, authors, venue, year, DOI, imported role, and excluded promotion for seventeen sources. The added provenance covers dimensional analysis, RG, information geometry, Kolmogorov complexity, causal sets, electronic structure, nuclear shells, pairing, fission, CABAC, gauge theory, Fock space, Euclidean reconstruction, electroweak theory, and CMB cosmology.
Repository-original finite lemmas are not assigned invented external identifiers.
It runs the complete Round Four checker, scans every Round Five Agda module and the unified root for holes, postulates, unsafe options, unsolved metas, and placeholder right-hand sides, and invokes the pinned Agda 2.9 checker on:
DASHI/Unified/Everything.agda
No successful kernel result is claimed until a workflow or local pinned-toolchain run is observed.
