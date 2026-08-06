# Unification Round Five: Constants, Dimension, Matter, and Cosmological Emergence

This tranche integrates the five supplied mathematical updates as a finite exact Agda spine.  It reuses the repository's constants registry, candidate-functional boundary, resource-limited crystallisation, odd/even trit adapter, dimension/signature axiom surfaces, gauge/QFT parity interfaces, GR clarification index, and paper-facing unification boundary.

The implementation does not promote a numerical constants theory, a proof that spacetime is four-dimensional, a first-principles periodic table, a quantitative nuclear model, a literal cosmological codec, continuum general relativity, the Standard Model, or terminal unification.

## Replacement rule for the constants material

The supplied replacement A--P supersedes the older Sections 46--76 where the two conflict.  The retained structure is implemented in:

- `ParameterScaleTaxonomyExact.agda`;
- `RGMDLExhaustionChambersExact.agda`;
- `DimensionPowerCountingBoundaryExact.agda`.

The five explanatory levels are:

1. exact structural invariants;
2. dimensionless dynamical parameters;
3. dimensionful scales;
4. conversion constants;
5. numerical representatives in chosen units.

The module links to `DASHI.Constants.Registry` instead of duplicating SI/CODATA authority data.

### Scale-selection obstruction

The finite theorem surface contains a nontrivial scale orbit

```text
unit representative    -> 1
doubled representative -> 2
```

and proves that identifying the two values is impossible.  This is the finite exact analogue of

```text
Q[D_s Phi] = s^Delta Q[Phi]
```

with nonzero weight: an exactly scale-equivariant selection rule cannot choose one unique finite nonzero representative without explicit breaking, spontaneous breaking, anomaly, boundary data, finite size, or calibration.

### Dimensional transmutation boundary

A generated scale is represented as a function of a dimensionless running datum and a reference scale.  Two exact examples yield `6` and `9`.  The point is not the physical formula; it is the dependency theorem: scale generation still retains an integration/reference datum.

### Reparametrisation and identifiability

Two distinct theory coordinates map to one observable class and therefore receive one invariant score.  Coordinate norms are not treated as physical objectives.  The finite quotient models the required descent of a selection functional to observational equivalence classes.

### Universal ratios and precision

The equality of `2/4` and `3/6` is proved by cross multiplication.  Continuous-value description length is indexed by requested precision rather than assigning a finite exact code to an arbitrary real number.

### RG, MDL, and exhaustion

The three processes are different Agda carriers:

```text
CouplingPoint
ModelCandidate
ExhaustionState
```

The finite RG trajectory reaches a fixed point whose location is not moved by the weak initial datum.  The MDL selector minimises a separate finite code length.  Exhaustion can freeze a trajectory before order is reached.

Static viability, reachability before exhaustion, and robustness are intersected.  One parameter is statically stable but dynamically unavailable, so stability is not promoted to physical formation.

### Phase chambers and spectral viability

Three parameter chambers are represented explicitly.  Crossing the chamber boundary changes the qualitative phase label.

A bound state requires a certified discrete level below the continuum threshold.  The corrected nonempty-intersection convention is encoded by `discreteBelowContinuum`.

The exact avoided-crossing discriminant is represented by

```text
gapSquare(Eold,Enew,v)
  = |Eold-Enew|^2 + 4 v^2.
```

At exact degeneracy it gives `0` when `v=0` and `16` when `v=2`.

## Dimension and four-volume

`DimensionPowerCountingBoundaryExact.agda` implements Sections 77--88.

Two causal profiles in dimensions two and four have the same qualitative local-finiteness, Lorentz-candidate, and dimension-relative boundary-scaling flags.  This is an exact countermodel to the implication that those premises alone determine dimension four.

Dimension estimation is kept separate from uniqueness.  The existing `DimensionFixedPointAxioms` is imported and classified as a conditional axiom surface: its `StabilityUnderDecimation` field assumes the four-dimensional conclusion rather than independently deriving it.

Power counting is interaction-specific:

```text
phi^4 marginal dimension = 4
phi^3 marginal dimension = 6
ordinary Yang--Mills marginal dimension = 4
```

This records the genuine special role of four dimensions for ordinary Yang--Mills while blocking the stronger claim that all interacting field theories outside four dimensions fail.

Four-volume appears only after a four-dimensional Lorentzian completion witness.  The implementation order is:

```text
establish/select dimension and signature
then select the matching invariant volume kind.
```

## Atomic construction

`AtomicFermionShellExact.agda` implements Sections 89--111.

Element identity is carried by proton number.  Electronic configuration is a separate state.  The orbital labels are declared representation input rather than outputs of triadic cardinality.

Once the rotational and spin representation is assumed, the exact capacities are:

```text
subshell capacity(l) = 2(2l+1)
shell capacity(n)    = 2n^2
```

with checked values `2`, `6`, `10`, `2`, `8`, and `18` for the standard finite examples.

Fermionic occupancy carries an explicit `occupied <= capacity` proof.  The corrected `Z=18` signature is encoded exactly as

```text
[0,0,1,1,1,1,1,1].
```

A two-regime toy orbital functional exhibits an exact level-order reversal between `3d` and `4s`.  It remains a candidate score, not an MDL or physical Hamiltonian theorem.

A separate interaction penalty reverses the preference of the one-body score.  This demonstrates why actual electronic order depends on configuration interaction.  Valence is classified by an active energy window rather than by maximal principal quantum number alone.

## Nuclear shell closure and pairing

`NuclearShellPairingExact.agda` implements Sections 112--123 and 138--146.

Proton and neutron sectors are distinct.  A magic closure requires both saturation and a large gap.  A doubly closed witness contains separate proton and neutron proofs.

Composition-dependent gap labels provide the finite exact shell-evolution chain:

```text
composition change
-> effective field change
-> gap change
-> closure status change.
```

Pairing is unavailable without an attractive pairing interaction.  The four proton/neutron parity sectors have blocked-sector counts

```text
even-even 0
odd-even  1
even-odd  1
odd-odd   2.
```

Odd-even staggering and separation-energy curvature are represented by exact finite differences.  The odd/even-to-trit module is imported only as an encoding adapter: binary parity is not identified with intrinsic ternary cardinality.

## Finite-density nuclear instability

`NuclearShapeInstabilityExact.agda` implements Sections 124--137 and 143--149.

The leading Fermi term is extensive at fixed density:

```text
E_F(8) = E_F(4) + E_F(4).
```

The split finite drop has a larger surface witness and a smaller electrostatic witness.  A joint shape cost includes surface, electrostatic, asymmetry, shell, and pairing terms.  In the canonical candidate the split cost is `12` and the compact cost is `16`.

This encodes the corrected mechanism: fission is shape-energy competition or barrier crossing, not automatic relief of Pauli pressure.

Fissility is represented by numerator/denominator/rank data corresponding to the unit-free control ratio proportional to `Z^2/A`.  Numerical thresholds remain coefficient-dependent.

A metastable state has positive local curvature, a lower-energy channel, and a barrier.  Local stability is therefore not absolute stability and energetic possibility is not a decay-rate theorem.

## Causal coding and cosmological observation

`CausalCodingCosmologyBoundaryExact.agda` implements Sections 150--158, 179--182, and 189.

The context function consumes only decoded history plus shared side information.  An offline encoder may inspect the complete source, while the decoder remains forward sequential.

A globally admissible complete code maps to `forwardInfluenceOnly`; no retrocausal signalling is inferred.

The following are distinct types:

```text
BitPair
PhysicalInitialState
BoundaryData
CMBObservation
LawSyntax
VisibleHistory.
```

Two distinct early states produce the same CMB observation.  This proves a concrete many-to-one observational projection.  The CMB is therefore represented as a noisy/projected checkpoint, not a lossless bitstream or global Cauchy surface.

CABAC is bounded to adaptive entropy coding.  Global rate-distortion or MDL search belongs to the larger encoder and is not an intrinsic CABAC theorem.

## Geometry emergence obligations

`KernelGeometryEmergenceObligations.agda` implements Sections 159--163, 175--177, 183, 185--188.

Two stress profiles have the same energy density but different pressure, anisotropic stress, and momentum flux.  This proves that scalar kernel load underdetermines a relativistic source tensor.

The symmetric four-dimensional tensor carrier has ten named components.  The required emergence cutset includes:

- continuum manifold construction;
- Lorentzian metric construction;
- tensorial stress-information source;
- Bianchi identity;
- covariant conservation;
- diffeomorphism invariance;
- equivalence principle;
- geodesic limit;
- gravitational radiation;
- Einstein dynamics;
- controlled higher-order corrections.

The existing signature axioms and GR clarification index are imported.  They remain bounded interfaces, not a promotion of non-flat continuum GR.

## Quantum-field and Standard-Model emergence obligations

`KernelQFTEmergenceObligations.agda` implements Sections 164--174 and 178, 184--188.

Global finite orbit classes and local gauge classes are separate types.  A finite three-edge graph has a nontrivial loop holonomy, giving a concrete curvature witness without promoting continuum Yang--Mills theory.

The imported repository surfaces include:

- QFT parity and analytic-authority cutsets;
- Lie/gauge theory parity;
- gauge-group contract;
- spin-emergence/Clifford interface;
- Standard-Model conformance vectors.

The new cutset records Hilbert completion, Lorentz scalar limit, Clifford spinors, local gauge redundancy, connection/curvature, Fock construction, stable excitations, correlation poles, the exact Standard-Model gauge group, chiral representations, Higgs/Yukawa sectors, anomaly cancellation, reflection positivity, and a controlled continuum limit.

## Unified effective action and backreaction

`UnifiedEffectiveActionBoundary.agda` keeps UV/IR scale regimes distinct from theory labels.  Geometry, quantum matter, and backreaction can all occur in each regime.

The target effective action contains:

```text
microscopic kernel term
Einstein-Hilbert target term
Standard-Model target term
higher corrections
backreaction term.
```

A recovery receipt requires separate geometry and quantum limits, a common coarse-graining map, consistent backreaction, and controlled corrections.

A finite joint dynamics demonstrates two-way state dependence: excited matter can move a flat geometry candidate to a curved candidate, while a vacuum state can relax it.  This is a typed backreaction model only.

The paper-facing unification theorem interface is imported and its terminal promotion remains false.  Kernel depth is not identified with the Planck length without a calibrated dimensionless map.

## Provenance

`Round5SourceAtlas.agda` records title, authors, venue, year, DOI, imported role, and excluded promotion for fourteen sources covering dimensional analysis, RG, information geometry, causal sets, electronic structure, nuclear shells, fission, CABAC, gauge theory, Euclidean reconstruction, electroweak theory, and CMB cosmology.

Repository-original finite lemmas are not assigned invented external identifiers.

## Validation

The cumulative root is:

```text
DASHI/Physics/Foundations/Round5Regression.agda
```

The focused command is:

```bash
bash scripts/check_unification_round5.sh
```

It first runs the complete Round Four checker, scans every Round Five Agda module for holes, postulates, unsafe options, unsolved metas, and placeholder right-hand sides, and then invokes the pinned Agda 2.9 checker on the cumulative regression root.
