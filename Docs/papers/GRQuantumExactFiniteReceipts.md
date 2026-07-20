# Exact Finite GR / Quantum Receipts

This note records the concrete proposition-level tranche assembled by
`DASHI.Unified.GRQuantumProofAdapters`.

## Canonical compile surface

The namespace-safe import target is:

```text
DASHI.Unified.GRQuantumProofTermAtlas
```

It imports every new proof surface without flattening their namespaces.

## Exact receipts

### Multiscale reconstruction and energy

- `DASHI.Core.MultiscaleMDL.join-split` reconstructs every fine state from its
  coarse projection and residual.
- `DASHI.Core.FiniteQuadraticMultiscale` proves uniqueness of the energy table
  `(0,1,1,2)` under zero normalization, unit coarse/detail normalization, and
  orthogonal no-leakage.

### Chain and antichain geometry

- `DASHI.Geometry.FiniteCausalDiamond` gives one past event, three incomparable
  spatial events, and one future event.
- Chain depth and antichain width are invariant under cyclic spatial
  relabellings.
- `DASHI.Geometry.FiniteCausalDiamondMinimality` proves the represented
  separating antichain is unique with width three and every represented maximal
  past-to-future chain has depth two.

### Clifford and finite Spin cover

- `DASHI.Algebra.ConstructiveClifford` provides generated Clifford words,
  square/anticommutation congruence, the 16-blade basis, parity, reversion signs,
  Pin words, and even Spin words.
- `DASHI.Algebra.FiniteQuaternionDoubleCover` proves the nontrivial finite cover
  `Q8 -> V4`:
  - homomorphism;
  - surjectivity;
  - kernel exactly `{+1,-1}`;
  - two-element fibers for every rotation.
- `DASHI.Algebra.FiniteQuaternionGroupReceipts` adds exact unit, inverse,
  central-sign, and sign-forgetting quotient laws.

This is the finite 180-degree-rotation subgroup model of the Spin mechanism. It
is not the continuous `Spin(3) -> SO(3)` or `Spin(3,1) -> SO+(3,1)` theorem.

### Finite wave and probability lane

- `DASHI.Algebra.Quantum.FiniteTreeWeyl` proves the qutrit cyclic Weyl shift,
  `shift^3 = id`, project/refine asymmetry, one-hot normalization, and one-hot
  Born weights.
- `DASHI.Algebra.Quantum.FiniteQutritBornAdditivity` proves norm-squared
  additivity for superpositions of distinct qutrit basis amplitudes.

The continuum Heisenberg CCR still requires Hilbert completion, an operator
scaling family, convergence in a selected topology, central limiting
commutator, and identification of the action grain.

### Flat Einstein/source lane

`DASHI.Physics.Closure.PropositionEinsteinBridge` assembles existing exact
producers for:

- flat Lorentzian `1+3` signature;
- zero Cartesian Levi-Civita connection;
- symbolic Einstein-Hilbert leading basis and metric variation;
- zero Ricci and Einstein tensors;
- zero-source Bianchi/conservation;
- zero mass normalization;
- finite quantum/flat-GR joint inhabitation.

The general non-flat and nonzero-source theorem remains conditional on metric
selection, tensor convergence, Bianchi/Noether, universal coupling,
background independence, and spin-two bootstrap proofs.

### Constraint lane

`DASHI.Physics.Closure.PropositionConstraintAlgebra` states the three
hypersurface-deformation equations as equalities and separates them from
quantum representation/anomaly obligations. Its canonical inhabitant is the
exact trivial flat representation only.

### UV lane

- `DASHI.Physics.Closure.FiniteRegionalSpectrum` gives explicit finite
  enumerations for a nine-state regional basis and regulated Hamiltonian/metric
  spectra.
- `DASHI.Physics.Closure.FiniteRegionalSpectrumBoundary` proves that the
  regulated surface cannot inhabit `UVSpectralClosed` while physical
  low-energy matching remains empty.

### Executable diagnostic

```text
scripts/run_gr_quantum_finite_model_diagnostic.py
```

recomputes:

- bounded quadratic-table uniqueness;
- causal-diamond counts;
- all 64 `Q8` multiplication pairs against the `V4` quotient law;
- every two-element quotient fiber and the `{+1,-1}` kernel;
- the qutrit Weyl relation;
- regulated spectral dimensions.

The script writes JSON and Markdown receipts and explicitly sets terminal and
physical claims to false.

## Exact bundle

The inhabited aggregate is:

```agda
canonicalExactFiniteGRQuantumBundle : ExactFiniteGRQuantumBundle
```

It includes all receipts above plus the observer-conditioned multiscale wave
boundary and finite diagnostic governance receipt.

## Terminal boundary

The finite bundle is not convertible to:

```agda
TerminalGRQuantumProof
```

without explicit inhabitants for the continuum Clifford/Spin, CCR, Einstein,
constraint, UV/low-energy, common-substrate, and empirical correspondence
closures.

New code promoting the older Boolean facade should require:

```agda
HardenedTerminalUnificationWitness
```

which carries both the compatibility-era witness and the proposition-level
terminal proof.
