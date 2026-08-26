# Conscious Access Round 7: Aristotle Return

This stacked tranche returns theorem surfaces from the supplied Aristotle archive to the Agda conscious-access stack.

The guiding rule is structural admission rather than analogy:

```text
shared vocabulary      is not a bridge
shared cardinality     is not a map
a map                  is not necessarily informative
an objective           is not automatically a Hamiltonian
phase labels           are not a continuous amplitude
```

## Imported Aristotle owners

The exact archive paths are recorded in `ConsciousAccessRound7AristotleSourceBridge.agda`:

- `Lean/Integration/TernaryHub.lean`
- `Lean/Spine/TernaryPhase.lean`
- `Lean/Spine/TritCarrier.lean`
- `Lean/Spine/Observer.lean`
- `Lean/Spine/OggGrid.lean`
- `Lean/Spine/Duality.lean`

The Agda modules explicitly distinguish full theorem ports from finite shadows when the Aristotle theorem depends on real/complex linear algebra not reconstructed here.

## Canonical ternary orientation

`TernaryCanonicalOrientationExact.agda` makes sign convention explicit. Canonical and reversed orientations both fix the neutral state and commute with ternary negation.

Thus downstream motif encodings can be orientation-covariant rather than treating one sign convention as intrinsic physics.

## Fixed/transverse C3 shadow

`TernaryFixedTransverseFiniteExact.agda` separates a common-amplitude coordinate from relational C3 phase directions. The common coordinate is invariant under phase shift while the three distinguished transverse phase directions carry an exact order-three action.

This is a finite shadow of Aristotle's stronger real theorem that the regular C3 carrier splits into one fixed dimension plus a two-dimensional mean-zero transverse sector.

## Rotation versus reflection

`TernaryRotationReflectionSeparationExact.agda` proves:

```text
rotation^3 = identity
reflection^2 = identity
reflection(rotation(t)) = rotation^2(reflection(t))
```

and proves rotation and reflection differ at the neutral trit.

This blocks the Yijing/moving-line lane from collapsing cyclic advancement, complement, and polarity inversion into one generic change operator.

## Observer admission

`NondegenerateObserverAdmissionExact.agda` defines a finite three-channel observer code. Constant channels have zero variation and therefore zero observed-area code. A canonical non-flat channel has positive code `12`.

The theorem surface encodes the Aristotle rule that the existence of a map is insufficient: inherited observer conclusions require nondegenerate information.

`NeuralFixedTransverseObserverBridgeExact.agda` then shows that the existing two neural microstates can share:

- the same coarse fMRI-like observation;
- the same total activation mass;
- the same cyclic norm-like variation;

while retaining different order-sensitive Laplacian variation and distinct relational C3 phase labels.

Thus even multiple coarse invariants need not identify ordered microscopic state.

## Phase versus amplitude

`CyclotomicPhaseAmplitudeBoundaryExact.agda` carries an exact three-phase cycle and conjugation involution. All three unit phases have the same norm code, so norm alone does not identify phase.

Amplitude is a separate coordinate. The module proves both:

```text
same phase + different amplitude
different phase + same amplitude
```

preventing a three-state phase carrier from being promoted to a continuous quantitative field by vocabulary alone.

## Equal cardinality is not an equivariant map

`EqualCardinalityStructureBoundaryExact.agda` proves a genuine obstruction on equal three-element carriers. A free order-three rotation cannot be equivariantly bijected to a reflection action with a fixed point.

The obstruction is orbit structure, not cardinality.

## Ogg-style no-go

`OggTernaryEquivariantLabellingNoGoExact.agda` extracts the mechanism of Aristotle's concrete Ogg theorem.

The internal carrier has cardinality code:

```text
5 * 3 = 15
```

matching the existing fifteen Ogg-prime list. But for any target observer carrying a unique ramified point, every class-preserving action fixes that point. Therefore no bijection can intertwine it with the free ternary shift on the internal `5 x 3` carrier.

This strengthens the existing Monster/moonshine boundary from "arithmetic is not yet an action" to an actual reusable equivariance obstruction.

## Operator admission

`OperatorStructureAdmissionBoundaryExact.agda` imports the admission consequence of Aristotle's odd-dimensional symplectic no-go. A Hamiltonian promotion must carry an explicit phase-space admission certificate; an objective value alone is insufficient.

The full real theorem that every odd-dimensional alternating form is degenerate remains owned by the Aristotle Lean archive and is not falsely reproved by the finite Agda parity gate.

## Provenance

The source bridge reuses four external records already present in DASHI:

- Jean-Pierre Serre, *A Course in Arithmetic*, DOI `10.1007/978-1-4684-9884-4`;
- Fan R. K. Chung, *Spectral Graph Theory*, DOI `10.1090/cbms/092`;
- Andrés J. Aricheta, *Supersingular Elliptic Curves and Moonshine*, DOI `10.3842/SIGMA.2019.007`;
- Emil Artin, *Theory of Braids*, DOI `10.2307/1969218`.

Internal Aristotle archive provenance is recorded by exact file path rather than invented bibliographic identifiers.

## Validation root

```text
DASHI/Biology/ConsciousAccessRound7AristotleRegression.agda
```

The focused checker cascades through Round 6, scans the new modules for holes/postulates/unsafe options/placeholders, then invokes the pinned Agda 2.9 runner on the Round 7 regression and `DASHI/Biology/Everything.agda`.
