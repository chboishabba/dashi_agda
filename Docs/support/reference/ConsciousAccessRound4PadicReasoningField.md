# Conscious-Access Round Four: p-adic Reasoning Fields and Crystallisation

## Scope

This tranche turns the supplied p-adic/kernel/crystallisation discussion into a finite exact Agda spine. It reuses the repository's existing `DASHI.Geometry.SSP369Ultrametric` prefix carrier and the Round Three hybrid manifold/tree bridge. The new modules separate structures that were previously liable to be conflated:

- balanced triadic digits versus residues modulo three;
- carryless cyclic addition versus carry-aware hierarchical addition;
- coordinatewise support/orientation folding versus a global inversion quotient;
- finite prefix cylinders versus a completed p-adic space;
- exact reasoning addresses versus their lossy Euclidean render coordinates;
- linear shell selection versus nonlinear stripe/hexagon competition;
- threshold selection versus mobility-limited freeze-out;
- periodic crystal symmetry versus cut-and-project internal-space coding.

The formal results are exact finite witnesses. They are not promoted to a completed p-adic analysis library, a solved Swift-Hohenberg PDE, a physical crystallisation calculation, or a biological/cognitive ontology.

## Kernel lift and inversion quotient

`DASHI.Biology.TriadicKernelLiftQuotientExact` defines

```text
Kernel d = Vec KernelTrit d
NineSheet = KernelTrit × KernelTrit
```

and proves the exact round trips

```text
splitNine (liftNine xs sheet) = (xs , sheet)
liftNine (splitNine ys)       = ys.
```

Thus a nine-lift is a product extension by two triadic coordinates. It is not definitionally the addition of one continuous field component.

The module also defines the genuine three-state support/orientation fold

```text
inactiveTrit
activeTrit negativeOrientation
activeTrit positiveOrientation
```

and the five global inversion orbits of one nine-state sheet:

```text
zero
first axis
second axis
equal-sign diagonal
opposite-sign diagonal.
```

Negating both sheet coordinates leaves the quotient orbit unchanged.

## Carryless and carry-aware triadic arithmetic

`DASHI.Biology.TriadicCarryResidualExact` defines cyclic addition on `TriResidue` and proves associativity and commutativity by complete finite case analysis. It also proves the characteristic-three correction

```text
residue1 + residue1 = residue2,
```

so ternary cyclic addition does not inherit Boolean XOR self-cancellation.

The differentiable/probabilistic algebraic layer is represented by cyclic convolution of three masses. For every hard basis pair,

```text
basisMass a star basisMass b = basisMass (cyclicAdd3 a b).
```

The balanced carry transducer has type

```text
KernelTrit × KernelTrit × KernelTrit
  -> KernelTrit × KernelTrit
```

and proves, for all twenty-seven input triples, exact reconstruction of the local integer total and equivariance under global sign inversion. The canonical positive overflow is

```text
(+1) + (+1) + 0 = (-1) + 3(+1).
```

The output digit records what resolves at the current depth; the carry records what is transported to the next depth.

## Prefix cylinders, LOD, and render geometry

`DASHI.Biology.PadicCylinderLODReasoningField` reuses `SSP369Ultrametric` addresses. It proves that adding one child digit and then projecting returns the parent prefix. It also constructs exact three-child mass aggregation and the canonical witness

```text
2 + 3 + 4 = 9.
```

Class masses are aggregated before any class normalisation. A finite conditional-average certificate is represented division-free by

```text
3 * parentValue = child3 + child6 + child9.
```

The Morton-like observation map consumes three hierarchical digits per Euclidean voxel level. At depth six it records a coarse voxel and a fine voxel, and flattening produces a side-nine coordinate. The address remains the semantic state; the voxel is an observation layout.

`DASHI.Biology.ReasoningFieldRenderBridgeExact` carries the exact source address through the render sample. It proves:

- two addresses can share a coarse cache key while differing at the fine voxel;
- inverse-density brightness can be implemented without negative source mass;
- camera projection is non-injective through an explicit voxel collision.

The final image cannot replace the retained address metadata.

## Causal chart and residual objective

`DASHI.Biology.CausalHierarchicalChartResidualExact` types history and target separately. A predictor consumes `HistoryTwo`; the target is available only to the residual scorer. Two cases with the same history therefore have the same prediction even when their targets differ.

The module separates spatial partition depth from triadic value depth, defines local block transformations, and gives a complete two-candidate objective

```text
chart complexity + balanced-ternary residual depth.
```

The refined candidate has objective `3`, while the coarse candidate has objective `4`. This proves finite minimality over the declared candidate type only; it does not imply a globally linear-time search algorithm.

A depth-two consistency tube is represented by equal coarse digits with unconstrained fine digits. It is not promoted to a differential manifold.

## Digit-plane collapse

`DASHI.Biology.FinitePadicCollapseExact` introduces a four-plane support profile and the weighted thickness

```text
rho0 + 3 rho1 + 9 rho2 + 27 rho3.
```

The exact finite trajectory has thicknesses

```text
58 -> 19 -> 7 -> 7.
```

The fixed point retains coarse support while its high-depth tail vanishes. Collapse therefore means hierarchical residual thinning, not erasure of all digit planes. Support and orientation remain separate data.

## Shell selection and nonlinear branch competition

`DASHI.Biology.FiniteWaveShellGradientExact` defines the finite analogue of the quadratic Swift-Hohenberg shell penalty

```text
(|k|^2 - k0^2)^2.
```

For the three test classes its values are

```text
zero mode      1
selected shell 0
high mode      9.
```

The selected shell minimises the quadratic penalty, but the shell alone does not select a unique direction or nonlinear lattice branch.

`DASHI.Biology.FiniteCrystallisationModeSelectionExact` constructs a six-direction cycle, opposite directions, and a canonical three-mode star separated by 120 degrees. It proves that branch preference depends on the nonlinear coupling regime:

```text
reflection-symmetric quartic regime -> stripe score 1, hexagon score 3
resonant triad-coupled regime       -> stripe score 3, hexagon score 1.
```

The module also distinguishes a triangular translation carrier from visible hexagonal cells.

## Stabiliser and fundamental domain

`DASHI.Biology.FiniteSymmetryStabiliserExact` constructs the two-element reflection group and proves its action law on two-site patterns. The constant pattern has stabiliser size `2`; the asymmetric pattern has stabiliser size `1`.

One fundamental-domain value reconstructs the symmetric pattern, while the asymmetric pattern needs two independent site values. This establishes a finite representation-complexity reduction from symmetry. It does not assert that the more symmetric pattern has lower physical energy or is globally MDL-minimal.

## Resource-limited crystallisation

`DASHI.Biology.ResourceLimitedCrystallisationExact` separates the threshold predicate from the mobility value. Its exact trajectory is

```text
homogeneous -> nucleated -> coarsening -> frozen,
```

with defect count

```text
3 -> 3 -> 2 -> 1.
```

At resource exhaustion the mobility is zero, the frozen state is idempotent, and one defect remains. A local orientation mismatch supplies a finite grain-boundary residual. Freeze-out is therefore not defect erasure or proof of a global minimum.

## Residue crystallisation and changing periods

`DASHI.Biology.PadicCrystallisationResidueExact` uses a four-site periodic carrier. The coarse residue pattern is invariant under a one-site shift. The finer alternating pattern is invariant only under a two-site shift:

```text
coarse shift-one mismatch = 0
fine shift-one mismatch   = 4
fine shift-two mismatch   = 0.
```

The coarse depth stabilises at time one and the fine depth at time two. Finer residues can reduce translation symmetry and need not stabilise simultaneously with coarse residues.

## Coupled order and Gibbs code length

`DASHI.Biology.CoupledWaveTriadicOrderExact` combines a finite wave branch, a nine-sheet inversion orbit, and a residual defect. Internal orbit preference and wave-branch score are separate terms. The aligned hexagonal/equal-sign candidate has objective `1`; two mismatched alternatives have objective `4`.

The finite Gibbs code length

```text
L(E) = 2 E + 5
```

preserves the objective ordering. This is an exact affine negative-log-prior analogue, not an identity between every free-energy functional and every MDL objective.

## Internal-space projection

`DASHI.Biology.QuasiperiodicInternalSpaceBoundaryExact` separates physical and internal coordinates, defines a finite acceptance window, and proves that different accepted internal codes may have the same physical projection. One exact nine-lift refines the internal code.

Periodic planar rotation orders and quasiperiodic rotation labels are represented by different types. The module explicitly blocks the inference

```text
nine-lift -> irrational projection -> quasiperiodicity.
```

An irrational superspace projection remains a separate continuum construction.

## Source atlas

`DASHI.Biology.ConsciousAccessRound4SourceAtlas` records title, authors, venue, year, DOI, imported role, and excluded promotion for:

- Jean-Pierre Serre, *A Course in Arithmetic*, DOI `10.1007/978-1-4684-9884-4`;
- Alain M. Robert, *A Course in p-adic Analysis*, DOI `10.1007/978-1-4757-3254-2`;
- J. Swift and P. C. Hohenberg, *Hydrodynamic Fluctuations at the Convective Instability*, DOI `10.1103/PhysRevA.15.319`;
- M. C. Cross and P. C. Hohenberg, *Pattern Formation Outside of Equilibrium*, DOI `10.1103/RevModPhys.65.851`;
- Ron Lifshitz and Dean M. Petrich, *Theoretical Model for Faraday Waves with Multiple-Frequency Forcing*, DOI `10.1103/PhysRevLett.79.1261`;
- T. W. B. Kibble, *Topology of Cosmic Domains and Strings*, DOI `10.1088/0305-4470/9/8/029`;
- Robert V. Moody, *Model Sets: A Survey*, DOI `10.1007/978-3-662-04253-3_6`;
- Michael Baake and Uwe Grimm, *Aperiodic Order, Volume 1*, DOI `10.1017/CBO9781139025256`.

Repository-original finite lemmas are marked by their module comments and are not assigned invented DOIs.

## Regression and authority boundary

`DASHI.Biology.ConsciousAccessRound4FullBoundary` packages the complete theorem surface. `DASHI.Biology.ConsciousAccessRound4Regression` imports every module and exposes the central exact witnesses.

The formal boundary rejects promotion to:

- a solved continuum Swift-Hohenberg model;
- a completed implementation of the full p-adic field;
- derivation of a physical crystal from reasoning data;
- identification of a rendered filament with an observed continuous thought process.
