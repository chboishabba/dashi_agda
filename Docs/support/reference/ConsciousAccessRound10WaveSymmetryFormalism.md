# Conscious Access Round 10 — Wave, Fourier, Quaternion and Orbit Formalism

## Scope

This tranche turns the supplied wave/conscious-access discussion into theorem-bearing finite mathematics while reusing the repository's existing wave, 369, Monster, quaternion, observer and conscious-access owners.

The core factorization is:

```text
representation/Fourier mode
+ local quaternion orientation
+ orbit/symmetry reduction
+ field-dependent effective coupling
+ recurrent access criteria.
```

These axes are deliberately not collapsed.

## 1. Exact ternary Fourier modes

`BalancedTernaryFourierModeExact.agda` reuses `TriadicDepthOneCharacters` and `FiniteThreeCycleTorusExact`.

The coarse carrier is the existing finite torus

```text
T^2_3 = Z/3 x Z/3.
```

Each coordinate is evaluated by an exact additive `C3Phase` character.  Translation by one step satisfies a literal eigenphase law for the matching coordinate, while the orthogonal coordinate character is unchanged.

The module also checks:

```text
9 coarse modes x 3^9 fine frequencies = 3^11 = 177147,
```

and proves that evaluation at the completed `j` channel is invariant under each ordinary torus pullback.

This is finite harmonic analysis, not a continuum wavelength theorem.

## 2. More than circular/toroidal waves

`FiniteTorusVectorWaveGeometryExact.agda` adds an actual centered-difference vector calculus to the 3 x 3 torus.  Four explicit fields have center signatures

```text
uniform planar   : (div,curl) = (0,0)
radial source    : (div,curl) = (4,0)
rotation         : (div,curl) = (0,4)
spiral = src+rot : (div,curl) = (4,4).
```

The construction is motivated by Das–Zabeh–Ermentrout–Jacobs (DOI `10.1038/s41467-026-71386-z`) and the Muller–Busch–Davis–Reynolds review (DOI `10.1016/j.neuron.2026.06.019`).  It is a finite algebraic prototype, not a reconstruction of their measurements and not a complete discrete Hodge theorem.

## 3. Quaternion orientation over a mode

`QuaternionSymmetryResolvedWaveExact.agda` reuses the proof-bearing unit-quaternion action already proved in `QuaternionHopfUnitOrbitExact`.

A mode now has four typed coordinates:

```text
spatial T^2_3 mode
fine 3^9 frequency
finite div/curl geometry
unit-quaternion orientation.
```

Unit-quaternion action changes only the orientation.  Spatial mode, fine frequency and geometry are exact orbit invariants.  Thus quaternion state answers "how is this mode oriented?" rather than replacing the Fourier/representation answer to "which mode is this?"

The quaternion time-frequency calibration is Flamant–Le Bihan–Chainais, DOI `10.1016/j.acha.2017.05.007`.

## 4. Traveling control wave and analog computation

`TravelingWaveFunctionalTopologyExact.agda` gives concrete finite theorems:

```text
same structural edge + different field gate -> different effective edge;
same high-frequency content + different slow control -> different readout;
pullback moves a one-site stencil on T^2_3;
opposite encoded phases superpose to exact zero;
same neural state + different field -> different successor.
```

This is the exact finite layer beneath the existing abstract `ConsciousAccessCoalition` cycle.

The field-control literature is pinned to Miller–Brincat–Roy, DOI `10.31234/osf.io/z48x7_v3`, and Pinotsis–Miller, DOI `10.1093/cercor/bhag098`.  The module explicitly blocks the promotion `finite feedback -> universal ephaptic wave mechanism`.

## 5. Access bridge

`ConsciousAccessWaveControlBridgeExact.agda` packages the actual theorem functions rather than Boolean receipts.  A canonical evidence object contains:

- both torus translation eigenlaws;
- both `j`-readout invariances;
- planar/source/rotation/spiral div/curl witnesses;
- functional-topology separation;
- cross-frequency gating separation;
- nontrivial moving-stencil witness;
- exact opposite-phase cancellation;
- field-to-successor causal separation;
- the existing recurrent coalition criteria.

The bridge keeps explicit non-promotions for phenomenal identity, `j = global workspace`, Monster dimension = neural mode, universal ephaptic generation, and equal spectral power = equal cognitive state.

The anesthesia phase-alignment calibration is Bardon et al., DOI `10.1016/j.celrep.2025.115685`.

## 6. Monster/orbit extraction boundary

`MonsterWaveModeSeparatingProbeExact.agda` uses the existing genuine 3A/3B/3C normalizer labels and the generic `SeparatingProbeFamilyExact` owner.

A candidate is

```text
(order-three Monster lane, proposed physical geometry).
```

Two probes — normalizer kind and physical geometry — separate the candidate exactly.  A concrete witness has the same 3A lane but planar versus rotational geometry, proving:

```text
same order-three lane != determined physical wave geometry.
```

This formalizes the correct route:

```text
actual group action
-> representation/character probes
-> orbit/irrep decomposition
-> independent physical geometry comparison.
```

Period or dimension arithmetic alone cannot identify a physical mode.

## 7. Independent Riemann reflection-orbit cross-pollination

The fourth supplied discussion is implemented separately in `RiemannReflectionOrbitDefectExact.agda`.

For

```text
alpha = Re(s) - 1/2,
```

critical reflection sends

```text
alpha -> -alpha,
```

while

```text
alpha^2
```

is invariant.  The reflected pair has zero signed displacement but total defect `2 alpha^2`.

The module then carries out the proposed 2 x 2 experiment on the generic centered block

```text
[ c+a  b ]
[ b   c-a ].
```

Its exact invariants are

```text
trace = 2c
det   = c^2 - b^2 - a^2,
```

and both are invariant under `a -> -a`; the determinant therefore retains the orientation-blind transverse defect `a^2` after sign cancellation.

Alpöge–Furman is pinned by arXiv DOI `10.48550/arXiv.2608.13637`, but the module explicitly does not identify this generic block with their actual Weil-form block and does not claim that their present theorem bounds `sum alpha^2`.

## Validation

The cumulative root is

```text
DASHI/Biology/ConsciousAccessRound10WaveSymmetryValidation.agda
```

and the focused checker is

```text
bash scripts/check_conscious_access_round10_wave_symmetry.sh
```

The checker rejects postulates/holes/unsafe escapes, verifies theorem and DOI surfaces, runs the Round-9 predecessor checker, and then sends the Round-10 root through the repository's Agda 2.9 parallel driver.

## Claim boundary

This tranche proves finite algebraic structure.  It does not prove:

```text
finite T^2_3 mode = measured cortical wavelength
quaternion coefficient = complete neural state
j completion = consciousness
369 arithmetic = Monster action
Monster conjugacy class = physical wave class
ephaptic coupling = universal traveling-wave mechanism
access-consciousness = phenomenal consciousness
generic reflection block = Alpoge--Furman Weil block
finite alpha^2 invariance = RH.
```
