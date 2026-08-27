# Conscious Access Round 11 — Wave, Fourier, Quaternion and Orbit Formalism

## Scope

This tranche turns the supplied wave/conscious-access discussion into theorem-bearing finite mathematics while reusing the repository's existing wave, 369, Monster, quaternion, observer and conscious-access owners. It is cumulative over `ConsciousAccessRound10PsychogeographyValidation`.

The core factorization is:

```text
representation/Fourier mode
+ local quaternion orientation
+ orbit/symmetry reduction
+ field-dependent effective coupling
+ recurrent access criteria.
```

These axes are deliberately not collapsed.

## Exact ternary Fourier modes

`BalancedTernaryFourierModeExact.agda` reuses `TriadicDepthOneCharacters` and `FiniteThreeCycleTorusExact`. The coarse carrier is the existing finite torus `T^2_3 = Z/3 x Z/3`. Each coordinate is evaluated by an exact additive `C3Phase` character. Translation by one step satisfies a literal eigenphase law for the matching coordinate, while the orthogonal coordinate character is unchanged.

It also checks

```text
9 coarse modes x 3^9 fine frequencies = 3^11 = 177147
```

and proves that evaluation at the completed `j` channel is invariant under each ordinary torus pullback. This is finite harmonic analysis, not a continuum wavelength theorem.

## More than circular/toroidal waves

`FiniteTorusVectorWaveGeometryExact.agda` adds centered-difference vector calculus to the 3 x 3 torus. Four explicit fields have center signatures

```text
uniform planar   : (div,curl) = (0,0)
radial source    : (div,curl) = (4,0)
rotation         : (div,curl) = (0,4)
spiral = src+rot : (div,curl) = (4,4).
```

The construction is motivated by Das–Zabeh–Ermentrout–Jacobs (DOI `10.1038/s41467-026-71386-z`) and Muller–Busch–Davis–Reynolds (DOI `10.1016/j.neuron.2026.06.019`). It is a finite prototype, not a reconstruction of cortical measurements and not a complete discrete Hodge theorem.

## Quaternion orientation over a mode

`QuaternionSymmetryResolvedWaveExact.agda` reuses the proof-bearing unit-quaternion action already proved in `QuaternionHopfUnitOrbitExact`.

A mode has four typed coordinates:

```text
spatial T^2_3 mode
fine 3^9 frequency
finite div/curl geometry
unit-quaternion orientation.
```

Unit-quaternion action changes only orientation. Spatial mode, fine frequency and geometry are exact orbit invariants. Quaternion state therefore answers "how is this mode oriented?" rather than replacing the Fourier/representation answer to "which mode is this?" The quaternion time-frequency calibration is Flamant–Le Bihan–Chainais, DOI `10.1016/j.acha.2017.05.007`.

## Traveling control wave and analog computation

`TravelingWaveFunctionalTopologyExact.agda` proves finite witnesses for:

```text
same structural edge + different field gate -> different effective edge
same high-frequency content + different slow control -> different readout
pullback moves a one-site stencil on T^2_3
opposite encoded phases superpose to exact zero
same neural state + different field -> different successor.
```

The field-control literature is pinned to Miller–Brincat–Roy, DOI `10.31234/osf.io/z48x7_v3`, and Pinotsis–Miller, DOI `10.1093/cercor/bhag098`. The module blocks `finite feedback -> universal ephaptic wave mechanism`.

## Access bridge

`ConsciousAccessWaveControlBridgeExact.agda` packages theorem functions rather than Boolean receipts. The canonical evidence object contains both torus translation eigenlaws, both `j`-readout invariances, the four div/curl geometry witnesses, functional-topology separation, cross-frequency gating separation, a nontrivial moving-stencil witness, exact opposite-phase cancellation, field-to-successor causal separation, and the existing recurrent coalition criteria.

The bridge retains non-promotions for phenomenal identity, `j = global workspace`, Monster dimension = neural mode, universal ephaptic generation, and equal spectral power = equal cognitive state. Anesthesia phase calibration is Bardon et al., DOI `10.1016/j.celrep.2025.115685`.

## Monster/orbit extraction boundary

`MonsterWaveModeSeparatingProbeExact.agda` uses the existing 3A/3B/3C normalizer labels and `SeparatingProbeFamilyExact`. A candidate is

```text
(order-three Monster lane, proposed physical geometry).
```

Normalizer kind plus physical geometry form a separating probe family. A concrete witness has the same 3A lane but planar versus rotational geometry, proving that same order-three lane does not determine physical wave geometry.

The formal route is therefore:

```text
actual group action
-> representation/character probes
-> orbit/irrep decomposition
-> independent physical geometry comparison.
```

Period or dimension arithmetic alone cannot identify a physical mode.

## Independent Riemann reflection-orbit cross-pollination

`RiemannReflectionOrbitDefectExact.agda` implements the fourth supplied discussion separately. For `alpha = Re(s) - 1/2`, critical reflection sends `alpha -> -alpha`, while `alpha^2` is invariant. The reflected pair has zero signed displacement but total defect `2 alpha^2`.

The module carries out the proposed generic 2 x 2 centered-block experiment:

```text
[ c+a  b ]
[ b   c-a ]
```

with exact invariants

```text
trace = 2c
det   = c^2 - b^2 - a^2.
```

Both are invariant under `a -> -a`; the determinant retains the orientation-blind displacement residual. Alpöge–Furman is pinned by arXiv DOI `10.48550/arXiv.2608.13637`, but the generic block is explicitly not identified with their Weil-form block and no `sum alpha^2` theorem is claimed from their current result.

## Validation

Cumulative root:

```text
DASHI/Biology/ConsciousAccessRound11WaveSymmetryValidation.agda
```

Focused checker:

```text
bash scripts/check_conscious_access_round11_wave_symmetry.sh
```

The checker rejects postulates/holes/unsafe escapes, verifies theorem and DOI surfaces, runs the existing Round-10 predecessor checker, and sends the Round-11 root through the repository's Agda 2.9 parallel driver.

## Claim boundary

This tranche does not prove:

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
