# Base369 Tesla-compatible polyphase assembly

## Status and boundary

This tranche formalises a modern DASHI phase/refinement interpretation motivated
by periodic, rotating-field, resonance, and polyphase engineering. It does **not**
attribute Base369, 3-adic refinement, representation-theoretic decomposition,
MDL, Eisenstein series, or the `j`-invariant to Nikola Tesla. It also does not
promote a universal physical `369` doctrine.

The implementation is:

- `DASHI.Foundations.Base369BinaryTernaryRefinement`
- `DASHI.Foundations.Base369PolyphaseCharacters`
- `DASHI.Foundations.Base369EngineeringMDL`
- `DASHI.Foundations.Base369TriadicPhaseTower`
- `DASHI.Physics.Closure.Base369PolyphaseKernelBoundary`
- `DASHI.Physics.Closure.Base369AutomorphicSpectralGate`
- `DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary`
- `DASHI.Geometry.Base369SectorUnrollingFinite`
- `DASHI.Foundations.Base369TeslaPolyphaseRegression`

It extends, rather than replaces:

- `DASHI.Foundations.Base369CirclePhase`
- `DASHI.Foundations.HexTruthPolarityFactor`
- `DASHI.Foundations.SSPPrimeLane369Refinement`
- `DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge`

## 1. Structural reading of 3, 6, and 9

The checked interpretation is:

```text
3 = coarse three-phase carrier
6 = three-phase carrier × binary polarity / half-cycle refinement
9 = ternary refinement of the three-phase carrier
```

The phase grids form a diamond, not a chain:

```text
        C18
       /   \
     C6     C9
       \   /
        C3
```

`C6` and `C9` are incomparable as equal-sector refinements because neither `6`
divides `9` nor `9` divides `6`. Their common refinement has `lcm(6,9)=18`
sectors.

The general resolution coordinate is

```text
R(a,b) = C_(2^a 3^b).
```

Binary and ternary refinement update independent coordinates and therefore
commute:

```text
B(T(R(a,b))) = R(a+1,b+1) = T(B(R(a,b))).
```

The canonical points are:

```text
C3  = R(0,1)
C6  = R(1,1)
C9  = R(0,2)
C18 = R(1,2).
```

## 2. Finite triadic tower

A concrete finite fragment is checked:

```text
C3 -> C9 -> C27.
```

Each step has a lift and a coarse-sector projection with

```text
project (lift x) = x.
```

This is the first exact phase-tower fragment. It is not yet a generic theorem
for every `C_(3^n)`, an inverse-limit construction of `Z_3`, or a claim that
physical phase is intrinsically 3-adic. It supplies the finite carrier shape
needed by later quotient-compatible kernels.

## 3. Character sectors and three-phase sequences

For `C3`, a complex character would be

```text
chi_m(k) = exp(2 pi i m k / 3).
```

The current finite module checks the exponent arithmetic `m*k mod 3` using the
existing `TriTruth` field. It exposes three symbolic sectors:

- zero/common sequence;
- positive/counterclockwise sequence;
- negative/clockwise sequence.

The exact checked law is the exponent form of character additivity:

```text
m * (x + y) = m*x + m*y mod 3.
```

This is enough to distinguish the three finite sequence sectors and prove their
one-step phase response. Complex roots of unity, a full DFT, Parseval,
reconstruction, and imported symmetrical-component engineering authority stay
behind an explicit analytic bridge.

## 4. Equivariant phase kernels and resonance boundary

A finite polyphase kernel is packaged with a selected phase shift and the law

```text
K(shift x) = shift(K x).
```

The tranche includes identity and one-step rotation examples on `C3`. Character
exponents obey the symbolic shift law

```text
chiExp_m(1 + x) = chiExp_m(1) + chiExp_m(x).
```

This is a finite equivariance/eigenphase shape. It does not yet provide complex
eigenvalues, gain, damping, forcing overlap, stability thresholds, or measured
resonance. In DASHI, resonance must be attached to an operator, a mode, and an
observable consequence—not inferred from decimal digits alone.

## 5. Engineering cost and MDL

A phase realisation carries six independent engineering costs:

1. number of windings;
2. number of phase-switching operations;
3. circuit-component count;
4. switching complexity;
5. harmonic-synthesis operations;
6. control-program length.

A consumer supplies weights and obtains

```text
engineeringCost =
  w_winding * windings
+ w_switch * phaseSwitches
+ w_component * components
+ w_complexity * switchingComplexity
+ w_harmonic * harmonicSynthesis
+ w_program * controlProgramLength.
```

The joint selection score is

```text
engineeringCost
+ modelDescriptionLength
+ residualDescriptionLength.
```

`CostModel369` interprets the existing generated-expression syntax into this
cost carrier. The default checked model is deliberately syntax-only: atoms cost
one component/token, `+` records phase-switch/control overhead, and `*` records
harmonic-synthesis/control overhead. For

```text
3 * (6 + 9) = 45
```

that benchmark records three atom components, one phase-switch operation, one
harmonic-synthesis operation, and control-program length five.

These are accounting conventions, not claims of circuit optimality. A real
motor, inverter, resonant coil, switching network, or controller must supply a
calibrated model and empirical loss data.

## 6. Finite concentric-ring unrolling

The geometry tranche now represents the finite radial approximation explicitly.
For discrete angle units `theta` and ring index `j`, the arc sample is

```text
arc(j) = theta * j.
```

`ringArcProfile theta M` stores the exact finite list, and
`finiteSectorAreaUnits` sums it. The checked example

```text
theta = 2, M = 3
profile = [0,2,4]
area units = 6
```

is purely finite. The continuum statement

```text
A = integral_0^r theta*rho d rho = (1/2) theta r^2
```

remains a real-analysis limit theorem. The finite profile is the object whose
straightening approaches the triangular envelope.

## 7. Arithmetic-representation-modular assembly

The intended broader pipeline is:

```text
finite quotient
-> finite character / irrep sector
-> trace or theta q-series
-> proved modular transformation law
-> Eisenstein/cusp decomposition
-> constructed elliptic spectral curve
-> j-invariant quotient.
```

The current checked tranche reaches the first two stages only. The gate enforces:

- Eisenstein promotion requires a proved modular transformation law;
- `j` promotion requires an actual elliptic/genus-one object and an appropriate
  modular or algebraic classification law.

Periodic or polyphase subject matter by itself does not justify modular forms.
Likewise, `j` is not a generic coordinate on a ternary stream or on `Z_3`; it is
only meaningful after an associated elliptic moduli object has been constructed.

## 8. Historical statement

The allowed statement is:

> Tesla's periodic, rotating-field, and polyphase engineering provides a
> legitimate motivating context for finite cyclic phase carriers.

The prohibited strengthening is:

> Tesla developed the Base369 carrier, a 3-adic phase tower, DASHI's
> representation/MDL assembly, or a universal technical 369 doctrine.

Accordingly, the repository treats this as a **Tesla-compatible modern
polyphase interpretation**, not a historical reconstruction.

## 9. Next proof obligations

The next useful extensions are:

1. a generic finite cyclic carrier `C n` with rotation and group laws;
2. divisibility-indexed refinement maps and checked `gcd`/`lcm` universal laws;
3. exact complex or algebraic root-of-unity scalars and finite Fourier inversion;
4. quotient-compatible kernel families across `C_(3^n)`;
5. measured motor/inverter/coil/control cost models;
6. a real-analysis proof of sector unrolling from finite radial sums;
7. construction of an actual trace/theta series before any modular promotion;
8. construction of an actual elliptic spectral curve before any `j` promotion.
