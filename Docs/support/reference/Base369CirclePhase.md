# Base369 circle-phase and generated-expression bridge

## Status

This note is a **typed finite-carrier and interpretation bridge**. It does not
claim that the numerals `3`, `6`, and `9` possess a universal physical status,
and it does not attribute a technical `369` theory to Nikola Tesla.

The checked implementation is:

- `DASHI.Foundations.Base369CirclePhase`
- `DASHI.Foundations.Base369CirclePhaseRegression`

It reuses the existing `Base369` carriers `TriTruth`, `HexTruth`, and
`NonaryTruth`, plus the role-separation discipline from
`DASHI.Foundations.NumberRoleBoundary`.

The implemented polyphase/spectral/engineering follow-on is documented in
`Docs/support/reference/Base369TeslaPolyphase.md`.

## 1. Generated expressions, not a basis

The syntax

```text
e ::= 3 | 6 | 9 | e + e | e * e
```

is represented by `Expr369`. The words **generator** or **generated
expression algebra** are intentional. The values `3`, `6`, and `9` are not an
independent basis because

```text
6 = 3 + 3
9 = 3 + 3 + 3.
```

With no multiplicative unit adjoined, repeated addition and multiplication
remain inside the nonnegative multiples of three. The implementation makes
that invariant constructional by evaluating first in units of three:

```text
eval369 e = 3 * unitValue e.
```

Consequently every expression has a `MultipleOfThree` witness. The motivating
example is checked directly:

```text
3 * (6 + 9) = 45.
```

This proves expressibility of `45` in the grammar. It does **not** make that
expression the unique or geometrically canonical description of a 45-degree
rotation.

## 2. Circle partitions as cyclic phase carriers

The existing carriers can be read as finite cyclic phase grids:

| carrier | circle partition | angular step |
|---|---:|---:|
| `TriTruth` | `C3` | `2π / 3` |
| `HexTruth` | `C6` | `2π / 6` |
| `NonaryTruth` | `C9` | `2π / 9` |

The implementation keeps this phase reading separate from the carriers'
algebraic reading through `NumberRoleBoundary`.

There are canonical inclusions

```text
C3 -> C6
C3 -> C9
```

because `3` divides both `6` and `9`. There is no direct refinement inclusion
between `C6` and `C9`, because neither sector count divides the other. Their
least common refinement is

```text
lcm(6, 9) = 18,
```

represented by `Phase18`. The two paths from the triadic grid agree:

```text
C3 -> C6 -> C18
C3 -> C9 -> C18.
```

`tri-common-refinement-commutes` proves this agreement by complete finite case
analysis.

This is the useful structural reading of `3, 6, 9`:

- `3` is a common coarse phase grid;
- `6 = 2 * 3` is a binary refinement of that grid;
- `9 = 3 * 3` is a ternary refinement of that grid;
- `18 = 2 * 3^2` is their common refinement.

A strictly triadic nested tower remains

```text
3, 9, 27, 81, ...
```

whereas `6` belongs to a compatible binary-refinement branch.

## 3. Phase, periodicity, and Tesla boundary

Periodic signals naturally live on a phase circle. Three-phase alternating
current uses three phases separated by `2π/3`; this is a genuine engineering
use of a `C3` phase partition and is relevant to Tesla's work on polyphase
systems and rotating magnetic fields.

The repository does not infer from this that Tesla developed a universal
`3-6-9` arithmetic, nor that decimal digit patterns provide physical laws.
The formal content is limited to generated expressions, finite cyclic phase
carriers, and refinement maps.

## 4. Concentric-ring unrolling

For a sector with real radius `r` and angle `θ` in radians, the concentric arc
at radial coordinate `ρ` has length

```text
ℓ(ρ) = θρ.
```

Straightening and stacking the infinitesimal rings gives a triangular linear
profile with height `r` and terminal base `θr`. Integrating the profile yields

```text
A = ∫[0,r] θρ dρ = (1/2) θr².
```

For an `n`-sector equal partition, `θ = 2π/n`, hence each sector has area

```text
A_n = πr² / n.
```

The present Agda module records this as `SectorUnrollingBoundary` rather than
pretending that the finite `Nat` carriers prove a theorem of real integration.
The follow-on module `DASHI.Geometry.Base369SectorUnrollingFinite` now checks
exact finite radial arc profiles and accumulated area units, while leaving the
continuum limit behind the same analytic boundary.

## 5. Implemented follow-on

The next finite tranche is now implemented:

1. `DASHI.Foundations.Base369BinaryTernaryRefinement` gives the
   `C_(2^a 3^b)` resolution coordinates and commuting binary/ternary refinement;
2. `DASHI.Foundations.Base369TriadicPhaseTower` checks a concrete
   `C3 -> C9 -> C27` lift/project fragment;
3. `DASHI.Foundations.Base369PolyphaseCharacters` checks the symbolic `C3`
   character-exponent sectors corresponding to zero, positive, and negative
   phase sequence;
4. `DASHI.Physics.Closure.Base369PolyphaseKernelBoundary` checks finite shift
   equivariance and symbolic one-step mode response;
5. `DASHI.Foundations.Base369EngineeringMDL` separates winding, switching,
   components, switching complexity, harmonic synthesis, and control-program
   costs and combines them with model/residual description length;
6. `DASHI.Physics.Closure.Base369AutomorphicSpectralGate` keeps trace/theta,
   modular-law, Eisenstein, elliptic-curve, and `j` promotion dependency-gated;
7. `DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary` keeps engineering
   motivation separate from unsupported historical attribution.

The remaining theorem path is generic `C n`, divisibility-indexed maps, full
finite Fourier inversion over an explicit scalar carrier, quotient-compatible
kernel families, calibrated engineering costs, and the real sector-area limit.
