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
A future analytic module may discharge the integral after selecting the
repository's canonical real-analysis interface.

## 5. Extension path

The next mathematically meaningful extensions are:

1. a generic finite cyclic carrier `C n` with rotation and group laws;
2. refinement maps induced by divisibility proofs `n | m`;
3. common refinements expressed by `lcm` and coarse intersections by `gcd`;
4. characters/Fourier modes on the finite phase grids;
5. an MDL cost on `Expr369`, selecting minimum-cost representatives modulo a
   chosen circle resolution;
6. a real-analysis sector-unrolling theorem kept separate from historical or
   physical interpretation.
