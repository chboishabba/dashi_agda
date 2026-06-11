# Marx Dialectical Derivative Receipt

Declared surface level: `bridge/diagnostic`, with an algebraic theorem-shaped
subsurface.

This note records a narrow Marx/DASHI bridge. It does not claim that DASHI
proves Marx's historical or political theory, and it does not claim a completed
foundation of all modern analysis. It does record a stronger mathematical
point: Marx's algebraic method for factorable functions has the same
receipt-gated operator-promotion shape that DASHI uses elsewhere:

```text
finite displacement
-> algebraic factorization witness
-> lawful cancellation / collapse
-> promoted operational symbol
```

## Source Anchors

Local source:

```text
/home/c/Downloads/Marx_Mathematical_Manuscripts_1881.pdf
```

Extracted with `pdftotext` to `/tmp/marx_math_manuscripts.txt`.

The relevant local text anchors are:

- lines 1104-1115: division by `x1 - x` occurs while `x1 - x` is still a
  finite difference;
- lines 1207-1266: Marx distinguishes the preliminary derived function from
  the final derived function, after `x1` is reduced to `x`;
- lines 1270-1316: the apparent `0/0` is interpreted as an expression of a
  process whose real content was already established on the algebraic side;
- lines 1736-1743: symbolic differential coefficients become operational
  symbols, meaning symbols of a process still to be carried out.

## DASHI Reading

The finite-difference construction is a carrier transport:

```text
x -> x1 -> x*
```

The final `x*` is not a bare return to the original state. It is a return after
the factorization witness has preserved a residue. In the cubic example:

```text
(x1^3 - x^3) / (x1 - x)
  = x1^2 + x1*x + x^2
  -> 3*x^2 after x1 = x
```

The key governance condition is that `x1 - x` is not projected to zero before
the quotient has been made algebraically non-mystical.

## Algebraic Calculus Schema

The admissible algebraic regime is:

```text
Delta  = finite displacement
rho    = factorization receipt
kappa  = collapse x1 -> x
sigma  = promoted symbolic operator
```

For a function `f`, the DASHI/Marx admissibility condition is:

```text
f(x1) - f(x) = (x1 - x) * F_f(x,x1)
```

The Marx derivative is then:

```text
D_M f(x) = F_f(x,x)
```

This formalizes the algebraic factorization class. For polynomials the
standard witness is:

```text
x1^n - x^n = (x1 - x) * sum_{k=0}^{n-1} x1^{n-1-k} * x^k
```

so the power-rule shape is:

```text
D_M(x^n) = n*x^{n-1}
```

The Agda receipt also records theorem-shaped receipts for linearity, product,
and chain rules. They are intentionally not marked as promoted theorem closure
yet: a future stronger pass should supply a typed algebraic carrier with
addition, multiplication, distributivity, composition, and the needed nonzero
intermediate-displacement guards.

Safe strong statement:

```text
DASHI can formalize Marx's algebraic differential method as an admissible
finite-transport / factorization / collapse / operator-promotion pipeline.
```

Unsafe overclaim:

```text
DASHI has proved all of modern calculus, analysis, or differential geometry.
```

## Existing Repo Alignment

This is closest to the existing fascistic/antifascistic boundary vocabulary:

- `AntiFascistSystem.agda` records invertible, entropy-preserving dynamics and
  a no-collapse boundary.
- `FascisticSystem.agda` records projection/contraction style updates where
  entropy does not increase.
- `Docs/AntifascisticBoundaryAndMusic.md` gives the safe reading: a rich
  carrier can preserve structure while a coarse observable projection loses
  information.

The Marx bridge uses that same distinction. Prematurely setting `x1 - x = 0`
is a projection-only collapse. Marx's route preserves the carrier displacement
until a factorization witness makes the collapse admissible.

## Formal Receipt

The Agda surface is:

```text
DASHI/Physics/Closure/MarxDialecticalDerivativeReceipt.agda
```

It records:

- source anchors from Marx's mathematical manuscripts;
- ternary trace `zer -> pos -> zer`, read as identity, displacement,
  return-with-residue;
- a cubic witness for `x^3 -> 3*x^2`;
- an admissible factorization-class schema;
- theorem-shaped receipts for power, linearity, product, and chain rules;
- a non-promotion boundary: no modern-analysis or differential-geometry
  completion is claimed.

The receipt is diagnostic, but no longer merely metaphorical. Its main value is
that it makes the Marx algebraic regime compatible with existing DASHI
governance:

```text
no promotion without a non-collapse witness
```
