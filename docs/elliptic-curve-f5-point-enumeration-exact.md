# Exact F5 enumeration for the BSD seed

`DASHI/Mathematics/Arithmetic/EllipticCurveF5PointEnumerationExact.agda` replaces the earlier prefilled fibre-count row with a literal finite-field scan for

```text
E : y^2 = x^3 - x
```
over `F5`.

The module defines all five residues, Boolean equality, the square table and the `x^3-x` table:

```text
x:          0 1 2 3 4
x^3-x:      0 0 1 4 0
```

It evaluates all 25 affine pairs `(x,y)`. The solution counts reduce definitionally to

```text
1,1,2,2,1,
```

so the affine count is `7`, and adding the unique projective point at infinity gives

```text
#E(F5)=8.
```

`EllipticCurveFrobeniusExact.agda` now imports this enumeration and derives its p=5 row from it. The downstream exact consequences remain

```text
a5 = 5 + 1 - 8 = -2,
P5(T)=1+2T+5T^2,
|a5|^2=4 <= 20=4p.
```

The enumeration module is imported by the cumulative substantive Millennium validation root and named explicitly in the no-hole/source/theorem checker. It remains a local Euler-factor witness, not a global L-function, Mordell–Weil, Selmer/Sha, or BSD proof.
