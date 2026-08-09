# Yang–Mills Round 41 — certified single-plaquette owner envelope

Round 41 implements the higher-alpha fork identified after Round 40: consume rigorous rational enclosures of the four physical singleton-owner coefficients without pretending that arbitrary selected-background matrix entries or a Moore–Penrose inverse are themselves rational.

## Exact input

For one selected plaquette, the certificate carries four intervals:

```text
localization
transport
near Green
far Green
```

Each interval contains the corresponding physical owner coefficient. The actual owner contribution must already satisfy

\[
R_i\le c_i^{\mathrm{actual}}\,C_p(h).
\]

The enclosure proves

\[
c_i^{\mathrm{actual}}\le c_i^{\mathrm{upper}}.
\]

Because the plaquette charge is nonnegative, exact ordered-field monotonicity gives

\[
R_i\le c_i^{\mathrm{upper}}\,C_p(h).
\]

## Explicit robustness slack

The certificate also carries a nonnegative padding coefficient \(\Delta_{\mathrm{YM}}\) with the exact identity

\[
c_{\mathrm{loc}}^{\mathrm{upper}}
+c_{\mathrm{tr}}^{\mathrm{upper}}
+c_{\mathrm{near}}^{\mathrm{upper}}
+c_{\mathrm{far}}^{\mathrm{upper}}
+\Delta_{\mathrm{YM}}
=
\frac{55}{18874368}.
\]

The padding is assigned to the localization owner. The new theorem proves that increasing its coefficient by a nonnegative amount preserves the owner inequality, then constructs the exact existing `CorrelatedOwnerBudgets` record.

Thus a generated interval computation may be consumed only after it supplies:

1. rigorous componentwise containment;
2. physical owner inequalities;
3. nonnegative plaquette charge;
4. nonnegative padding;
5. the exact rational budget identity.

A floating-point output or nominal optimizer result cannot promote itself.

## End-to-end correlated residual theorem

Given the existing exact-cancellation witness, the certified envelope now proves directly

\[
R_{\mathrm{correlated}}
\le
\frac{55}{18874368}\,C_p(h).
\]

This is the exact scalar inequality consumed by the Round-40 selected-singleton reducer.

## What this changes

The previous Round-40 optimizer type required exact reported rational costs. Round 41 provides a robust route for validated numerics and interval analysis:

```text
physical selected background
  -> literal atom and Green evaluation
  -> rigorous rational coefficient enclosures
  -> explicit positive budget padding
  -> exact CorrelatedOwnerBudgets
  -> singleton residual bound.
```

It does not identify a non-rational physical matrix with a rational one, and it does not construct the selected-background stencil, multiplier floor, atom family or four physical inequalities.

## Immediate physical producer target

For one literal selected background and one plaquette, produce:

```text
CertifiedSelectedPlaquetteEnvelope
```

from the actual

\[
A\mapsto L_A\mapsto K_A^+\mapsto R_{A,p}(h)
\]

pipeline. The key success condition is a strictly positive or at least nonnegative certified padding after all enclosure widths and triangle-inequality losses have been charged.
