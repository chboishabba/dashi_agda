# Navier–Stokes Round 31 — the exact HH-bad scale-gain gate

Round 31 attacks the first falsification target in the nine-owner programme. It does not add a terminal Clay wrapper and it does not claim the physical bad-set estimate.

## The obstruction

At shell scale \(\lambda_q\), the raw three-dimensional Bernstein route has the schematic cost

\[
M_q^{\mathrm{raw}} \sim \lambda_q^3 E_q,
\]

whereas viscous shell dissipation is

\[
D_q \sim \nu \lambda_q^2 E_q.
\]

The existing repository no-go theorem already proves that no scale-independent constant can absorb the first expression into the second: one full shell power is missing.

## Exact time-localized repair

The new machine-checked theorem proves that, for a bad-shell occupation time \(\tau_q\),

\[
\tau_q\lambda_q\le \eta_q\nu
\]

implies

\[
\tau_q\lambda_q^3E_q
\le
\eta_q\nu\lambda_q^2E_q.
\]

The proof is exact rational ordered-field algebra. It is uniform in the shell label and sums over any finite bad-shell family.

At the critical occupation time

\[
\tau_q=\eta_q\nu\lambda_q^{-1},
\]

the two sides are exactly equal. This identifies, rather than merely names, the missing one-inverse-scale mechanism.

The physical PDE obligation is now precise:

```text
physicalHHBadOccupationEstimate:
  badOccupation(q) * shellScale(q)
  <= eta_HHbad(q) * viscosity
```

with constants uniform in the Galerkin cutoff, shell cutoff and maximal time.

## Alternative amplitude repair

A second exact theorem proves that

\[
A_q\le\eta_q\nu\lambda_q^2
\]

implies

\[
A_qE_q\le\eta_q\nu\lambda_q^2E_q.
\]

Thus the HH-bad lane may close by either:

1. an inverse-scale occupation-time estimate; or
2. a dissipation-wavenumber / intermittency estimate placing the bad amplitude directly in the viscous range.

A raw shell Bernstein estimate alone cannot close the lane.

## Same-carrier, same-object condition

The strengthened Galerkin builder now requires:

```text
velocityAt(positive mode) = stored positive coefficient
velocityAt(negative mode) = conjugate reconstructed coefficient
retained modes            = exact positive/negative reconstruction list
```

Forgetting these equalities recovers the Round-30 builder and its literal viscous-plus-quadratic vector field. They prevent a state-indexed existential choice of an unrelated finite system from being consumed as one canonical ODE.

The concrete state lookup that inhabits this stronger record remains open.

## Anti-circular remainder grammar

Owner remainders are now generated only from:

```text
initial/data-controlled constants
known critical integrals
lower-order controlled quantities
declared dissipation fractions
finite sums
```

Every grammar term compiles exactly to

\[
\eta D+A+B\int X.
\]

There is no constructor for an uncontrolled BKM integral, Serrin norm or target critical supremum.

## Exact frontier after Round 31

The algebraic question “where can the missing shell power come from?” is closed. The physical theorem is not.

The highest-alpha next producer is one of:

\[
\tau_q\lambda_q\le\eta_q\nu,
\]

or

\[
A_q\le\eta_q\nu\lambda_q^2,
\]

on the actual HH-bad cells, with a cutoff-uniform coefficient small enough to leave room for the commutator and tail owners.

Only after that estimate is established should the remaining owner family be assembled and the strict global viscosity margin be attempted.
