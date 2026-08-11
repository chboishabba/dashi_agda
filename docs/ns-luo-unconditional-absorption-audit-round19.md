# NS Luo Round 19: unconditional-absorption forensic audit

## Scope

This round audits the mechanism advertised in Ryusho Nemoto's manuscript
*Global Regularity of the Three-Dimensional Navier–Stokes Equations via a
Coupled Energy and Stability Framework* (PhilArchive record `NEMGRO`; no DOI
was located in the public record).

The public abstract claims global smoothness from a coupled energy/stability
functional and spectral rigidity of the trace-free strain tensor. The exact
proposition text and the proposed PDE estimates were supplied externally for
audit. No result from the manuscript is imported as a theorem.

The question is not whether coupled-function cancellation is algebraically
possible. It is. The question is whether trace-free spectral rigidity produces
the required scale-uniform differential inequality without assuming an
uncontrolled norm.

## Exact spectral theorem

For a trace-free symmetric three-by-three spectrum

```text
lambda3 = -(lambda1 + lambda2),
Q       = lambda1^2 + lambda2^2 + lambda3^2,
P       = lambda1 lambda2 lambda3,
C3      = lambda1^3 + lambda2^3 + lambda3^3,
```

Round 19 proves

```text
C3 = 3 P
```

and the sharp identity

```text
Q^3 - 54 P^2
  = 2 (lambda1-lambda2)^2
      (lambda2-lambda3)^2
      (lambda1-lambda3)^2.
```

Consequently

```text
54 P^2 <= Q^3,
6 C3^2 <= Q^3.
```

This is the correct finite spectral-rigidity content. It is homogeneous of
order six after squaring, equivalently cubic versus `Q^(3/2)`. It is not a
linear estimate of a cubic quantity by the quadratic magnitude `Q`.

The source header records Jeffrey S. Case and Aaron J. Tyrrell,
*A Sharp Inequality for Trace-Free Matrices with Applications to
Hypersurfaces*, DOI `10.1090/proc/16657`, and Evan Miller's strain-eigenvalue
criterion, arXiv DOI `10.48550/arXiv.1710.05569`.

## Exact no-go result

The quadratic projection does not determine cubic orientation:

```text
( 2,-1,-1): Q = 6, C3 =  6
(-2, 1, 1): Q = 6, C3 = -6.
```

More decisively, on the extensional equality branch

```text
(2r,-r,-r),
Q(r)  = 6 r^2,
C3(r) = 6 r^3.
```

For every nonnegative proposed universal coefficient `K`, choose

```text
r = K + 1.
```

Then Round 19 proves strictly

```text
C3(r) - K Q(r) = 6 (K+1)^2 > 0,
```

hence

```text
K Q(r) < C3(r).
```

Therefore no scale-independent nonnegative coefficient can absorb the
positive cubic strain branch into the quadratic strain magnitude merely from
trace-free spectral algebra.

This does not disprove every possible coupled-functional proof. It proves that
the missing differential inequality must use additional dynamics,
cancellation, localization, a higher-order term, or a genuinely scale-critical
quantity. It cannot be obtained from the sharp trace-free eigenvalue identity
alone.

## Coupled functional: exact algebra versus physical producer

Round 19 proves the exact implication

```text
E' + D       <= N  + R_E
alpha S'     <= -N + R_S
--------------------------------
(E' + alpha S') + D <= R_E + R_S.
```

It also proves that an additional bound

```text
R_E + R_S <= eta D
```

closes the strict margin

```text
(E' + alpha S') + (1-eta) D <= 0.
```

The nonlinear cancellation is therefore not the disputed step. The hard
producer is the second differential inequality together with a non-circular
residual estimate. Any manuscript proof must expose:

1. the exact definition and sign of the stability functional;
2. every integration-by-parts and boundary term;
3. the coefficient of the cubic strain term;
4. the terms remaining after cancellation;
5. a bound of those terms by a strict fraction of dissipation using only
   already-controlled quantities.

## Residual ledger and two-lane assembly

The finite residual ledger is now literal:

```text
R_q = R_q^collar
    + R_q^tail
    + R_q^pressure
    + R_q^low
    + R_q^phase
    + R_q^passive
    + R_q^fragmentation.
```

The weighted total is proved equal to the sum of the seven weighted component
ledgers, and componentwise budgets imply their exact combined budget.

The lower/comparable and high-high lanes are also assembled exactly:

```text
L <= eta_L V + R_L
H <= eta_H V + R_H
eta_L + eta_H <= eta
--------------------------------
L + H <= eta V + R_L + R_H,
```

with the remaining viscosity coefficient exposed as `1-eta`.

## Highest-alpha frontier after the audit

The algebraic shortcut has been tested and does not eliminate the physical
producer. The shortest remaining route is still:

```text
periodic strain / directional-defect representation
  -> good-time high-high absorption
  -> bad-time residence compression
  -> seven-source critical weighted summability
  -> strict total coefficient eta < 1
  -> H^(1/2) continuation.
```

A different coupled-functional route remains viable only if it supplies an
independently proved stability-response inequality whose residuals pass the
same non-circular and scale-uniform audit.

## Files

```text
DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
DASHI/Physics/Closure/NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact.agda
DASHI/Physics/Closure/NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact.agda
DASHI/Physics/Closure/NSTriadKNLuoResidualSourceLedgerExact.agda
DASHI/Physics/Closure/NSTriadKNLuoTwoLaneStrictAbsorptionExact.agda
DASHI/Physics/Closure/NSTriadKNLuoUnconditionalAbsorptionRound19Validation.agda
```

No unconditional Navier–Stokes regularity theorem is asserted.
