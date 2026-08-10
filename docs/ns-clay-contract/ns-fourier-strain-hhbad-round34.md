# Navier–Stokes Round 34 — literal finite-system repair, Fourier strain, HH-bad summability and Cotlar target

Round 34 follows the shortest-cut contract after Round 33. It advances actual finite-system and Fourier/operator mathematics. It does **not** add a terminal Clay wrapper and it does not promote a conditional owner estimate to a physical theorem.

The controlling rule remains:

```text
never transport a bound without transporting its index,
carrier, trajectory and resource valuation.
```

## 1. The Round-30 finite-system API is repaired rather than bypassed

The old `FiniteComplex3GalerkinSystem F E I` was indexed by the integer embedding `E` and inverse-square datum `I`, but several Round-30 consumers attempted to call projections that did not exist. More importantly, the old fields

```text
zeroModeExcluded : Set
realityClosed    : Set
```

were markers, not usable nonzero/transversality proofs.

Round 34 adds exact accessors for the indexed embedding, inverse-square datum, velocity, Galerkin laws and projected ordered term. The physical finite-system wrapper now carries the actual theorem

```text
retainedModeNonzero :
  mode ∈ modes -> NonZeroMode mode
```

alongside retained transversality. The projected nonlinear fold and dependent physical vector field consume those literal proofs.

## 2. The correct F1 object is cutoff-indexed

Round 33 proved a genuine obstruction: an arbitrary raw `ReconstructedPhysicalState` can contain duplicate positive representatives with conflicting values or a positive/negative-sheet conflict. Such a state cannot define the same-object Fourier velocity function.

Round 34 therefore does not pretend that every weak raw state admits a finite Galerkin system. It defines

```text
CutoffSameObjectDatum F E state
```

carrying:

```text
same-object compatibility;
one concrete cutoff N;
one ModeInverseSquare datum;
viscosity;
reconstructed retained modes = nonzeroCutoffModes N.
```

The constructor

```text
canonicalPhysicalFiniteSystem
```

then produces the literal finite Galerkin system with

```text
velocity = Round-33 executable canonical lookup;
triads   = physicalTriadEnumeration N;
modes    = reconstructedStateModes state.
```

Every retained mode is proved nonzero and every retained coefficient is proved transverse. A `CutoffSameObjectFamily` produces the existing Round-31 `SameCarrierSameObjectGalerkinBuilder`.

Thus the finite-system constructor is closed on the mathematically correct strengthened carrier. What remains is to construct the strengthened cutoff-compatible state family used by the actual ODE, rather than asking the weaker raw state type to contain information it was never designed to store.

## 3. The old rational ODE state carrier was too weak

The Round-26 polynomial syntax uses rational coefficients and an `Assignment = CoordinateVariable -> Q`. That is excellent exact syntax for the degree-two Galerkin polynomial, but `Q` is not the complete real state space required by Picard–Lindelöf.

Round 34 separates syntax from semantics. `NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact` interprets the same rational atoms in the repository's pinned Murray–Bishop constructive real carrier:

```text
BishopAssignment = CoordinateVariable -> BishopReal
```

with rational coefficients embedded as constant Bishop reals. Using Bishop's checked commutative-ring solver, it proves on the real carrier

```text
c*x - c*u = c*(x-u)
```

and

```text
c*x*y - c*u*v
  = c*((x-u)*y + u*(y-v)),
```

then proves the corresponding identity for arbitrary finite atom lists. Equality is Bishop setoid equality, not propositional equality.

This removes the false inference

```text
rational polynomial syntax -> rational physical trajectory.
```

The remaining F2/F3 work is now precise: encode the finite physical Fourier carrier into a Bishop-real coordinate assignment, prove the literal field commutes with that encoding, and construct the finite-dimensional contraction/Picard–Lindelöf theorem on that complete carrier.

## 4. Exact periodic Fourier strain multiplier

For nonzero Fourier mode `k`, vorticity coefficient `omega`, and `a = k cross omega`, Round 34 defines

\[
S_k(\omega)
=-\frac{1}{2|k|^2}
  \left(k\otimes a+a\otimes k\right).
\]

This is the symmetric-gradient Fourier symbol obtained from the exact Fourier Biot–Savart inverse. The formalization proves:

```text
S_k is symmetric;
tr S_k = 0;
S_k v = -(1/(2|k|^2)) [ k ((k×omega)·v) + (k×omega)(k·v) ];
v·S_k v = -|k|^-2 (k·v)((k×omega)·v);
omega·S_k(omega)omega = 0;
k·omega=0 -> S_k(omega)omega=0.
```

The last two identities isolate the exact same-mode depletion before any normalized direction field or square root is introduced.

For transverse `omega`, the exact Frobenius identity is

\[
\|S_k(\omega)\|_F^2=\frac12|\omega|^2.
\]

Summing over any finite family yields the cutoff-independent identity

\[
\sum_k\|S_k(\omega_k)\|_F^2
=\frac12\sum_k|\omega_k|^2.
\]

This closes the finite Fourier `L^2` multiplier half of the periodic strain package. It does not yet construct the real-space periodic principal-value kernel, its Euclidean-homogeneous-plus-smooth decomposition, or the kernel increment estimate needed for physical `HH-good`.

## 5. The sharp HH-bad target profile is globally summable

Round 33 proved that the unique exact multiplicative compensation for the raw ratio

\[
R_q=2\,2^q
\]

is

\[
g_q(\eta)=\frac{\eta}{2}2^{-q}.
\]

Round 34 now proves the exact finite-prefix identity

\[
\sum_{q=0}^{Q}g_q(\eta)
=\eta-\eta 2^{-(Q+1)},
\]

hence

\[
\sum_{q=0}^{Q}g_q(\eta)+\eta 2^{-(Q+1)}=\eta.
\]

So the inverse-dyadic repair demanded by the one-shell Bernstein obstruction does **not** create a divergent global shell tax. Its total target mass is exactly `eta`.

This makes the physical question sharper: derive this shell-decaying profile from occupation time, dissipation-range amplitude, intermittency, alignment or another signed mechanism. The profile is arithmetically feasible; it is not yet physically produced.

## 6. A concrete rational Cotlar target

The existing Round-30 Cotlar reducer accepted a two-sided cross-shell decay certificate. Round 34 fixes an exact rational target and its complete row mass.

For the direct target

\[
\|T_q^*T_r\|,\ \|T_qT_r^*\|
\le C2^{-|q-r|},
\]

the symmetric row mass through distance `R` is exactly

\[
C\left(1+2\sum_{d=1}^{R}2^{-d}\right)
=C\left(3-2\,2^{-R}\right),
\]

with limiting cutoff-independent mass `3C`.

The stronger textbook square-root target

\[
\|T_q^*T_r\|,\ \|T_qT_r^*\|
\le C^2 4^{-|q-r|}
\]

has the exact rational square-root envelope `C 2^{-|q-r|}` because `(2^-d)^2=4^-d`.

What remains is the physical theorem that the literal commutator operators satisfy one of these two-sided estimates uniformly in Galerkin cutoff, shell cutoff and hypothetical maximal time.

## 7. Frontier after Round 34

Closed or materially narrowed in this tranche:

```text
F1a literal cutoff-indexed same-object finite-system constructor
F1b actual retained nonzero/transversality evidence
F2a complete-real semantics of the rational Galerkin polynomial
A1a exact Cotlar dyadic target and cutoff-uniform row mass
A3a exact periodic Fourier strain symbol
A3b exact finite Fourier L2 strain identity
A6a exact global summability of the uniquely required HH-bad gain profile
```

Still physical/open:

```text
F1c construct the cutoff-compatible same-object state family used by the ODE
F2b physical Fourier state <-> Bishop-real coordinate equivalence
F2c physicalFieldEncodedExactly on the Bishop carrier
F3  finite Bishop-real Picard-Lindelof / contraction theorem
F4  literal exhaustive triad-energy family
F5  real integrated finite energy identity
F6  literal global finite flow
S1  literal trajectory shell authority

A1  physical two-sided Com pair-product decay
A2  physical Com owner estimate
A3  periodic principal-value strain kernel and increment theorem
A4  physical HH-good owner estimate
A5  physical directional-defect evolution
A6  physical HH-bad occupation or amplitude gain profile
A7  physical positive-variation/crossing estimate
A8  physical HH-bad owner estimate
A9-A14 remaining physical owners

C1-C3 one actual nine-owner family with strict eta_total < 1
L1-L6 shell/Galerkin limits, compactness, Serrin continuation and final witness
```

The highest-alpha order remains physical `HH-bad`, physical two-sided `Com`, then periodic principal-value strain/`HH-good`. Round 34 narrows all three without pretending to have supplied the missing PDE estimates.
