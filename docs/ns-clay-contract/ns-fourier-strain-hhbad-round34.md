# Navier–Stokes Round 34 — finite-system repair, Bishop semantics, Fourier strain and sharp shell targets

Round 34 follows the shortest-cut contract after Round 33. It advances actual finite-system, finite-energy, Fourier and shell-decay mathematics. It does **not** add a terminal Clay wrapper and it does not promote a conditional owner estimate to a physical theorem.

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

Round 34 therefore defines the strengthened datum

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

The constructor `canonicalPhysicalFiniteSystem` then produces the literal finite Galerkin system with

```text
velocity = Round-33 executable canonical lookup;
triads   = physicalTriadEnumeration N;
modes    = reconstructedStateModes state.
```

Every retained mode is proved nonzero and every retained coefficient is proved transverse. A `CutoffSameObjectFamily` produces the existing Round-31 `SameCarrierSameObjectGalerkinBuilder`.

Thus the finite-system constructor is closed on the mathematically correct strengthened carrier. The remaining F1 producer is to construct the cutoff-compatible state family used by the actual ODE, rather than asking the weaker raw state type to contain information it was never designed to store.

## 3. The old rational ODE state carrier was too weak

The Round-26 polynomial syntax uses rational coefficients and an `Assignment = CoordinateVariable -> Q`. That is exact syntax for the degree-two Galerkin polynomial, but `Q` is not the complete real state space required by Picard–Lindelöf.

Round 34 separates syntax from semantics. `NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact` interprets the same rational atoms in the repository's pinned Murray–Bishop constructive-real carrier:

```text
BishopAssignment = CoordinateVariable -> BishopReal
```

with rational coefficients embedded as constant Bishop reals. Using Bishop's checked commutative-ring solver, it proves on that real carrier

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

The remaining F2/F3 work is precise: encode the finite physical Fourier carrier into a Bishop-real coordinate assignment, prove the literal field commutes with that encoding, and construct the finite-dimensional contraction/Picard–Lindelöf theorem on that complete carrier.

## 4. Safe canonical triad-orbit quotient for F4

The repository already contained a useful permutation/reality quotient of finite zero-sum triads, but its representative recursion called itself on a filtered list and therefore used a termination pragma. Round 34 replaces that route with strictly structural recursion on the original finite list.

`OrbitRepresentativePartition source` carries:

```text
representatives;
representatives are a subset of source;
every source triad is covered modulo the 12-element orbit;
distinct representatives are orbit-separated.
```

Insertion performs one decidable orbit lookup. On a hit, the old representative list is retained and coverage extends to the new head. On a miss, the head is inserted and the negative lookup proof establishes separation. No recursion occurs on a filtered list and no termination pragma is used.

Specialising to `fullCutoffZeroSumTriads` and attaching zero-sum evidence constructs

```text
safeFullCutoffCanonicalTriadOrbitEnumeration
```

with exhaustive and no-duplicate permutation/reality orbit coverage. This closes the finite combinatorial subleaf of F4. The remaining F4 theorem is now narrower: identify the actual complex three-leg Galerkin energy transfer on these packets and connect it to the already-developed local complex triad-conservation algebra.

## 5. Exact periodic Fourier strain multiplier

For nonzero Fourier mode `k`, vorticity coefficient `omega`, and `a = k cross omega`, Round 34 defines

\[
S_k(\omega)
=-\frac{1}{2|k|^2}
  \left(k\otimes a+a\otimes k\right).
\]

The formalization proves:

```text
S_k is symmetric;
tr S_k = 0;
S_k v = -(1/(2|k|^2)) [ k ((k×omega)·v) + (k×omega)(k·v) ];
v·S_k v = -|k|^-2 (k·v)((k×omega)·v);
omega·S_k(omega)omega = 0;
k·omega=0 -> S_k(omega)omega=0.
```

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

## 6. The sharp HH-bad target profile is globally summable

Round 33 proved that the unique exact multiplicative compensation for

\[
R_q=2\,2^q
\]

is

\[
g_q(\eta)=\frac{\eta}{2}2^{-q}.
\]

Round 34 proves

\[
\sum_{q=0}^{Q}g_q(\eta)
=\eta-\eta 2^{-(Q+1)},
\]

hence

\[
\sum_{q=0}^{Q}g_q(\eta)+\eta 2^{-(Q+1)}=\eta.
\]

So the inverse-dyadic repair demanded by the one-shell Bernstein obstruction does **not** create a divergent global shell tax. Its total target mass is exactly `eta`.

## 7. Luo critical dissipation matches the required HH-bad scaling

The literal length of Luo's parabolic time window is not itself the Round-33 inverse-shell gain. The useful matching quantity is the critical localized high-frequency dissipation scale. Round 34 formalizes this as

\[
D_q^{\rm crit}
=\frac{\eta}{2}\nu\lambda_q^{-1}.
\]

It proves exactly

\[
\lambda_q D_q^{\rm crit}=\frac{\eta}{2}\nu,
\qquad
D_q^{\rm crit}R_q=\eta\nu.
\]

More generally, a `LuoCriticalDissipationCell` carrying

\[
\lambda_qD_q\le\frac{\eta}{2}\nu
\]

implies

\[
D_qR_q\le\eta\nu.
\]

If the actual physical HH-bad gain satisfies `0 <= G_q <= D_q`, then the same absorption follows:

\[
G_qR_q\le\eta\nu.
\]

This is a route refinement, not a physical closure. Two producer statements remain explicit and false: construct the physical Luo-style localized-dissipation estimate on the DASHI trajectory, and prove that the actual HH-bad gain is controlled by that localized dissipation.

## 8. Concrete rational Cotlar targets

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

For the stronger square-root target

\[
\|T_q^*T_r\|,\ \|T_qT_r^*\|
\le C^2 4^{-|q-r|},
\]

the exact rational root envelope is `C 2^{-|q-r|}`.

Luo's scalar flux calculation naturally exhibits the stronger direct quarter-decay profile. Round 34 therefore also proves

\[
1+2\sum_{d=1}^{R}4^{-d}
=\frac53-\frac23\,4^{-R},
\]

with limiting mass `5/3`. This records the exact extra summability available if quarter-decay survives the operator realization. It does **not** turn a scalar flux estimate into the required two-sided operator pair-product theorem.

## 9. Frontier after Round 34

Closed or materially narrowed in this tranche:

```text
F1a literal cutoff-indexed same-object finite-system constructor
F1b actual retained nonzero/transversality evidence
F2a complete-real semantics of the rational Galerkin polynomial
F4a safe exhaustive/no-duplicate triad orbit enumeration
A1a exact Cotlar dyadic and quarter-decay row masses
A3a exact periodic Fourier strain symbol
A3b exact finite Fourier L2 strain identity
A6a exact global summability of the uniquely required HH-bad gain profile
A6b exact Luo critical-dissipation -> sharp HH-bad calibration bridge
```

Still physical/open:

```text
F1c construct the cutoff-compatible same-object state family used by the ODE
F2b physical Fourier state <-> Bishop-real coordinate equivalence
F2c physicalFieldEncodedExactly on the Bishop carrier
F3  finite Bishop-real Picard-Lindelof / contraction theorem
F4b literal complex three-leg Galerkin energy-transfer identification
F5  real integrated finite energy identity
F6  literal global finite flow
S1  literal trajectory shell authority

A1  physical two-sided Com pair-product decay
A2  physical Com owner estimate
A3  periodic principal-value strain kernel and increment theorem
A4  physical HH-good owner estimate
A5  physical directional-defect evolution
A6c physical Luo-style localized high-frequency dissipation smallness
A6d physical HH-bad gain <= localized-dissipation link
A7  physical positive-variation/crossing estimate
A8  physical HH-bad owner estimate
A9-A14 remaining physical owners

C1-C3 one actual nine-owner family with strict eta_total < 1
L1-L6 shell/Galerkin limits, compactness, Serrin continuation and final witness
```

The highest-alpha order remains physical `HH-bad`, physical two-sided `Com`, then periodic principal-value strain/`HH-good`, while F2--F6 are completed on the corrected finite real carrier. Round 34 narrows all of these without pretending to have supplied the missing Clay-level PDE estimates.
