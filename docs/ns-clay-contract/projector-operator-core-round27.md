# Round 27 — finite shell projectors, signed operators and maximal viscosity core

[Back to the Clay-contract overview](README.md)

Round 27 imports only the mathematically useful architecture from the finite Monster projector/core lane. It does not assert a relationship between Monster representation theory and Navier–Stokes dynamics. The exported ideas are ordinary finite harmonic analysis and proof-accounting principles:

- explicit diagonal projectors;
- state/dual separation;
- equivariance under an involution;
- signed translation–multiplier commutators;
- centred probes;
- maximal common-core selection;
- division-free Plücker geometry;
- generated finite arithmetic certificates.

The attached highest-alpha route remains unchanged at its physical centre: the cutoff-uniform nonlinear absorption estimate and strict viscosity margin are still open.

## Sharp finite shell projectors

`NSTriadKNLiteralFiniteShellProjectorRound27Exact.agda` defines

```text
P_q(k) = 1 when shellIndex(k)=q, and 0 otherwise.
```

It proves pointwise

```text
P_q(k)^2 = P_q(k),
P_q(k) P_r(k) = 0 when q and r differ,
```

and finite identity resolution for every mode whose shell index is below the declared maximum. It also proves covariance under any shell-index-preserving mode map and exact commutation with arbitrary diagonal rational multipliers.

This is a sharp finite projector algebra. Smooth Littlewood–Paley multiplier bounds and uniform Sobolev norm equivalence remain analytic producers.

## Fourier reality as an involutive fixed-point carrier

`NSTriadKNRealityInvolutionEquivarianceRound27Exact.agda` defines

```text
J u(k) = conjugate(u(-k)).
```

It proves `J(Ju)=u` pointwise and proves equivalence between the standard Fourier reality law and `Ju=u`. A generic theorem shows that an extensional vector field satisfying

```text
F(Ju) = J(Fu)
```

preserves the real Fourier carrier.

Every diagonal multiplier with the correct symbol-reality law is instantiated as an equivariant field. The complete nonlinear Galerkin convolution still needs its own equivariance proof.

## State and multiplier/test dual separation

`NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact.agda` gives separate types to finite Fourier states and multiplier/test symbols. For translation by `ell`, it proves the exact signed identity

```text
M_m T_ell u - T_ell M_m u
  = M_(m - tau_ell m) T_ell u.
```

Pointwise this is

```text
(m(k)-m(k-ell)) u(k-ell).
```

No absolute value is inserted. The identity therefore preserves the cancellation needed for a later square-function or `TT*` estimate. The cutoff-uniform operator tax remains open.

## Centred five-source probe

`NSTriadKNCentredFiveSourceProbeRound27Exact.agda` writes each signed physical source as

```text
F_i = base + delta_i
```

and proves the division-free identity

```text
5 (w dot F)
  = (sum w) aug(F)
    + sum_i (5 w_i - sum w) delta_i.
```

Uniform weights annihilate the centred defect probe. This distinguishes total signed production from source imbalance and provides an exact audit tool for changing critical weights.

## Maximal uniform viscosity core

`NSTriadKNMaximalUniformViscosityCoreRound27Exact.agda` works over the nine unique Round 26 tax owners. A decomposition stores

```text
allocation(owner) = commonCore + residual(owner).
```

When one canonical owner is pinned with zero residual, the file proves that the canonical core equals that owner’s allocation and dominates the core of every competing decomposition of the same allocation vector.

This makes common-core maximality a theorem rather than an arbitrary allocation convention. The actual physical owner allocations and the strict rational coefficient inequality remain open.

## Physical-triad Plücker geometry

`NSTriadKNPhysicalTriadPluckerInvariantRound27Exact.agda` attaches the three coordinates of `p cross q` to every physical resonant triad and proves

```text
|p cross q|^2 = |p|^2 |q|^2 - (p dot q)^2.
```

Swapping the two inputs negates every oriented coordinate and preserves the squared interaction area. The invariant is division-free and separates interaction-plane geometry from dyadic shell magnitude.

## Finite certificate pipeline

`scripts/ns_round27_projector_operator_certificate.py` checks the finite projector, commutator, centred-probe, maximal-core and Plücker identities on a configurable lattice box. It writes a JSON receipt and regenerates `NSTriadKNLuoRound27FiniteCertificateGenerated.agda`.

For radius two the committed certificate records:

```text
125 modes,
250 projector-idempotence checks,
250 unequal-shell disjointness checks,
125 resolution checks,
15,625 commutator cells,
3,645 centred-probe cases,
15,625 Plücker pairs,
8 uniform-core candidates.
```

These finite checks can falsify incorrect algebra and constants. They do not establish cutoff uniformity.

## Exact remaining boundary

Round 27 has not proved:

1. equivariance and closure of the full nonlinear physical Galerkin vector field;
2. finite normed Picard–Lindelöf and global finite Galerkin existence;
3. the time-dependent physical filtered-vorticity shell balance;
4. smooth Littlewood–Paley bounds and critical norm equivalence;
5. the cutoff-uniform signed low-advection operator tax;
6. the periodic principal-value strain kernel and Calderón–Zygmund estimate;
7. the directional-defect evolution and bad-excursion amplitude tax;
8. physical owner allocations or the strict total coefficient below one;
9. shell/Galerkin limit passage or unconditional periodic regularity.

## Highest-alpha next theorem

The most informative immediate theorem remains

```text
LowAdvectsHighSignedOperatorTax
```

built from the now-exact multiplier-difference identity. In parallel, the finite ODE lane should prove full vector-field equivariance, local Lipschitz continuity, Picard–Lindelöf, the physical energy identity and global finite existence.

Progress is measured by a cutoff-independent coefficient, a completed physical finite-flow theorem, or a quantified counterexample—not by additional status records.
