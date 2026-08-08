# Highest-alpha lemma ladder to a Clay-submissible periodic proof

[Back to the paper-corpus overview](README.md)

The literal Fefferman periodic theorem type and terminal composition are present. This page lists the shortest dependency chain that could inhabit the physical inputs without adding a non-Clay hypothesis.

Round 27 inserts concrete projector, involution, state/dual, commutator, common-core and Plücker lemmas before the open analytic taxes. The central physical theorem remains unchanged:

```text
cutoff-uniform positive nonlinear production
  <= eta * viscous dissipation + admissible remainder,
eta < 1.
```

## A. Official target and reduction

### L0 — Literal Fefferman periodic alternative B — exact target

For every positive viscosity and every smooth divergence-free unit-periodic datum on `T3`, with zero force, construct global smooth periodic velocity and pressure satisfying Navier–Stokes, incompressibility and the initial condition. Pressure periodicity is explicit. Mean zero, uniqueness and a separate energy-equality hypothesis are not added.

### L1 — Mean centering and Galilean restoration — reducer checked

Construct the spatial mean `m`, solve for `v0=u0-m`, and prove

```text
u(x,t)=v(x-mt,t)+m,
p(x,t)=q(x-mt,t)
```

preserves the literal target.

### L2 — Critical local theory, maximal time and restart — classical interface checked

A bounded critical norm near a hypothetical finite maximal time must provide an extension beyond it.

## B. Finite physical PDE

### M1 — Sharp finite shell-projector algebra — checked exact in Round 27

For the literal shell index define `Pq(k)` as its Kronecker indicator. Prove:

```text
Pq^2=Pq,
Pq Pr=0 for q!=r,
finite shell resolution on the cutoff carrier,
commutation with diagonal multipliers,
covariance under shell-preserving mode maps.
```

Smooth Littlewood–Paley operator bounds remain open.

### M2 — Fourier reality involution — checked exact algebra in Round 27

Define

```text
J u(k)=conjugate(u(-k)).
```

Prove `J^2=id`, equivalence of `Ju=u` with Fourier reality, and the generic theorem

```text
F(Ju)=J(Fu)  and  Ju=u  =>  J(Fu)=Fu.
```

Diagonal reality-compatible multipliers are instantiated. Equivariance of the full nonlinear Galerkin field remains open.

### L3 — Literal finite Galerkin flow — materially narrowed; analytic instance open

Already checked:

- cutoff modes and duplicate-free resonant output fibres;
- exact Leray coefficient and physical/Fourier coefficient equality;
- linear/bilinear coordinate syntax of degree at most two;
- `xy-uv=(x-u)y+u(y-v)` for every finite coordinate sum;
- reality reconstruction and conjugate transversality;
- physical three-leg triad energy cancellation;
- M2’s fixed-point/equivariance criterion.

Still required:

```text
full viscous-plus-convolution vector field maps the finite carrier to itself;
finite normed local-Lipschitz bound;
Picard–Lindelöf;
time-dependent physical energy identity;
global finite-dimensional existence.
```

### L4 — Exhaustive physical support — checked exact in Round 25

Every literal resonant triad belongs uniquely to `HH`, `LH`, `HL` or `CC`; the differentiated commutator is the fifth class `Com`. There is no unnamed remainder.

### L5 — Physical signed filtered-vorticity shell balance — algebraic destination checked; evolution open

Round 26 supplies a signed weighted ledger and forces its five source coordinates from the literal output fibre. M1 now supplies exact sharp finite projectors. Still required:

```text
derive the time-dependent shell equation from the Galerkin trajectory;
construct lower and upper cutoff-boundary atoms;
prove cutoff-uniform critical shell norm equivalence.
```

### L6 — Pair-input-frequency diffusion coercivity — checked exact algebra

Damping remains attached to both input frequencies before a high–high product collapses to a low output.

## C. Operator and geometric precursors

### M3 — State/dual translation–multiplier commutator — checked exact in Round 27

Fourier states and multiplier/test symbols are different types. For translation by `ell`:

```text
M_m T_ell u - T_ell M_m u
  = M_(m-tau_ell m) T_ell u.
```

Pointwise the signed symbol is `(m(k)-m(k-ell))u(k-ell)`. No early absolute value is introduced.

### M4 — Centred five-source probe — checked exact in Round 27

For `Fi=base+delta_i`, prove division-free:

```text
5(w dot F)
 = (sum w) aug(F)
   + sum_i (5w_i-sum w) delta_i.
```

Uniform weights see only total production; centred weights expose source imbalance.

### M5 — Maximal uniform viscosity core — checked exact algebra in Round 27

For the nine unique tax owners, an allocation decomposition satisfies

```text
allocation(owner)=commonCore+residual(owner).
```

If a canonical owner has zero residual, its common core dominates every competing common core for the same allocation vector. Physical allocations remain open.

### M6 — Physical triad Plücker/Gram geometry — checked exact in Round 27

For each physical triad:

```text
|p cross q|^2=|p|^2|q|^2-(p dot q)^2.
```

Swapping inputs reverses orientation and preserves squared area. No vector normalization or division is used.

## D. Load-bearing physical estimates

### L7 — Duplicate-free physical tax ledger — ownership checked; coefficients open

Each positive-production atom has exactly one owner:

```text
HH-good, HH-bad, LH, HL, CC, Com, kernel, tail, boundary.
```

Every owner must prove

```text
Fi+ <= eta_i D + A_i(T) + B_i integral(X),
```

uniformly in shell, shell cutoff, Galerkin cutoff and hypothetical maximal time.

### L8 — Periodic principal-value strain kernel and Calderón–Zygmund estimate — open

Construct the periodic strain distribution, principal-value cancellation, spherical moments, smooth periodic remainder and the norm/difference estimates needed for high–high depletion.

### L9 — Signed low-advection operator tax — M3 checked; quantitative theorem open

Prove a cutoff-independent estimate for

```text
sum_q 2^-q |<[Pq,u_low dot grad] omega_near-q,omega_q>|
  <= eta_Com D + A_Com(T) + B_Com integral(X).
```

The already-failed absolute Schur route must be replaced by a sign-preserving square-function, almost-orthogonality or `TT*` argument.

### L10 — Directional high–high near-field tax — division-free algebra and M6 checked; physical inequality open

Use the periodic kernel and unnormalised cross-product defect to obtain

```text
(Fq_HH,near)+ <= C_HH d_q D_q + named remainder.
```

The zero denominator branch is explicit.

### L11 — Directional defect evolution — open

Derive from the physical PDE:

```text
dAq/dt + c0 nu 2^(2q) Aq
 <= G_adv + G_stretch + G_subgrid + G_kernel + G_tail.
```

Every source receives one tax owner.

### L12 — Hysteretic bad-excursion and amplitude tax — finite charge checked; PDE budget open

Round 26 proves entry gaps are paid by positive variation. Still required are a cutoff-uniform positive-variation estimate and an amplitude estimate strong enough to tax production on bad intervals.

### L13 — Lower interaction taxes and dissipation-range split — open

Close `LH`, `HL` and `CC`, and derive rather than assume the dynamic high-mode viscosity condition and critical low-frequency reservoir.

### L14 — Far-field, commutator and cutoff-tail summability — open

All residual families must be uniformly integrable or vanish in the nested limits. Any geometric tail ratio must satisfy one cutoff-independent `rho<1`.

## E. Strict critical budget

### L15 — Strict maximal-core/unique-owner viscosity margin — central bottleneck

Instantiate M5 with physical allocations and prove

```text
eta_total
 = eta_HH-good + eta_HH-bad + eta_LH + eta_HL + eta_CC
   + eta_Com + eta_kernel + eta_tail + eta_boundary
 < 1.
```

No term may be hidden or counted twice.

### L16 — Uniform finite critical estimate — reducer checked once L7–L15 exist

Derive uniformly in final cutoffs:

```text
X_N,Q(t)+(1-eta_total)D_N,Q(0,t)
 <= X_N,Q(0)+A(t)+B integral_0^t X_N,Q.
```

### L17 — Non-circular Grönwall — reducer checked

Obtain a finite critical bound without placing the target supremum, BKM integral or an equivalent continuation criterion on the uncontrolled side.

## F. Infinite limits and global continuation

### L18 — Shell cutoff limit — open analytic producer

Recover the full shell sum and every named source/tax family.

### L19 — Galerkin cutoff limit — open analytic producer

Obtain strong enough compactness to identify the quadratic term and initial trace while retaining

```text
u in L-infinity_t H^(1/2)_x intersect L2_t H^(3/2)_x.
```

### L20 — Absorbed-budget lower semicontinuity — reducer checked

Absorption occurs before weak convergence and the positive margin survives the limit.

### L21 — Critical-to-Serrin bridge and periodic continuation — open physical instance

Prove

```text
L-infinity H^(1/2) intersect L2 H^(3/2)
  -> L4 H1 -> L4 L6,
```

then instantiate periodic Prodi–Serrin continuation.

### L22 — Smooth bootstrap, pressure recovery and Galilean uncentering — open analytic instances

Recover smooth periodic pressure and restore arbitrary periodic mean.

### L23 — Literal Fefferman witness — checked terminal reducer

Once the physical inputs above are inhabited, the existing composition constructs the exact periodic Clay witness. No additional terminal wrapper is required.

## Highest-alpha priority after Round 27

The immediate order is:

```text
1. full nonlinear reality/transversality equivariance;
2. finite local Lipschitz, Picard–Lindelöf, energy identity and global finite flow;
3. physical time-dependent signed shell balance using M1;
4. first cutoff-independent signed operator tax using M3;
5. periodic strain/CZ plus M6 high–high tax;
6. bad-excursion amplitude and remaining source/tail taxes;
7. physical M5 allocation and L15 eta_total<1;
8. limits, Serrin continuation, smooth pressure and literal witness.
```

The single highest-value theorem remains `UniformCriticalNonlinearityAbsorption` with a cutoff-independent coefficient strictly below one. A result counts as progress only when it completes a physical producer, produces a uniform coefficient, or supplies a quantified counterexample eliminating a route.
