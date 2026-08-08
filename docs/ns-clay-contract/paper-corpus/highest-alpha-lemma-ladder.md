# Highest-alpha lemma ladder to a Clay-submissible periodic proof

[Back to the paper-corpus overview](README.md)

The terminal theorem type and final composition are present. The highest-alpha work is the shortest dependency chain that can inhabit the physical inputs without adding a non-Clay hypothesis.

## A. Target and local continuation

### L0 — Literal Fefferman periodic alternative (B) — exact target

For every `ν > 0` and every smooth divergence-free unit-periodic datum `u0` on `T3`, with zero force, construct smooth unit-periodic `u,p` for all `t ≥ 0` satisfying

```text
∂t u + (u·∇)u = ν Δu - ∇p,
∇·u = 0,
u(0) = u0.
```

Pressure periodicity is explicit. Mean zero, uniqueness and a separate periodic energy hypothesis are not added.

### L1 — Mean centering and Galilean restoration — reducer checked

Construct the spatial mean `m`, centered datum `v0=u0-m`, and prove

```text
u(x,t)=v(x-mt,t)+m,
p(x,t)=q(x-mt,t)
```

preserves the zero-force equation, smoothness, divergence, periodicity and initial trace.

### L2 — Local critical well-posedness, maximal time and restart — reducer/classical interface checked

For a selected critical space, construct a maximal strong solution and prove that a finite bound on the critical norm near `T*` supplies local existence beyond `T*`.

## B. Actual finite PDE and shell geometry

### L3 — Periodic divergence-free Fourier/Galerkin carrier — materially narrowed physical producer

Round 25 certifies the literal cutoff modes, resonant triads, duplicate-free output fibres, reality closure, Leray coefficient and coefficientwise physical/Fourier equivalence.

Round 26 adds:

- a coordinate syntax in which every finite Galerkin RHS atom is linear or bilinear and has degree at most two;
- the exact finite difference factorization `xy-uv=(x-u)y+u(y-v)`;
- a positive-orbit phase-space surface reconstructing negative modes by conjugation;
- an explicit conjugate-transversality law as the remaining constraint instance;
- local six-term triadwise energy cancellation;
- finite internal-transfer cancellation.

The remaining L3 producer is now:

```text
instantiate conjugate transversality on the selected continuum real carrier;
prove the literal polynomial vector field is locally Lipschitz in a finite norm;
apply Picard–Lindelöf;
connect the triadwise cancellation to the literal finite ODE energy identity;
use that identity to prove global finite-dimensional existence.
```

No ODE theorem is claimed merely from the degree-two syntax.

### L4 — Exhaustive physical Bony/commutator support theorem — checked exact in Round 25

Every literal cutoff `Z³` resonant triad is assigned uniquely to one of

```text
HH, LH, HL, CC.
```

The differentiated commutator is the fifth class `Com`; there is no unnamed remainder. The output fibre recomposes exactly and the fixed support collars do not depend on final cutoffs.

### L5 — Signed finite filtered-vorticity and critical shell ledger — algebra checked; physical instantiation open

Round 26 proves a finite signed weighted identity with separate coordinates

```text
HH, LH, HL, CC, Com, lower boundary, upper boundary.
```

Positive parts are not inserted into the identity. It also proves the division-free critical weight relation

```text
weight · vorticityEnergy
= criticalVelocityWeight · velocityEnergy
```

from the declared frequency-square meanings.

Still required:

```text
derive every SignedCriticalShellCell from the actual time-dependent Galerkin PDE;
prove uniform critical norm equivalence for the fixed dyadic partition;
identify every lower and upper cutoff atom physically.
```

The homogeneous critical route explicitly excludes the zero mode; L1/L22 restore arbitrary periodic means.

### L6 — Pair-input-frequency diffusion coercivity — checked exact algebra

For each interaction cell with input eigenvalues `λL,λR` and shell floor `κ`, prove

```text
κ ≤ λL,
κ ≤ λR
⇒
2νκ A ≤ ν(λL+λR)A.
```

The damping remains attached to both inputs before a high–high product collapses to low or zero output frequency.

## C. Load-bearing nonlinear estimates

### L7 — Duplicate-free physical tax ledger — ownership checked; coefficients open

Round 26 defines unique tax owners

```text
HH-good, HH-bad, LH, HL, CC, Com, kernel, tail, boundary
```

and proves that erasing ownership reconstructs the original total exactly. This is the analytic analogue of Round 25’s duplicate-free support theorem.

Each owner must now prove a physical estimate

```text
Fi⁺ ≤ ηi D + Ai + Bi Xint
```

with constants independent of shell `q`, shell cutoff `Q`, Galerkin cutoff `N` and finite maximal time `T*`.

Every remainder must be classified as

```text
data-controlled, time-integrable, small, telescoping
```

and ultimately reduced to the Grönwall-admissible shape

```text
R = A_T + B · integratedCriticalEnergy.
```

A finite but cutoff-dependent remainder is not admissible.

### L8 — Periodic principal-value strain kernel and Calderón–Zygmund control — open

Construct the periodic Biot–Savart/strain distribution, prove principal-value cancellation, actual spherical moments, the smooth periodic remainder and required `Lp`/difference estimates. Convert the polynomial vorticity cross-product defect into a quantitatively integrable near-field tax.

### L9 — Continuum increment-to-diffusion coercivity — division-free algebra checked; physical inequality open

Round 26 stores

```text
A = d² Z,
Z M = D²
```

and proves

```text
A M = d² D²,
Z=0 ⇒ A=0.
```

No quotient by a possibly vanishing denominator is introduced.

Still required: order, nonnegativity and continuum convolution estimates yielding a one-sided scale-uniform bound of the physical HH transfer by `dD` plus named residuals.

### L10 — Far-field annular packing or Carleson estimate — open

Prove the annular/far-field sum is critically summable with constants independent of cutoffs. A flux-decay statement is useful only after it controls the same continuation norm.

### L11 — Low transport, commutator and subgrid-stress estimate — finite identity checked; quantitative tax open

Round 26 fixes the derivative-placement name `LowAdvectsHigh`, reuses exact periodic self-test cancellation, and proves the finite kernel identity

```text
[P_q,a·∇]b
= finite sum of K_q(y)(a(x-y)-a(x))·∇b(x-y).
```

It also proves exact first-moment scaling under literal displacement rescaling.

The next theorem is the physical bound

```text
Σq 2^{-q}|⟨[P_q,a_low·∇]b_q,b_q⟩|
≤ ηCom D + C Xint + RCom
```

with cutoff-independent constants. This is the preferred first genuine L7 tax.

### L12 — Hysteretic positive-variation estimate — finite charge checked; PDE budget open

Round 26 proves for explicit hysteretic entries

```text
before+h ≤ after
⇒
h ≤ after-before,
```

and hence

```text
sum(entry gaps) ≤ sum(positive rises).
```

Still required: a scale-uniform PDE bound on the full positive variation and the associated bad-state amplitude. Bare component count or empirical residence time is insufficient.

### L13 — Dissipation-wavenumber high-mode condition and critical low reservoir — open

Derive dynamically, rather than assume,

```text
amplitudeq ≤ c ν λq²
```

on high modes, and prove the remaining low-mode reservoir is integrable in the critical budget. Raw three-dimensional Bernstein scaling is one frequency power too large.

### L14 — Uniform residual-tail ratio — open

For every far-field, commutator and cutoff tail, construct an actual ratio

```text
0 ≤ ρ < 1
```

uniform in all cutoffs, then apply the checked geometric-series transport.

## D. One strict critical budget

### L15 — Strict total viscosity margin — open and central bottleneck

Use the unique ownership ledger to sum each coefficient exactly once:

```text
ηtotal = ηHH-good + ηHH-bad + ηLH + ηHL + ηCC + ηCom
         + ηkernel + ηtail + ηboundary
< 1.
```

No source may be hidden in a generic residual or charged under two owners. This is the most concentrated highest-alpha target.

### L16 — Uniform integrated critical inequality — reducer checked once L7–L15 exist

Derive uniformly in `Q,N`:

```text
XQ,N(t) + (1-ηtotal) DQ,N(0,t)
≤ XQ,N(0) + A(t) + B ∫₀ᵗ XQ,N(s) ds.
```

### L17 — Non-circular continuous Grönwall — reducer checked

Obtain a finite critical bound on every finite interval without placing the target critical supremum, BKM integral or equivalent continuation criterion on the right.

## E. Infinite cutoffs and restart

### L18 — Shell cutoff `Q→∞` — open analytic producer

Prove convergence strong enough to recover the complete shell sum and all named signed source identities and tax allocations.

### L19 — Galerkin cutoff `N→∞` — open analytic producer

Pass to a physical periodic solution with enough strong convergence for the nonlinear term, initial trace and critical norm.

### L20 — Lower semicontinuity and absorbed-budget preservation — reducer checked

The positive dissipation and strict margin must survive the limit. Absorption occurs before taking weak limits.

### L21 — Pressure/smoothness recovery and critical restart — open physical instance

Recover smooth periodic pressure, bootstrap the velocity, and use the bounded critical norm to contradict finite maximal time.

### L22 — Uncenter arbitrary periodic data — open analytic instance of L1

Construct the continuum mean and verify the Galilean transformation on the physical carrier.

### L23 — Literal Fefferman witness and audit composition — checked reducer

The existing end-to-end theorem converts the physical path inputs into the exact periodic Clay witness. No additional terminal receipt is needed.

## Highest-alpha priority after Round 26

The immediate sequence is:

```text
L3 continuum-real finite ODE instance and global finite existence;
L5 physical signed critical-shell instantiation;
L11 first cutoff-independent low-advection/Com tax;
L8–L10 and L12–L14 remaining physical taxes;
L15 strict unique-owner viscosity certificate.
```

The bottleneck remains

```text
physical L7 coefficients → L15 ηtotal<1.
```

A result counts as progress only when it inhabits a physical cutoff-independent estimate, completes a required analytic instance, or supplies a finite quantified counterexample that removes a false route.
