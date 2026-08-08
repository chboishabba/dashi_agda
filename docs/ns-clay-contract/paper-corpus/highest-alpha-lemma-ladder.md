# Highest-alpha lemma ladder to a Clay-submissible periodic proof

[Back to the paper-corpus overview](README.md)

The terminal theorem type and final composition are already present. The highest-alpha work is the shortest dependency chain that can inhabit the physical inputs without adding a non-Clay hypothesis.

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

### L3 — Periodic divergence-free Fourier/Galerkin carrier — open

Construct the exact finite mode set, Leray projection, reality symmetry and Galerkin ODE. Prove preservation of divergence-free and mean-zero structure and exact agreement with the projected periodic PDE.

### L4 — Exhaustive Bony/commutator support theorem — open

For every admitted convolution triad, prove it belongs to exactly one named interaction class:

```text
HH, LH, HL, CC, differentiated commutator.
```

There may be no unnamed remainder. Support collars and constants must be independent of the final shell and Galerkin cutoffs.

### L5 — Finite filtered-vorticity/enstrophy identity — checked exact

Derive from the Galerkin PDE, before abstraction,

```text
ωt - νΔω = FHH + FLH + FHL + FCC + FCom
```

and the critically weighted finite energy identity after periodic integration by parts.

### L6 — Pair-input-frequency diffusion coercivity — checked exact algebra; physical cells depend on L3–L4

For each interaction cell with input eigenvalues `λL,λR` and shell floor `κ`, prove

```text
κ ≤ λL,
κ ≤ λR
⇒
2νκ A ≤ ν(λL+λR)A.
```

The damping must remain attached to both inputs before high–high multiplication collapses to low or zero output frequency.

## C. Load-bearing nonlinear estimates

### L7 — Five physical source taxes uniform in `q,Q,N,T*` — open

For every source `Fi` prove

```text
Fi ≤ ηi D + Ai + Bi Xint
```

with the same critical quantity `X`, explicit `ηi ≥ 0`, and constants independent of shell cutoff `Q`, Galerkin cutoff `N`, selected shell `q`, and finite maximal time `T*`.

### L8 — Periodic principal-value strain kernel and Calderón–Zygmund control — open

Construct the periodic Biot–Savart/strain distribution, prove principal-value cancellation, the actual spherical second-moment identity, the smooth periodic remainder, and the required `Lp`/difference estimates. Convert vorticity-direction defect into a quantitatively integrable near-field tax.

### L9 — Continuum increment-to-diffusion coercivity — open

Upgrade finite Jensen/quadrature estimates to the physical convolution and prove that the weighted increment quantity is controlled by the pair-input viscous dissipation with a scale-uniform coefficient. This is where projected-strain and “emergent damping” papers must survive the affine, sign and scaling counterexamples.

### L10 — Far-field annular packing or Carleson estimate — open

Prove the annular/far-field sum is critically summable with constants independent of cutoffs. A flux decay statement is useful only after this estimate feeds the same continuation norm.

### L11 — Critical commutator and subgrid-stress estimate — open

Use the exact filtered-stress identity and Bony support theorem to control differentiated commutators, low stretching, comparable interactions and subgrid terms without an uncontrolled critical supremum on the right.

### L12 — Hysteretic positive-variation estimate — open

For lower and upper thresholds separated by `h>0`, prove a scale-uniform bound on total positive crossing variation, so that

```text
h · totalEntryCharge
≤
δ · totalPositiveCrossingVariation.
```

A single threshold or a bare list of bad-time components has zero deterministic crossing cost.

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

Sum every named tax and prove

```text
ηtotal = ηHH + ηLH + ηHL + ηCC + ηCom
         + ηkernel + ηexcursion + ηtail
< 1.
```

No source may be hidden in a generic residual. This is the most concentrated highest-alpha target.

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

Prove convergence or compactness strong enough to recover the complete shell sum and all named source identities.

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

## Highest-alpha priority

The bottleneck is not L23. It is the block

```text
L7 → L8/L9/L10/L11/L12/L13/L14 → L15.
```

The best next lemma is whichever produces the largest verified decrease in `ηtotal` while remaining uniform in `q,Q,N,T*`. A paper audit is productive when it either supplies one of those producers or gives a finite counterexample that removes a false route.
