# Clay Sprint 34 Direction Mixing and Replenishment Frontier

Sprint 34 corrects the Sprint 28 direction-mixing story.  The frozen
eigenframe calculation is useful, but it is not the full Navier-Stokes angle
dynamics.

## Frozen Eigenframe

For vorticity direction:

```text
xi = omega / |omega|
```

the inviscid local direction equation is:

```text
D_t xi = (I - xi tensor xi) S xi
```

If the leading strain eigenframe is frozen, the angle to the leading
eigenvector satisfies:

```text
dtheta/dt =
  - (lambda_1 - lambda_2) * sin(theta) * cos(theta)
```

This is a solved local/toy lemma.  It says strain aligns vorticity with the
dangerous direction.  Strain is not the decorrelator.

## Full NS Correction

For full Navier-Stokes, the strain eigenframe rotates:

```text
dtheta/dt =
  - (lambda_1 - lambda_2) * sin(theta) * cos(theta)
  + FrameRotationTerm
```

The open gate is:

```text
EigenframeRotationControl
```

## Conditional Direction Diffusion

The model operator:

```text
L_K xi =
  nu * 2^(2K) * Delta_{S^2} xi
  - P_perp(S xi)
```

is useful only conditionally.  Full vorticity diffusion for `xi = omega/|omega|`
has amplitude-coupling terms.

Conditional coercivity:

```text
ShellDirectionEquation
+ amplitudeCouplingTermsAbsorbed
+ 2 * nu * 4^K >= lambda_1_max(K)
-> direction perturbations decay at shell K
```

If strain growth is subquadratic:

```text
lambda_1_max(K) <= C * 2^(alpha K)
alpha < 2
```

then high shells become coercive.

## Replenishment Frontier

Even if high-shell direction perturbations decay, nonlinear transfer from low
shells could replenish coherent high-shell alignment.

The hard gate is:

```text
NoCoherenceReplenishmentAtHighShells:
  K >= K_Kolmogorov(nu)
  -> ||P_K nonlinear_omega_source_perp||
     <= C(E0, nu) * ||omega_K||_2^2
```

Equivalently, the coherent non-Beltrami red branch cannot persist:

```text
NonBeltramiCoherentTubeCannotPersist
```

This is now the named Clay-hard frontier for the DASHI NS route.

## Falsification Targets

The next calculations are audits, not promotion evidence:

```text
strain growth:
  lambda_1_max(K) ~ C * 2^(alpha K)
  alpha < 2 is the conditional high-shell coercivity target

replenishment ratio:
  N_K =
    ||P_K nonlinear_omega_source_perp||
    / (||omega_K||_2^2 + epsilon)

red-branch survival:
  rho_K = R^+_(K+1) / (R^+_K + epsilon)
  need sup_K rho_K < 1 / sqrt(2)
```

If `rho_K` stays near `1` on coherent non-Beltrami tubes, the DASHI
pressure/braid route fails cleanly.  If replenishment is dominated by
high-shell direction mixing and `rho_K < 1/sqrt(2)`, the route becomes a
serious conditional NS path.

## Gate3 / YM Guard

Sprint 34 is an NS-frontier correction only.  It records no new Gate3 Mosco
closure, no Yang-Mills nonperturbative rho/leakage control, and no Lean-port
work.

## Boundary

This sprint records the frozen-eigenframe alignment calculation, Beltrami-safe
branch, pressure-downgrade mask, and conditional direction-diffusion
coercivity as toy/algebraic/conditional support surfaces only.  Solved items in
this sprint are not promotion evidence, and external artifacts are context only.
It does not prove eigenframe rotation control, amplitude-coupling absorption, no
coherence replenishment, non-Beltrami tube non-persistence, dynamic residue
decay, Gate3 closure, Yang-Mills uniformity, Lean-port work, or any Clay claim.
