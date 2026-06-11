# Clay Sprint 27 Pressure-Decorrelation Attempt

Sprint 27 records the actual Navier-Stokes attempt after the route compressed
to one conjecture.  No Clay flag changes in this document.

## Single Conjecture

```text
AnalyticBraidResidueDepletionForNS:
  exists R_K, C, r
  such that r * sqrt(2) < 1,
  R_K controls physical shell stretching,
  and R_(K+1) <= r * R_K along actual NS trajectories.
```

This is still open.

## Candidate Definitions

```text
A. CFM direction defect:
   sin(theta_K), where theta_K is the angle between omega_K and e_1(S_K).
   Status: non-circular, correct shape.

B. Beltrami defect:
   ||P_K(omega x u)||_2 / (||omega_K|| * ||u_K||).
   Status: non-circular.

C. Tautological stretching ratio:
   |T_K| / (2^(K/2) * D_K).
   Status: circular; decay is already the Clay estimate.
```

## Computed Positives

```text
1. The enstrophy identity isolates the stretching term.
2. The pressure Hessian rotates strain eigenvectors.
3. Perfect alignment is a local fixed point of the local strain dynamics.
4. The nonlocal pressure Hessian is generically nonzero.
5. A generic misaligned two-tube system decorrelates.
```

These are useful, but they do not prove deterministic all-data decorrelation.

## Surviving Adversary

The surviving adversary is the global parallel-tube configuration:

```text
all vortex tubes align with the same direction n
```

In that case, symmetry can cancel the nonlocal pressure Hessian, and the
pressure-decorrelation mechanism does not fire.

## Exact Remaining Gap

The remaining theorem is nonlinear vorticity-direction mixing:

```text
for all smooth data that are not globally Beltrami,
NS dynamics cannot maintain global parallel-tube synchronization
across all high shells.
```

In receipt terms, the open gate is:

```text
NonlinearVorticityDirectionMixingEstimate
NonBeltramiSmoothDataLowerBoundHsShellK
```

Both remain unproved. Viscous attenuation is diagnostic only; it does not prove
this lower bound.

Equivalently, prove deterministic decay:

```text
R_(K+1) <= r * R_K
with r < 1 / sqrt(2).
```

Diagnostics:

```text
DNS/Kolmogorov-like 2/3 rate: (2/3)*sqrt(2) ~= 0.943, closes weakly.
BT-carrier-only 6/7 rate:    (6/7)*sqrt(2) ~= 1.212, fails.
```

## Workers

```text
W1: residue definition audit.
W2: pressure-Hessian computation audit.
W3: parallel-tube adversary audit.
W4: nonlinear mixing gap audit.
W5: no external-tooling promotion governance.
W6: integration and validation.
```

## Boundary

This sprint records candidate definitions, computations, adversaries, and open
gates.  It does not prove analytic braid-residue depletion, physical stretching
control, deterministic decay below the critical ratio, coherent-tube exclusion,
nonlinear mixing, no blowup, global smoothness, or Clay Navier-Stokes.

Uploaded, preliminary, or external tooling artifacts are context only. They do
not act as Agda authority and cannot flip Gate3, NS, YM, or Clay promotion
flags.
