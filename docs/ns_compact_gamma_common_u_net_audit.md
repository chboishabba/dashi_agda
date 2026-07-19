# Compact-Gamma common-upper finite-net audit

> **Status:** finite Galerkin experiment plus exact conditional Agda reduction. Non-promoting.

## Purpose

The compact-Gamma lane now has the exact bounded potential

\[
B_K=\frac{Q_{K,+}}{Q_{K,+}+2\nu D_K}\in[0,1]
\]

and the integrated replenishment identity used by
`NSCompactGammaReplenishmentAbsorption.agda`.

For a chosen absorption factor \(\theta<1\), define the minimum nonnegative
integrated remainder

\[
C_\theta(I)
=
\int_I (\mathcal R_K-\theta\mathcal E_K)_+\,d\tau,
\qquad
\tau=\nu 2^{2K}t.
\]

Then

\[
\int_I\mathcal R_K\,d\tau
\le
\theta\int_I\mathcal E_K\,d\tau+C_\theta(I).
\]

The existing absorption theorem therefore gives

\[
\text{dangerous residence expenditure}
\le
B_K(t_0)+C_\theta(I)
\le
1+C_\theta(I).
\]

The immediate common-\(U\) problem is consequently reduced to bounding
\(C_\theta\) uniformly over cutoff, shell, and normalized packet profile.

## Normalized packet class

`scripts/ns_compact_gamma_common_u_net_audit.py` reuses the evolved angular
multi-triad constructor and normalizes every initial state to one declared
**target-packet energy**. This removes the trivial growth of the audit quantities
with the number and strength of component triads.

The declared family varies:

- triad count;
- satellite phase spread;
- target-to-input amplitude ratio;
- satellite strength;
- deterministic seed;
- target shell;
- cutoff.

Every state remains reality-closed and divergence-free and is evolved with the
same dealiased Leray-projected Galerkin RK4 solver used by the preceding lane.

## Center, calibration, and holdout net

The finite class is divided by seed into:

1. **centers**, which provide the finite net;
2. **calibration profiles**, used to fit a one-sided oscillation allowance;
3. **held-out profiles**, used only to test the resulting bound.

The state distance is the physical Fourier-coefficient \(L^2\) distance at the
search cutoff. Centers are matched within the same shell and triad-count branch.
For a profile \(u\) and selected center \(u_j\), the empirical audit tests

\[
C_\theta(u)
\le
C_\theta(u_j)+L_{\rm emp}\,\|u-u_j\|_2.
\]

The resulting sampled common upper is

\[
U_{\rm emp}
=
1+\max_j C_\theta(u_j)
+L_{\rm emp}\,\varepsilon_{\rm cover}.
\]

This is a falsification test. The fitted slope is not an analytic Lipschitz
constant and the sampled coverage radius is not a proof that the continuum
profile class is compact.

## Danger constants and residence coefficient

The audit also fits and tests

\[
\Gamma_K\ge\lambda
\Longrightarrow
\mathcal E_K\ge c_\lambda,
\]

and a strict sampled \(\theta<1\). When both survive, the finite candidate
residence coefficient is

\[
\frac{U_{\rm emp}}{(1-\theta)c_\lambda}.
\]

This number is diagnostic only. It is useful for comparing packet classes and
identifying which parameter regimes consume the margin, but it is not a
cutoff-uniform theorem.

## Exact Agda reduction

`NSCompactGammaFiniteNetCommonUpper.agda` proves the following abstract
composition.

Suppose:

- each compact potential satisfies `initialPotential <= one`;
- every profile remainder lies below its chosen center remainder plus one
  oscillation allowance;
- every center remainder lies below one common finite-net upper.

Then every member of the cutoff/shell/state family satisfies

\[
\text{dangerousResidenceExpenditure}
\le
1+C_{\rm net}+C_{\rm osc}.
\]

The theorem does not infer these hypotheses from numerical values. The actual
analytic leaf is the local-oscillation estimate for the integrated remainder,
followed by a finite-net or compactness construction uniform in cutoff and
shell.

## Running

```bash
python scripts/ns_compact_gamma_common_u_net_audit.py \
  --output-json /tmp/ns-compact-gamma-common-u.json \
  --search-cutoff 24 \
  --verify-cutoffs 32,48,64 \
  --target-shells 2,3 \
  --target-packet-energy 0.86 \
  --triad-counts 2,4 \
  --phase-spreads 0.0,0.35 \
  --target-ratios 2.5 \
  --satellite-fractions 0.55 \
  --center-seeds 1 \
  --calibration-seeds 2 \
  --holdout-seeds 3 \
  --gamma-threshold 0.5 \
  --end-parabolic-time 0.001 \
  --output-count 2 \
  --verify-count 1 \
  --pretty
```

## Remaining proof leaves

A successful finite receipt leaves the substantive mathematics unchanged:

1. prove a cutoff-uniform danger expenditure lower bound \(c_\lambda>0\);
2. prove an analytic local-oscillation or continuity estimate for
   \(C_\theta\);
3. construct a finite net or compact profile class with uniform coverage;
4. pass the bound through Galerkin limits and critical-profile compactness;
5. connect the resulting residence estimate to BKM continuation.

No BKM, global-regularity, or Clay promotion is asserted.
