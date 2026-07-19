# Evolved multi-triad compact-Gamma audit

> **Status:** finite Galerkin experiment and exact conditional reduction. Non-promoting.

## Why this tranche exists

The compact-Gamma candidate survived the isolated-triad phase/amplitude sweep:

\[
B_K=\frac{Q_{K,+}}{Q_{K,+}+2\nu D_K}
=\frac{\Gamma_K}{1+\Gamma_K}.
\]

That experiment was deliberately narrow. A single triad does not test angular
spread, competing interactions, packet evolution, shell scaling, or cutoff
stability. The next executable frontier is therefore

```text
isolated triad
  -> support-disjoint rotated multi-triad packet
  -> angularly diffuse target packet
  -> short exact Galerkin evolution
  -> matched shells and cutoffs
  -> empirical theta and c_lambda envelopes.
```

## Packet construction

The audit starts from the exact reality-closed triad

\[
p=(3,0,1),\qquad q=(0,3,1),\qquad k=(3,3,2),\qquad p+q=k,
\]

with the divergence-free polarization used by the matched baseline. Signed
coordinate permutations rotate this triad while preserving its algebra. A
greedy support rule chooses copies whose Fourier supports are disjoint up to
simultaneous sign reversal.

The first copy is the original positive-transfer anchor. Remaining copies are
weaker satellites with deterministic amplitude and phase dispersion. This
keeps the dangerous lane non-vacuous while forcing the target packet to occupy
several projective directions.

Shell 3 is obtained by dyadically scaling the shell-2 wavevectors. Thus the
same dimensionless geometry is compared across shells rather than replacing it
with unrelated examples.

## Angular diffuseness

For target-packet energy weights \(w_k\), define the normalized direction
second moment

\[
M_K=\frac{\sum_k w_k\widehat{k}\widehat{k}^{\mathsf T}}
          {\sum_k w_k}.
\]

The audit records

\[
d_{\mathrm{ang}}=\frac{1}{\operatorname{tr}(M_K^2)}\in[1,3],
\]

and

\[
\left\|M_K-\frac13I\right\|_F.
\]

`angular_participation_dimension = 1` is line-like concentration, while values
toward `3` indicate spread across three spatial directions. This is a geometric
diagnostic, not an isotropy theorem.

## Evolution and normalization

Each packet is evolved with the repository's dealiased, Leray-projected RK4
Galerkin solver. Output times are indexed by parabolic time

\[
\tau=\nu 2^{2K}t,
\]

so shell-2 and shell-3 trajectories are compared over the same normalized time
interval.

For every resolved state the exact compact-Gamma derivative is decomposed into

\[
\dot B_K
=\dot B_K^{\mathrm{target\ nonlinear}}
+\dot B_K^{\mathrm{off\ packet\ nonlinear}}
+\dot B_K^{\mathrm{viscous}}.
\]

The one-sided mechanism totals are

\[
\mathcal E_K=\sum_j\max(-\dot B_{K,j},0),\qquad
\mathcal R_K=\sum_j\max(\dot B_{K,j},0).
\]

The finite audit reports

\[
\theta_{\mathrm{emp}}
=\max_{\Gamma_K\ge\lambda}\frac{\mathcal R_K}{\mathcal E_K},
\]

and

\[
c_{\lambda,\mathrm{emp}}
=\min_{\Gamma_K\ge\lambda}\mathcal E_K.
\]

It also records spreads across matched N32/N48/N64 representations at fixed
candidate, shell, and parabolic time.

## Exact Agda reduction

`NSCompactGammaUniformFamilyResidence.agda` does not promote the numerical
extrema. It proves the conditional family theorem.

For every cutoff, shell, and state, suppose the existing absorbed residence
input gives

\[
X_{K,s}\le B_{K,s}(t_0)+C_{K,s},
\]

where \(X_{K,s}\) is the dangerous-residence expenditure. If one additionally
constructs a common bound

\[
B_{K,s}(t_0)+C_{K,s}\le U
\]

for every member of the family, then

\[
X_{K,s}\le U
\]

uniformly over the declared family. The Agda proof is a direct composition of
the existing replenishment-absorption theorem with the supplied common upper
bound.

The missing mathematics is exactly the construction of that common upper
bound from Navier--Stokes analysis. Sampled values of \(\theta\) and
\(c_\lambda\) do not construct it.

## Running

```bash
python scripts/ns_compact_gamma_multitriad_evolved_audit.py \
  --output-json /tmp/ns-compact-gamma-multitriad.json \
  --search-cutoff 24 \
  --verify-cutoffs 32,48,64 \
  --target-shells 2,3 \
  --triad-counts 2,4 \
  --phase-spreads 0.0,0.35 \
  --target-ratios 2.5 \
  --seeds 0,1 \
  --gamma-threshold 0.5 \
  --minimum-angular-participation 1.3 \
  --verify-count 1 \
  --end-parabolic-time 0.002 \
  --output-count 2 \
  --pretty
```

## Authority boundary

A successful receipt means only that one deterministic finite packet family
survived the declared search, short evolution, shells, and cutoffs. It does not
prove:

- a cutoff- or shell-uniform value of \(\theta<1\);
- a positive analytic \(c_\lambda\);
- compactness of normalized critical profiles;
- a continuum residence theorem;
- a BKM estimate or global regularity;
- the Navier--Stokes Millennium problem.
