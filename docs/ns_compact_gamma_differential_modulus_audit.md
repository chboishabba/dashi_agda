# Compact-Gamma differential-modulus audit

This lane follows the merged pathwise-retention audit. The earlier experiment
fitted finite segment quotients along normalized packet chords. The present
script asks whether those quotients are supported by an actual local
finite-Galerkin differential calculation.

## State manifold and tangent norm

Every interpolated state is renormalized to fixed target-packet energy. A
candidate tangent is projected onto the tangent space

\[
D\langle |u_K|^2\rangle[h]=0.
\]

The scale-normalized tangent norm is

\[
\|h\|_{X_K}^2
=
\|h\|_2^2+2^{-2K}\|\nabla h\|_2^2.
\]

This is a proof-search norm. No claim is made that it already controls every
continuum commutator uniformly.

## Exact Gamma derivative

On the strict positive-transfer branch,

\[
\Gamma_K=\frac{Q_K}{S_K},
\qquad
S_K=2\nu D_K,
\]

and the script computes

\[
D\Gamma_K[h]
=
\frac{DQ_K[h]S_K-Q_KDS_K[h]}{S_K^2}.
\]

The transfer derivative uses the exact Galerkin tangent of the projected
quadratic nonlinearity,

\[
DN(u)[h]
=-P\big((h\cdot\nabla)u+(u\cdot\nabla)h\big).
\]

## Exact escape derivative

Let

\[
m_j(u)=\frac{DB(u)[F_j(u)]}{\nu2^{2K}}
\]

for target nonlinear, off-packet nonlinear, and viscous mechanism fields. The
one-sided escape supply is

\[
\mathcal E_K=\sum_j\max(-m_j,0).
\]

Away from mechanism sign collisions,

\[
Dm_j(u)[h]
=
\frac{
D^2B(u)[h,F_j(u)]+DB(u)[DF_j(u)[h]]
}{\nu2^{2K}}.
\]

The code evaluates the mixed second derivative of the rational compact
potential from the exact first and second variations of cubic `Q` and quadratic
`D`. It then computes

\[
D\log\mathcal E_K[h]
=
\frac{D\mathcal E_K[h]}{\mathcal E_K}.
\]

A compact-potential kink, a mechanism sign collision, zero escape, or a zero
projected tangent is unresolved and fails closed.

## Experimental protocol

The audit:

1. reconstructs center, calibration, and held-out evolved packet profiles;
2. selects dangerous profile times;
3. evaluates normalized path points;
4. tests path, Navier–Stokes RHS, mechanism, viscous, and deterministic random
   packet tangents as configured;
5. fits `L_Gamma` and `L_logE` only on calibration rows;
6. applies the same constants to held-out rows;
7. reconstructs adverse profiles with the exact source seed at matched
   N32/N48/N64 cutoffs;
8. checks analytic derivatives against central finite differences without using
   those differences as the derivative definition.

## Formal bridge

`DASHI/Physics/Closure/NSCompactGammaDifferentialModulus.agda` proves a
division-free reduction. From

\[
|D\Gamma[h]|S^2\le V_\Gamma,
\qquad
V_\Gamma\le L_\Gamma\|h\|S^2,
\]

and positivity of `S²`, it derives

\[
|D\Gamma[h]|\le L_\Gamma\|h\|.
\]

The same theorem surface handles

\[
|D\log\mathcal E[h]|\mathcal E
\le |D\mathcal E[h]|
\le L_{\log\mathcal E}\|h\|\mathcal E.
\]

The Agda theorem composes supplied analytic inequalities; it does not create the
uniform PDE estimates.

## Authority boundary

A successful receipt establishes only exact finite-Galerkin differentiation and
survival or failure on the declared finite tangent family. It does **not** prove:

- uniformity in shell or cutoff;
- control of all tangent directions;
- compact path coverage;
- continuum compactness;
- BKM continuation or global regularity.
