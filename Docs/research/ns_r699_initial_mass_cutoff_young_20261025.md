# Navier–Stokes B: cutoff-uniform initial mixed mass (R699/R724/R735)

**25 October 2026; A/B original programme; source-specific mathematical note.**

## Provenance and theorem status

The helical decomposition and orthogonal projectors are standard curl
spectral theory; retain the historical attribution to Zhen Lei,
Fang-Hua Lin and Yi Zhou, *Structure of Helicity and Global Solutions of
Incompressible Navier–Stokes Equation*, ARMA 218 (2015),
DOI 10.1007/s00205-015-0884-8. Discrete convolution Young,
Cauchy–Schwarz and Sobolev embedding are classical results. DASHI's
contribution in this note is the SAME-LITERAL-MIXED-CARRIER adaptation
and exact finite witness in
`tests/test_ns_r699_initial_mixed_mass_young.py`.

The theorem below is mathematically established by these conventional
inequalities; the Agda R699 record has **not** been inhabited, and there
is no independent kernel certificate or claim of global Clay B.

## Cutoff-uniform initial-data theorem

Let u_0 be a real divergence-free, mean-zero vector field on T^3 with
normalized Fourier coefficients u_p and u_0 in H^s, s>3/2.
Let H±_p be the **genuinely normalized** orthogonal curl projectors on
the transverse Fourier plane:
  H±_p = 1/2(P_p ± i p×/|p|), for p != 0.

For any finite source-mode cutoff Lambda_N (including the literal
canonical cube), let u_p^N = 1_(p∈Lambda_N) u_p. Define the ORIGINAL
helical mixed incidence and fixed-output fold
  A^N_(p,q)=(H+_p u^N_p)×(H-_q u^N_q),
  M^N_k = sum_(p+q=k) A^N_(p,q).

Because projectors are norm-one and |a×b|<=|a||b|, pointwise
  |M^N_k| <= sum_(p+q=k)|u^N_p||u^N_q|.
By discrete Young ell1*ell2→ell2:
  (sum_k |M^N_k|²)^(1/2)
     <= ||u^N||_ell1 ||u^N||_ell2
     <= ||u_0||_ell1 ||u_0||_ell2.
For s>3/2 in dimension 3, Cauchy–Schwarz:
  ||u_0||_ell1²
     <= [sum_p (1+|p|²)^(-s)]
        [sum_p (1+|p|²)^s |u_p|²].
Write C_s²=sum_(p∈Z³) (1+|p|²)^(-s)<∞. Thus
  sup_N sum_k |M^N_k(0)|²
     <= C_s² ||u_0||_(H^s)² ||u_0||_(L²)².

Restricting outputs to the original R699 nonzero cutoff list only
decreases this nonnegative sum. No fibre-cardinality prefactor,
cutoff-dependent constant, terminal state, nonlinear forcing bound,
or viscosity dependence is needed. Numerical factors for Fourier
volume normalization should use the repository's normalized torus
convention.

**This proves the analytical content of R699's
`CutoffUniformInitialMixedMassCeiling` for genuine normalized physical
projectors.** The remaining *formal* join is an actual real/complex
Fourier norm/Young inequality on the exact R699 real trajectory
initial trace, followed by a rational upper bound witness above the
real constant. Do not set the old R699 boolean to true before this
join checks. The present `HelicalModeScalars` Agda record is freely
parametrized; it DOES NOT alone prove |H±v|<=|v| for arbitrary
rational fields and scalars. Its physical normalization needs a real
carrier theorem or explicit projector law.

## Genuine restricted-class W1 result without a new hypothesis

For a *real, smooth unforced heat shear*
  u(t,x,y,z)=f(t,x,y) e_z
with f solving the scalar 2D heat equation (viscosity nu>0), we have
(u·grad)u=0 identically and the physical nonlinear projected force
vanishes. Therefore the ORIGINAL R230/R691 coherent commutator integral
vanishes on this trajectory. From the already-proved R691 identity,
  W_N(T) + E_(M,N)(T) = E_(M,N)(0)
                      <= C_s² ||u_0||_(H^s)² ||u_0||_2²
for EVERY N and T>=0. This fully pays R735's W1 for this specific
nonlinear-force-free solution class only, and is a useful strict
same-source acceptance test. The physical NS global regularity of
these heat shears is of course classical and is NOT a new Clay theorem.

The original global NS R735 W1 remains OPEN because arbitrary
trajectories have nonzero `globalIntegratedCommutator`; R735 W2 also
remains OPEN. In particular no argument here provides B1/B2/B3/B4
signed coercivity, actual R406 B7 transport, or periodic continuation.

## Sharp physical anti-shortcut: energy alone never bounds this endpoint

For each integer N>=2, define the real trigonometric shear
  u_N(x,y,z) = 2/sqrt(2N) sum_(n=1)^N cos(nx) e_z
on T³, with viscosity ν=1. It is smooth, real, transverse,
mean-zero, and solves the UNFORCED Navier–Stokes equation by heat
evolution because (u_N·grad)u_N=0. Its nonzero initial Fourier
coefficients at ±(n,0,0) are a_N e_z with
a_N=1/sqrt(2N), so the NORMALIZED kinetic energy is exactly
  sum_k |u_(N,k)|² = 2N a_N² = 1.

For p,q>0 along the x-axis the TRUE normalized helical projector
formula gives
  (H+_p a_N e_z) × (H-_q a_N e_z)
    = -(i/2) a_N² e_x = -(i/(4N))e_x.
For p,q<0 it is the complex conjugate; opposite-sign ordered
pairs have zero mixed product. For each k=2,...,N the original
same-cutoff fixed-output mixed fold is therefore
  M_k = -(i/(4N))(k-1)e_x,
  M_-k = conjugate(M_k).
The same-N nonzero output mixed-mass sum is EXACTLY
  E_(M,N)(0)
    = 2 sum_(k=2)^N ((k-1)/(4N))²
    = ((N-1)(2N-1))/(48N) ~ N/24.
If all generated outputs through 2N are included instead, the
mass is N/12+1/(24N). In particular no DATA-INDEPENDENT
inequality of the form
  E_(M,N)(0) <= B(E_kinetic(u_N))
for a fixed finite bound function B with B(1)<infinity can hold
uniformly across all smooth initial data. This is a *physical*
helicity-source counterexample to the energy-only shortcut,
not a counterexample to global NS regularity or a universal
data-dependent R699 bound.

For each **fixed** smooth u_N, the H^s-dependent Young bound above
still supplies a finite uniform ceiling across cutoffs. The family
changes its initial data as N changes; never confuse these
quantifiers. The H^s norms of u_N grow, so no contradiction arises.

Three additional independent exact SymPy checks passed:
`tests/test_ns_r699_energy_only_initial_mass_no_go.py`.
They verify true spectral projector orientation, exact
same-cutoff count, fixed L² energy, full-output sum and growth.
No Agda/Lean kernel certification is inferred.

## Exact local verification and acceptance

`python -m pytest -q /mnt/data/test_ns_r699_initial_mixed_mass_young.py`
returned 3 passed (SymPy 1.14.0); the matching committed file is
`tests/test_ns_r699_initial_mixed_mass_young.py`.

Tests: transversality, physical H± norm orthogonality, zero/finite
cutoff upper bound, H^2 finite Young/Cauchy certificate,
quartic amplitude scaling, exact heat-shear R691/W1 endpoint.
These are finite tests, NOT a proof of infinite Fourier Young/Sobolev
or a kernel source receipt; those general steps have the classical
analytic proof above.

## Max-cut priority after this result

- Formal source-reuse: attach REAL helical norm-one laws plus
  cutoff-independent initial trace to original R699/R724,
  without inventing a fresh RNNN record.
- B hard leaf W1: bound the actual globally summed coherent
  nonlinear commutator with a cutoff-independent RHS that is
  compatible with R735 W2 and the R823 negative control.
- B hard leaf W2: strict positive-margin augmented critical
  production/weighted cancellation on the same actual trajectory.
- A remains original Bishop continuum A1/A2 and noncircular A3.
- Source-written != kernel verified != unrestricted Clay B.
