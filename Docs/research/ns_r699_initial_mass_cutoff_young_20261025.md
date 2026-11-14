# 2026-10-25 next max-cut — R735 W1 finite-time energy-only obstruction

This extends the physical R699 energy-only test to the ACTUAL
R691/R735 W1 endpoint on the same unforced NS heat-shear trajectory.
Original literature: Navier--Stokes heat/energy identity (Leray),
helical spectral projectors (Lei--Lin--Zhou), source-defined
R691/R735 in DASHI. The explicit finite-time Fourier construction
and exact arithmetic are DASHI's independent work.

For N>=2 let
 u_N(0,x,y,z)=2/sqrt(2N) Σ_(j=1)^N cos(jx)e_z.
At ν=1 this is smooth, real, divergence-free, mean zero, and
(u_N·grad)u_N=0. Thus
 u_N(t)=2/sqrt(2N) Σ_j exp(-j²t) cos(jx)e_z
is an exact unforced NS solution. Let a_N²=1/(2N).
Original Fourier kinetic energy
  E_N(0)=2N a_N²=1.
Integrated enstrophy is
  ∫_0^∞ D_N(t)dt
    =Σ_(j=1)^N 2a_N²*j² *∫_0^∞exp(-2j²t)dt
    =N a_N²=1/2.

For the original physical helical mixed fold with identical canonical
input/output cutoff N, the only nonzero input products at k>0
come from p,q>0. Because
  (H+_(p,0,0) a_N e_z)
    × (H-_(q,0,0) a_N e_z)
    = -i a_N² e_x/2=-i e_x/(4N),
the exact positive k coefficient for k=2,...,N is
  M_k(0)=-i (k-1) e_x/(4N)
and negative -k is its conjugate.
Therefore
  E_M,N(0)=2Σ_(k=2)^N ((k-1)/(4N))²
    =((N-1)(2N-1))/(48N).

At the FIXED positive time T=log2, a Fourier coefficient decays by
the exact rational factor 2^(-j²).
The actual same-output coefficient is
  M_k(T)=-i/(4N) Σ_(p=1)^(k-1)
    2^(-(p²+(k-p)²)) e_x.
The full mixed output L² energy is at most
  ||u_N(T)||_(ell1)² ||u_N(T)||_(ell2)²
    <= [2a_N Σ_j 2^(-j²)]²
       [2a_N² Σ_j 2^(-2j²)]
    <= (2a_N)² * (2a_N²/3)
    =2/(3N²),
using 2^(-j²)<=2^(-j) and 2^(-2j²)<=4^(-j).

Since the exact projected nonlinear forcing vanishes,
the SOURCE R691 global commutator is zero on this trajectory.
R691/R735 W1 therefore reduces EXACTLY to
  W_N(T)+E_M,N(T)=E_M,N(0).
Thus
  W_N(log2)>=((N-1)(2N-1))/(48N)-2/(3N²)
which diverges linearly with N although kinetic energy=1 and the
entire dissipation budget=1/2 at every N. For a fixed T>0 this
disproves the universal energy-only form of the W1 bound across
arbitrary SMOOTH initial data. It does NOT disprove a
data-dependent W1 bound for any fixed datum, does NOT contradict the
H^(3/4) initial ceiling, and is not blowup.

Local exact Fraction tests (4 passed) check the time-decayed
convolution at T=log2, terminal estimate, energy identity, unbounded
lower bound and ordered-pair count. The matching regression is
`tests/test_ns_r735_w1_energy_only_heat_shear_no_go.py`.
No checked-head Agda/Lean kernel proof is claimed.

**Next viable B analytical source:** genuinely signed physical
nonlinear global commutator compensation compatible with R735 W2,
and the true normalized helical H^(3/4) initial-data attachment
to the rational R699 carrier. No energy-only shortcut.

---

# PREFERRED STRONGER RESULT — H^(3/4) SUFFICES, R699 INITIAL WITNESS

The earlier ell1/ell2 Young proof (s>3/2) below is valid, but NOT
optimal and should NOT determine the initial regularity requirement.
The actual mixed product permits an L4/L4 physical-space argument.

Let P_N be the repository's SHARP rectangular Fourier input cutoff
`|p_j|<=N` on T³, and let H± be the **genuine normalized**
curl/helical order-zero Fourier multipliers. On divergence-free
Fourier velocities set
  M_N = (H+ P_N u0) × (H- P_N u0)
with normalized torus Plancherel; this is EXACTLY the source-defined
H+×H- mixed incidence after convolution and output summation.

By the pointwise cross-product inequality and Hölder:
  ||M_N||_(L2)²
    <= ||H+ P_N u0||_(L4)² ||H- P_N u0||_(L4)².
The periodic Calderon--Zygmund/Riesz-transform theorem gives
`||H±||_(L4->L4)<=C_H4`. The **rectangular** sharp partial sum
`P_N` has `sup_N ||P_N||_(L4->L4)<=C_P4`, since each 1D
interval Fourier partial sum is a difference of two modulated Riesz
projections (M. Riesz theorem) and the 3D cube is their tensor
product. These operator bounds are nontrivial classical analytic
facts; do NOT replace them by the FALSE assertion that a Dirichlet
kernel has uniformly bounded L1 norm.

The 3D periodic Sobolev embedding `H^(3/4)->L4` yields
  sup_N sum_k |M_(N,k)|²
    <= (C_H4 C_P4 C_Sob)⁴ ||u0||_(H^(3/4))⁴.

Furthermore by H^0/H^1 interpolation, for u0∈H¹:
  ||u0||_(H^(3/4))⁴ <= ||u0||_(L2) ||u0||_(H¹)³,
so with E0=||u0||²_L2 and D0=||grad u0||²_L2:
  sup_N E_(M,N)(0)
    <= C * sqrt(E0) * (E0+D0)^(3/2),
where C depends only on the fixed universal torus/operator
normalizations and not on N, T, solution history or viscosity.

Restricting the mixed output to R699's canonical nonzero output
cutoff only decreases the nonnegative mass. This PROVES the standard
physical smooth/H¹ initial-data ceiling analytically at lower regularity
than the earlier s>3/2 ell1 proof; it is not a universal positive
R735 W1 for general NONLINEAR evolution.

**Exact computational check:** `tests/test_ns_r699_h34_l4_physical_endpoint.py`
passed 2 independent local SymPy checks. It computes FULL Fourier
coefficients of |H±P_N u|², exact L4 fourth powers and mixed L2
mass for genuine collinear real divergence-free modes, verifies
Hölder exactly and the endpoint s=3/4 exponent. It does NOT prove
the general L4 operator bounds, which are the classical theorems
above.

**Source attribution:** periodic Fourier partial sum boundedness is
M. Riesz/Hilbert-transform theory (see
https://doi.org/10.1007/s00591-025-00390-z and classical harmonic
analysis texts); helical multiplier Lp boundedness derives from
periodic Riesz-transform/Calderon--Zygmund theory; H^s->Lp is
classical Sobolev. The original H± representation retains
Lei--Lin--Zhou attribution. DASHI owns the source-join and fixture.
The original rational-parameter Agda R699 record STILL needs
physical-real helical normalization and norm inequalities before
kernel certification. Do not claim that the SOURCE CODE now contains
the full proof term or that R735 W1/W2 are closed.

---

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
