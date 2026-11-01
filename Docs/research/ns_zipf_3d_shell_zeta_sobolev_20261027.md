# 3D Fourier lattice → Hurwitz spectral moments → critical Sobolev gates

**27 October 2026.** Companion to `ns_zipf_hurwitz_rank_phase_pressure_maxcut_20261027.md` and the original R734/R735 source in PR #1271. Classical lattice counting and zeta algebra, NOT a 3D NSE regularity theorem or an independent original discovery.

## Exact shell identity

For periodic `k in Z^3 \ {0}`, let `R=||k||_infty`. A full shell has **exactly**
`|S_R| = (2R+1)^3-(2R-1)^3 = 24R^2+2`.

For the **specified** radial per-mode energy `e_k=(R+q)^(-beta)`, `q>=0`, the spectral moment with cube norm weight `R^m` is
`M_m(beta,q) = sum_{R>=1}(24R^2+2)R^m/(R+q)^beta`, `m=0,1,2`.

By p-series comparison the infinite sum converges **iff** `beta>m+3`: at `q=0, beta=m+3` the summand equals `24/R+2/R^3` and diverges; increasing beta by one yields `24/R^2+2/R^4` and converges. These are STATIC summability facts, not dynamic absorption bounds.

For `q=0` and within its convergent domain:
`M_m(beta,0)=24 zeta(beta-m-2)+2 zeta(beta-m)`.

Thus `m=0` (energy) needs `beta>3`, `m=1` (critical H1/2 comparator) needs `beta>4`, and `m=2` (H1/enstrophy comparator) needs `beta>5`. The actual Euclidean Fourier weights obey `R <= |k|_2 <= sqrt(3) R`, giving equivalent FINITENESS for this profile but not identical numerical values.

For `q>0`, the strict-domain Hurwitz binomial identity is
`M_m(beta,q)=24 sum_{j=0}^{m+2} binom(m+2,j)(-q)^(m+2-j) zeta(beta-j,q+1) + 2 sum_{j=0}^m binom(m,j)(-q)^(m-j) zeta(beta-j,q+1)`
for `beta>m+3`. At finite radius `1..N`, replace `zeta(t,q+1)` with the EXACT finite difference `zeta(t,q+1)-zeta(t,q+N+1)` for each term. No RH zero criterion or unjustified pole cancellation is involved.

## Necessary physical-rank join

Ordering **physical wavenumber shells** by `R` yields cumulative mode count `(2R+1)^3-1 ~ 8R^3`. Only under a compatible isotropic/monotone per-mode energy profile does `e_k~R^(-beta)` induce a Zipf modal-energy rank exponent `s=beta/3`. The resulting conditional strict thresholds are `s>1` for finite energy, `s>4/3` for critical H1/2 square, and `s>5/3` for H1/enstrophy square.

An empirical **energy-sorted** Fourier ranking, generic corpus word Zipf exponent, or amplitude-only histogram does NOT automatically provide the frequency ordering or phase/triad correlations. The source-matched six-mode R734 phase reversal keeps every rank magnitude equal and reverses the signed nonlinear transfer. A rank statistic can screen a proposed spectral hypothesis but cannot pay its signed PDE forcing, pressure, tail, localisation and continuation terms.

## Attribution, tests, status and roadmap

Original mathematical credits: elementary 3D integer lattice counting, Fourier/Sobolev definitions and Riemann/Hurwitz zeta plus p-series. Existing DASHI R92/R102 Waleffe signed-helical owner and R691/R734/R735 selected original physical source retain attribution. No new source priority asserted.

New `tests/test_ns_zipf_3d_shell_hurwitz_moments.py`: **six locally passing tests** for the full cube count, exact finite shifted Hurwitz identities at `m=0,1,2`, harmonic critical endpoints and Euclidean/cube norm equivalence. These tests and the earlier five-rank tests are finite algebraic or physical six-mode symbolic computations, NOT exact-PR-head all-suite runs, Agda/Lean kernel certification or an unforced continuum proof.

Next phase: (1) use correct physical frequency↔magnitude join and preserve phase; (2) fit alternate tails only on source-qualified data; (3) test any R734 replacement against the original signed phase/amplitude obstruction; (4) retain four helical channels and actual source-selected pressure/weighted defect; (5) independently handle forced C/D external-2026 theorem versus our unforced periodic problem. The universal original R734 W2 leaf is false and remains retired; the source-written conditional compilers are not refuted.
