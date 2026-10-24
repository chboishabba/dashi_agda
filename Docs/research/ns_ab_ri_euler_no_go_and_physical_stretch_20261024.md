# 2026-10-24 final max-cut amendment: exact B source equality / critical A source

The original mathematical contributions named below remain attributed
to Jean Leray (projected NS/energy), Jean-Michel Bony (paraproducts),
Bahouri–Chemin–Danchin (LP/Sobolev exposition), classical
Hardy–Littlewood–Sobolev/Sobolev-duality and Gagliardo–Nirenberg
interpolation, and the earlier DASHI theorem owners. This amendment
is a source-coordination and exact finite-algebra integration;
it does **not** claim independent discovery of these foundations.

### B: the ORIGINAL selected critical-touching covariance is welded

At one literal output fibre, Aτ is the existing mixed-helicity
bilinear vector, M=Στ Aτ, rate rτ=ν(|pτ|²+|qτ|²),
n=length fibre and R=Στ rτ. Write
W(X,Y)=2 Re <X,Y>, D=−Στ rτ Aτ. Then exactly
  C=n W(M,D)+R W(M,M)
   =R W(M,M)−n Στ rτ W(M,Aτ).
The existing R685 physical identity supplies
  Στ rτ W(M,Aτ)=W(M,commutator)−W(M,tangent).
R236's original same-carrier six-block theorem supplies
  C=ν(Q_deepOnly+Q_criticalTouching).
COMPOSING THESE ALREADY-EXISTING OWNERS yields
  ν Q_criticalTouching =
      R W(M,M)−n[W(M,commutator)−W(M,tangent)]
      −ν Q_deepOnly.
This is NOW a source-written Agda theorem named
`originalCriticalTouchingIsCorrectedR685Rate` in the
existing `NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact`.
The rate and commutator expressions are exposed as theorem terms
in `NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact`.

This is an exact physical quartic **identity**, not a strict upper
estimate. The finite-fibre coefficients n and R can diverge under
zero-amplitude cutoff padding, as proved by the older B4 adversary.
Thus this mathematical weld does NOT solve B4 or B7; R690 still needs
cutoff-uniform signed spacetime control and actual continuation.

Local exact same-output sample ν=2, k=(64,1,0):
DFL input pair (1,0,0)+(63,1,0),
Core pair (32,0,0)+(32,1,0),
DHH pair (2048,0,0)+(-1984,1,0), plus DFL swap.
Abstract complex Aτ algebraic sample gives C=780398656,
Qdeep=162531800, Qcrit=227667528; both sides νQcrit
equal 455335056. This witnesses the identity on the source-defined
physical rates/classifier but does **not** certify an actual
helical-system realization of the chosen Aτ.

The classical curl-convection defect is also corrected: its
ordered residual cancels after p↔q pairing. The R236 deep far-low
region must merge LH and HL; separate oriented LH and HL do not
cancel. The other two swap-closed regions are DHH and Core.
This is independent of the quartic covariance identity. There is
no universal identity between the quartic covariance and cubic
vortex stretching without nontrivial degree-restoring terms; the
conditional all-amplitudes no-go is source-written in Lean.

### A: no H² logarithmic premise required

For the SAME divergence-free u∈H¹(R³), define
  V=(-ν Δ)^(-1)P div(u⊗u).
Fourier multiplier geometry yields
  ||V||_{dot H^(1/2)}
    <= ν^(-1) ||u⊗u||_{dot H^(-1/2)}.
By dual homogeneous Sobolev embedding
  L^(3/2)(R³) -> dot H^(-1/2)(R³),
and L³ interpolation between L² and L⁶ followed by Sobolev:
  ||V||_{dot H^(1/2)}
    <= (K/ν) ||u||³_L3?  NO: exponent is **2**, precisely
    <= (K/ν) ||u||_L3²
    <= (K/ν) ||u||_L2 ||grad u||_L2.
K collects the standard Sobolev constants. No f=0 forcing
substitution or alternate Fourier field is introduced.
This genuine spatially scale-critical source bound corrects the
prior false conclusion that a divergent *pointwise envelope* made
dot-H^(1/2) control impossible.

For physical nonlinear mild Duhamel W, the frequency-by-frequency
positive heat kernel a exp(-a(t-s)), a=ν|xi|², has mass ≤1.
Weighted Jensen and Tonelli imply
  ∫_0^T ||W(t)||²_{dot H^(1/2)} dt
      <= ∫_0^T ||V(t)||²_{dot H^(1/2)} dt
      <= K² E0²/(2ν³)
under the unforced energy inequality. This is uniform in T.

**Critical caveat:** the spatial dot-H^(1/2) norm is scaling
critical, but its time-L² integral is NOT a continuation norm:
under uλ(t,x)=λu(λ²t,λx), its square scales as λ^(-2).
The energy class also gives only L⁴_tL³_x, with
2/4+3/3=3/2>1, outside critical Serrin. The missing A3 is
a noncircular critical spacetime or uniform-in-time bound.
The canonical Bishop same-solution Fourier transport remains
not kernel-checked. Do not claim Clay A from these estimates.

**Computational receipt:** local independent SymPy/Python checks
of the vector polynomial, merged-region cancellations,
physical six-block compensated identity, three-region H²
diagnostic and H¹ critical-exponent/scaling algebra:
`pytest /tmp/test_ns_ab_maxcut_receipt.py` -> **5 passed**.
PR-head tests and Agda/Lean kernel were NOT executed.
The H²-log file is retained only as a dominated diagnostic;
`scripts/ns_a_critical_h1_dual_sobolev.py` is the new source
analysis note and checks.

---

# 2026-10-24 same-object physical max-cut: exact B class compensation + A Duhamel response

**Original attribution:** The Fourier curl-vorticity identity and heat-kernel convolution bounds are classical Navier–Stokes mathematics (Temam and standard semigroup/Plancherel theory). Bony and Bahouri–Chemin–Danchin own Littlewood–Paley/paraproduct source ideas; DASHI's R63/R236 source owners implement the strict classifier. The new script/calibrations are DASHI integration checks, not new discovery of these identities. OpenAI C/D and Euler theorem source ownership is unchanged. No Clay A/B theorem asserted.

## B: a NONTRIVIAL same-field signed finite Fourier identity

`scripts/ns_physical_vorticity_partition.py`, regression
`tests/test_ns_physical_vorticity_partition.py` (five tests locally
passing on matching scripts, including a mixed-triad fixture).

Let `u_hat(-k)=conj(u_hat(k))`, `k·u_hat(k)=0`, finite Fourier support,
`omega_hat(k)=i k×u_hat(k)`, and normalized T³ Fourier integration.
The actual unforced projected nonlinear velocity source is
`N_hat(k)=-i P_k sum_(p+q=k)(q·u_hat(p))u_hat(q)`.
Curl kills its longitudinal projection, and the actual vorticity
equation gives the GLOBAL physical identity

```text
2 Re sum_k |k|² conj(u_k)·N_k
= 2 Re sum_k conj(omega_k)·i k×N_k
= 2 Re sum_k conj(omega_k)·[
    -i sum_(p+q=k) (q·u_p)omega_q
    +i sum_(p+q=k) (q·omega_p)u_q
  ]
= 2 Re sum_k conj(omega_k)·[
    i sum_(p+q=k) (q·omega_p)u_q
  ].
```

The vorticity transport term vanishes AFTER signed output summation;
no claim is made that it vanishes on each output or each Bony class.
For every generated output (even outside the retained input support),
the script checks the VECTOR CURL identity symbolically. The projection
identity and global kinetic conservation are also checked.

The splitter copies the ACTUAL repository j(k)=ceil(log2(max|k_i|))
with j(0)=0 and authoritative STRICT `j_p+3<j_q`, `j_q+3<j_p`,
and `j_k+3<j_p AND j_k+3<j_q`. Only after this does it apply the
literal R236 deep filters `3j_low<=2j_high` and `5j_k<=4max`.
This is a partition of physical production BY the source classifier,
not a definitionally equal term of R236's distinct critical-production
consumer. The differentiated Com class remains a fifth source,
not silently merged into CC.

**Adversarial six-mode datum:** p=(1,0,0), q=(0,1,64), k=p+q;
transverse real p/q amplitudes and imaginary k amplitude
constructed by cross products, plus conjugate negative modes.
The EXACT source-weighted sums are:

| tag | physical enstrophy P | vorticity transport T | stretching S | curl residual P−T−S |
|---|---:|---:|---:|---:|
| LH | +4 | 0 | 0 | +4 |
| HL | −16392 | −4 | −16384 | −4 |
| HH | +4 | +4 | 0 | 0 |
| CC | 0 | 0 | 0 | 0 |
| TOTAL | −16384 | 0 | −16384 | 0 |

A naive classwise `P_C=S_C` is **FALSE** even in this elementary
real smooth datum. The signed global sum cancels both transport and the
nonzero classwise curl residual. An arbitrary per-class absolute-value
estimate would lose precisely these cancellations. This makes the
existing R690 sum-BEFORE-estimation discipline a mathematical requirement,
although it does not prove an exact R690 mixed-helicity→enstrophy link.

The +8/−8 moderate-scale physical fixture from the previous cut is
retained as independent nonzero calibration. Zero-amplitude mode padding,
strict three-shell collar (j=0 versus j=3), phase reversal and multiple
triad superposition are separately regression-tested.

**Unpaid:** exact phase-preserving general complex-to-existing-rational
carrier theorem; the R236 critical-production/Com source equality
to the full physical production with compensation; R685/R690 mixed
commutator identification; uniform signed quantitative bound and B7
continuation. The present exact tests alone do NOT discharge these.

## A: advance stationary physical response to actual Duhamel, WITHOUT A3

Already proved analytically in `scripts/ns_a_schwartz_fourier_same_object.py`
and its existing owner: for divergence-free physical u∈H¹(R³),
`V_hat(t,xi)=[nu|xi|²]^{-1} F[Pdiv(u⊗u)](t,xi)` obeys
`∫_0^T ||V_hat(t)||²_L²xi dt <= 4 sqrt(2) pi E0² sqrt(T)/nu^(5/2)`
when the unforced energy inequality holds, using the **same u**.

For `a=nu|xi|²>0`, the actual nonlinear Duhamel response of
`F_hat(t,xi)=a V_hat(t,xi)` is
`W_hat(t,xi)=int_0^t a exp(-a(t-s)) V_hat(s,xi) ds`.
The causal positive kernel `h_a(r)=a exp(-ar)1_(r>=0)` has mass <=1
on [0,t]. Jensen/Cauchy–Schwarz:
`|W_hat(t,xi)|² <= int_0^t a exp(-a(t-s)) |V_hat(s,xi)|² ds`.
Integrate t∈[0,T], exchange nonnegative integrals by Tonelli:
```text
int_0^T |W_hat(t,xi)|² dt
 <= int_0^T |V_hat(s,xi)|² (1-exp(-a(T-s))) ds
 <= int_0^T |V_hat(s,xi)|² ds.
```
Integrate in xi to obtain the new full-frequency, finite-time physical
Duhamel norm estimate
```text
||W_hat||²_(L²([0,T]×R³))
 <= ||V_hat||²_(L²([0,T]×R³))
 <= 4 sqrt(2) pi E0² sqrt(T) / nu^(5/2).
```
Choose zero output frequency as the natural null-set representative.
This requires the actual distributional/mild Duhamel identity on
the physical solution, not an unrelated transform variable.
A formal Bishop time/space Fourier inhabitant is still missing.
The nonlinear term's sign in the mild equation does not affect
the squared-norm estimate.

`scripts/ns_a_physical_duhamel_maximal_l2.py` and
`tests/test_ns_a_physical_duhamel_maximal_l2.py` check exact kernel
mass, exact scalar nonstationary input `V=e^{-2t}` at heat rate a=1
(where input squared norm=1/4 and output=1/12), and a rational
sign-changing finite convolution contraction.

**Critical scaling diagnostic:** under NS scaling
`u_lambda(t,x)=lambda u(lambda² t,lambda x)`, W scales similarly
and `||W_lambda||²_(L²_tL²_x)=lambda^{-3}||W||²`.
This estimate does NOT provide a scale-critical Serrin/Kato/BKM
criterion or the signed centered double-resolvent A2, and does NOT
imply global regularity. It is, however, a genuine same-source
time-integrated estimate, more directly applicable to the actual
mild equation than only the stationary response.

## Execution / acceptance
- Local exact Python/SymPy tests: **15 passed**, with one duplicate local test deselected, across the expanded
  physical B suite and A Duhamel tests; source files were ported to
  the GitHub PR branch. The independently added B classwise test
  passed locally as the fifth physical-classifier test.
- No checked-out exact-PR-head test run, no Agda/Lean kernel receipt.
- The mathematical identities follow standard vector calculus and
  Jensen/Tonelli under their listed hypotheses; the executable
  regression alone is not a universal theorem proof.
- A and B unrestricted continuation: **OPEN**. The two direct
  next proofs are original-carrier signed B compensation and physical
  A2 scale-critical domination, NOT redoing Fourier algebra.

---

# Navier–Stokes A/B decisive max-cut: Euler/Ri incompatibility and physical B witness
Date: 2026-10-24

## Provenance, distinctions, and source authority
- **OpenAI**, *Finite time blowup for the Euler equation* (released 2026-09-08), formal source `openai/NavierStokesAndEuler`, `Euler.exists_compact_smooth_euler_singularity`; already audited in DASHI `NSOpenAI2026EulerToClayFourAlternativeBidiExact.agda`. Original result belongs to OpenAI. Lean source metadata claims `sorry_count: 0`; no fresh independent kernel build here.
- **Myong-Hwan Ri**, *Global regularity for the Navier-Stokes equations with application to global solvability for the Euler equations*, arXiv:2601.15685v1 (2026-01-22), https://arxiv.org/html/2601.15685v1; Theorem 1.1, inequality (1.3), proof (3.24)–(3.30), Euler Theorem 4.2. Ri's source claim is not independently certified.
- **DASHI** owns only this compatibility audit and the new exact Fourier witness and accompanying conditional Lean proposition. Neither is an original proof of Navier–Stokes A/B.

## A: exact mathematical no-go for Ri's viscosity-*uniform* theorem
Ri's (1.3), in dimension three, claims for EVERY smooth divergence-free datum u0, all ν>0 and s≥1/2,
  sup_{t>0} ||u^ν(t)||_{H^s}² ≤ C(s) ||u0||_{H^s}²,
where C(s) is independent of ν (indeed asserted to depend only on s).

Take a smooth compactly supported datum u0 producing the unforced Euler C¹ blowup in the OpenAI released theorem. Fix any s>5/2, say s=3. Let T* be the Euler lifespan. On each [0,T] with T<T*, classical viscous-to-inviscid convergence for smooth Euler solutions with the SAME u0 implies u^ν(t)→u^Euler(t) in L² for every fixed t≤T. Boundedness of u^ν(t) in H^s independently of ν and weak compactness then give the Euler norm estimate by lower semicontinuity (one may extract a subsequence and identify its limit in L²):
  ||u^Euler(t)||_{H^s}² ≤ C(s)||u0||_{H^s}², for all 0≤t<T*.
The right side is independent of t. Because s>5/2, H^s(R³) embeds into C¹_b; hence sup_{t<T*} ||∇u^Euler(t)||_∞ < ∞. This contradicts the OpenAI Euler theorem's finite-time C¹ blowup. Thus Ri's stated estimate (1.3) cannot be true with these quantifiers, given the released Euler theorem and standard pre-blowup inviscid convergence.

**Scope:** This is a no-go for the **uniform-in-viscosity bound**, not the assertion that positive-viscosity unforced NS is globally regular for a fixed ν. The proof does not rely on the forced C/D blowup or on a false Euler→NS-blowup implication. Ri's individual frequency identities are NOT thereby falsified; do not import Ri Theorem 1.1/A3 as established. His Section 3 line (3.17) also visibly displays an unweighted gradient sum as a velocity-shell sum; inspect as a possible typographical or substantive issue rather than treating that isolated mismatch as proof of the whole theorem's failure.

**Formal code:** `chboishabba/dashi_lean4/NSEulerRiUniformViscosityNoGo.lean` proves a conditional abstract statement: if a family of viscous norms converges pointwise to the Euler norm and is uniformly bounded, the Euler norm cannot be unbounded. It does **not** formalize H^s→C¹, viscous/inviscid convergence, or import the upstream Euler theorem as a proof term. Source-written; Lean kernel unchecked this cut.

## B: exact nonzero physical spectral production, no fibre-count centering
New exact SymPy regression:
`tests/test_ns_physical_vorticity_production_exact.py`.
Normalized periodic Fourier data at p=(1,0,0), q=(0,1,2), k=p+q=(1,1,2):
  uhat(p)=(0,1,1); uhat(q)=(1,0,0); uhat(k)=i(1,-1,0),
with uhat(-m)=conj(uhat(m)), and all other amplitudes zero.
Every mode is transverse, so u is real, smooth and divergence free.

At t=0, let
  Nhat(m)=-i P_m sum_{p+q=m} (q·uhat(p)) uhat(q),
  omegahat(m)=i m×uhat(m).
Two separately evaluated EXACT finite polynomial expressions agree:
  d/dt ||u||²_nonlinear=2 Re sum_m conj(uhat(m))·Nhat(m)=0,
  d/dt ||omega||²_nonlinear=
     2 Re sum_m |m|² conj(uhat(m))·Nhat(m)=8,
  2 ∫ omega·(omega·∇u) dx [normalized average]=8.

Sign reversal of the imaginary k amplitude yields -8 for both vorticity-production formulas while nonlinear kinetic production stays zero. Inserting high-frequency zero amplitudes does not change either physical observable. This is a nonvanishing concrete bridge between the physical projected nonlinear derivative and vorticity stretching, unlike earlier shear fixtures with identically vanishing physical convection.

The same exact state has E=10, enstrophy=38, palinstrophy=198. Under amplitude u↦a u,
  nonlinear enstrophy production =8 a³,
  viscous dissipation in d/dt||omega||² at ν=1 is 396 a².
At a=50 instantaneous derivative equals +10000. Therefore *no universal fixed scalar coefficient absorbing arbitrary physical stretching only into palinstrophy* can hold for all amplitudes. This is neither a blowup construction nor an obstruction to a more delicate signed/spacetime estimate.

**Owner joins:** R236 (`NSTriadKNPhysicalParabolicCriticalRegionRoutingExact`) owns the shell classifier, R685 (`NSTriadKNR650RateKernelCommutatorEndpointRound685Exact`) owns the physical mixed-helicity commutator-minus-tangent, and R690 (`NSTriadKNR650GlobalSignedRateLiftInputLaplacianRound690Exact`) owns the signed output sum. These currently refer to a mixed-helicity R440-type field, NOT literally the u/omega enstrophy functional above. In particular the old B4 full-fibre defect is disproved. The **remaining exact theorem** is an equality or explicit remainder formula between the original selected R236 critical-production consumer and the Leray-projected u/omega production, with all selected complements compensated. This fixture is the nontrivial mandatory regression for any proposed bridge.

## Execution and acceptance
- Local Python (SymPy 1.14.0): `python -m pytest -q test_ns_physical_vorticity_production_exact.py` → 3 passed (standalone matching test).
- Source-written Lean conditional no-go and B regression committed; no Lean/Agda kernel build, no exact-PR-head pytest in this run.
- A/B claim status: A physical Fourier same-object identification and signed scale-critical A2/A3 remain open; B quantitative global signed estimate and B7 continuation remain open. C/D are released proof donors, not A/B proof closures.

**Next maximum cut:** Construct the exact physical u→ω curl/Leray spectral bridge in the actual existing R236/R685/R690 consumer and its signed compensating remainder. Separately audit Ri's earlier *valid* local-frequency estimates and the existing Bishop whole-space A2 against the Euler-compatible (necessarily viscosity-dependent or differently conditioned) continuation input. Do not create another numbered proof layer.
