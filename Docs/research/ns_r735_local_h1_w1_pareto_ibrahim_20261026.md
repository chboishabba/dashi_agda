# NS/B R735 W1 — local H¹ payment and classical small-data global payment

**26 October 2026.** This is a source-attributed partial mathematical advance on the *actual unforced periodic physical Galerkin* W1 carrier, not proof of universal W1/W2, B7 or Clay regularity.

## Original source roots and Pareto / snowball / Ibrahim policy

The underlying 3D Navier–Stokes energy and enstrophy estimates are **classical**, originating in Leray and standard strong-solution theory (e.g. Roger Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, 1979). The helical projection/conditional energy programme belongs to Zhen Lei, Fang-Hua Lin and Yi Zhou, *Structure of Helicity and Global Solutions of Incompressible Navier–Stokes Equation* (2015), arXiv:1505.00142, DOI 10.1007/s00205-015-0884-8. Sobolev, Gagliardo–Nirenberg, M. Riesz uniform rectangular Fourier partial sums, Calderón–Zygmund periodic Leray/helical L⁴ multipliers, Hölder and Young are **classical donor mathematics**. The original DASHI R426/R691/R699/R735 authors own the same-output mixed-product and signed endpoint source definitions. This cut contributes a *derived same-carrier explicit bound*, exact symbolic scalar checks and acceptance barriers—not claims of priority for local 3D strong solutions or those analytic theorems.

**Most relevant latest PRs inspected**: Agda #1255 and Lean #87 already have a source-attributed Miller (2021, DOI 10.1090/bproc/74) anisotropic projected-vorticity continuation interface and finite algebra. Do not duplicate the workers' conditional criterion or call it an unconditional producer. Agda #1240 has an independent VERID physical B4 rate-shift invariance: changing the reference rate does **not** pay its original failing covariance/ED inequality. An earlier worker's A1 Bishop positive-rate-floor work is also separate; none of these is a W1 estimate. The 2015 Lei–Lin–Zhou preprint and later publication are one source root, not multiple independent validations. The Ibrahim first-link/Pareto framework is a *method*, not evidence for a PDE theorem.

## 26 October: CRITICAL ORIGINAL-OUTPUT-SELECTOR RECONCILIATION

The previous physical numerical test calculated the **full mixed
convolution output**, which is NOT the exact source-selected R691/R735
signed consumer when the original Galerkin cutoff retains only
`|k|_infinity<=N`. The original W1 object must be

  M_N := P_N[(H+u_N)×(H-u_N)],
  Q_N := P_N[(H+F_N)×(H-u_N)+(H+u_N)×(H-F_N)],
  C_N := 2 Re <M_N,Q_N>,

where `F_N=-P_N Leray((u_N·grad)u_N)` and both output projections
use the SAME cutoff and physical trajectory. All previous
`H+u×H-u` notation must be understood as followed by this literal
output projection when claiming R691/R735 source identity.

Because P_N is an **orthogonal L² Fourier projection**, the
analytic W1 estimate in this report survives unchanged:
  ||P_N M||_2<=||M||_2,
  ||P_N Q||_2<=||Q||_2,
  |C_N|<=2||P_N M||_2||P_N Q||_2
        <=C||u_N||_(H1)^(7/2)||u_N||_(H2)^(3/2).
This preserves cutoff-independent constants WITHOUT promoting
a selected-output signed identity into an all-output one.

The physical six-mode regression provides an explicit source
counterexample to equating the two signed quantities.
With the SAME real/divergence-free velocity and cutoff N=2,
  C_N(selected 12 nonzero modes) = -9.849528420767435,
  C_N(full 18 nonzero generated modes) = +1.200843362231229.
Their signs are opposite. Central finite-difference differentiation
of the original **selected** mixed energy agrees with the selected
C_N but NOT with the full C_N.
At cutoff N=4, the same field has all 18 generated modes included
and the two sums agree (2.5523607586812247), after independently
recomputing Galerkin nonlinear forcing for N=4.

New selected-output additions in
`tests/test_ns_r735_local_w1_physical_carrier.py` passed
**3 independent local numerical tests**; they use explicit double
precision tolerances, not exact symbolic Fourier certificate.
These are source-sensitive acceptance checks and do not refute
the valid source-independent Hölder estimate or constitute kernel
verification. Previous all-output numerical tests remain valid
Leibniz algebra diagnostics, *not* exact R691 signed-consumer
validation.

## Correct physical carrier and quintic estimate

Take smooth real divergence-free mean-zero periodic Galerkin solutions on the **normalised** 3-torus. Let \(P_N\) be the same rectangular input Fourier cutoff as the original owner, \(\mathbb P\) the Leray projector, \(H_\pm\) the **actual norm-one curl/helical spectral projectors**, and \(\nu>0\). Define the physical velocity \(u_N=P_Nu_N\), projected nonlinear forcing \(F_N=-P_N\mathbb P((u_N\cdot\nabla)u_N)\), mixed field \(M_N=(H_+u_N)\times(H_-u_N)\) and its nonlinear derivative \(Q_N=(H_+F_N)\times(H_-u_N)+(H_+u_N)\times(H_-F_N)\).

The original globally signed coherent commutator at physical Fourier outputs is \(C_N=2\operatorname{Re}\langle M_N,Q_N\rangle\), with source normalisation folded into a universal constant \(C_W\), and with the original output selector applied to both fields. The original R691 endpoint reads \(W_N(T)+E_{M,N}(T)=E_{M,N}(0)+\int_0^T C_N(t)\,dt\).

The cutoff-uniform operator bounds and \(H^{7/4}\hookrightarrow L^\infty\cap W^{1,4}\), with \(\|u\|_{H^{7/4}}\le\|u\|_{H^1}^{1/4}\|u\|_{H^2}^{3/4}\), imply

\[
\|M_N\|_2\le C\|u_N\|_{H^1}^2,\quad
\|F_N\|_4\le C\|u_N\|_{H^1}^{1/2}\|u_N\|_{H^2}^{3/2},\quad
\|Q_N\|_2\le C\|u_N\|_{H^1}^{3/2}\|u_N\|_{H^2}^{3/2}.
\]
Hence the **improved real physical W1 commutator bound**

\[
\boxed{|C_N(t)|\le C_W\|u_N(t)\|_{H^1}^{7/2}\|u_N(t)\|_{H^2}^{3/2}.}
\]

The last \(H^2\) exponent is \(3/2<2\), so it is time-integrable from the standard *local* \(L_t^2H_x^2\) estimate, unlike the earlier \(H^2\)-to-the-fifth shortcut.

## Explicit cutoff-independent short time, depending only on initial H¹

Write \(E_0=\|u_0\|_2^2\), \(D_0=\|\nabla u_0\|_2^2>0\), \(X_N=\|\nabla u_N\|_2^2\), \(Y_N=\|\Delta u_N\|_2^2\). The classical periodic enstrophy/Gagliardo–Nirenberg/Young argument gives one universal \(K>0\) with

\[
X'_N+\nu Y_N\le K\nu^{-3}X_N^3,\quad X_N(0)\le D_0,\quad \|u_N(t)\|_2^2\le E_0.
\]

Scalar comparison yields \(X_N(t)\le D_0(1-2KD_0^2t/\nu^3)^{-1/2}\). Set \(T_*:=\nu^3/(4KD_0^2)\). Every Galerkin cutoff on \([0,T_*]\) has \(X_N(t)\le\sqrt2D_0\). The *inhomogeneous* norm has \(\|u\|_{H^2}^2=E+2X+Y\), and integration yields

\[
B_2(T)=T(E_0+2\sqrt2D_0)+\frac{D_0+2\sqrt2K\nu^{-3}D_0^3T}{\nu},
\qquad
\int_0^T\|u_N\|_{H^2}^2dt\le B_2(T).
\]

With \(E_{M,N}(0)\le C_M\|u_0\|_{H^{3/4}}^4\le C_M(E_0+D_0)^2\) from the physical R699 Sobolev product bound, Holder now proves the **cutoff-independent local R735 W1 bound**

\[
\boxed{W_N(T)+E_{M,N}(T)\le C_M(E_0+D_0)^2
+C_W(E_0+\sqrt2D_0)^{7/4}T^{1/4}B_2(T)^{3/4}}
\quad (0\le T\le T_*).
\]

If \(D_0=0\), mean-zero incompressibility makes \(u_0\equiv0\); the estimate is trivial.

## Additional **all-time** bound for the classical small-H¹ subclass

If the **initial enstrophy** satisfies \(D_0\le\nu^2/\sqrt{2K}\), then the inequality \(Y_N\ge X_N\) and the same exact energy differential inequality give \(X'_N+(\nu/2)Y_N\le0\) on every Galerkin trajectory, hence \(X_N(t)\le D_0e^{-\nu t/2}\). This is the classical small-data 3D strong-solution mechanism, **not** an arbitrary-data theorem.

Kinetic energy decays \(E_N(t)\le E_0e^{-2\nu t}\), with \(\int_0^\infty X_N\,dt\le E_0/(2\nu)\) and \(\int_0^\infty Y_N\,dt\le 2D_0/\nu\). Thus

\[
\int_0^\infty\|u_N\|_{H^2}^2dt
\le \frac{3E_0/2+2D_0}{\nu}=:B_\infty.
\]

Use \(\|u_N\|_{H^1}^2\le(E_0+D_0)e^{-\nu t/2}\) and weighted Hölder with exponents 4 and 4/3:

\[
\boxed{\int_0^\infty |C_N(t)|dt
\le C_W(E_0+D_0)^{7/4}
\Big(\frac{2}{7\nu}\Big)^{1/4}B_\infty^{3/4}.}
\]

Therefore \(W_N(T)+E_{M,N}(T)\) has an **explicit uniform-in-cutoff and uniform-in-time** ceiling for **the sufficiently small initial-H¹ class**, namely

\[
\boxed{
W_N(T)+E_{M,N}(T)\le C_M(E_0+D_0)^2+
C_W(E_0+D_0)^{7/4}
\Big(\frac{2}{7\nu}\Big)^{1/4}
\Big(\frac{3E_0/2+2D_0}{\nu}\Big)^{3/4}
}
\quad (N\ge1,T\ge0).
\]

**Scope firewall:** this pays the *physical analytic W1 inequality* only on a known classical small-data class. The general R735 W1 record applies to all source-selected trajectories; its Agda rational helical-scalar carrier is not automatically the normalized complex Hilbert carrier used here. No original Agda W1 record has been kernel-inhabited; W2, B7 and global large-data Navier–Stokes regularity remain open. Re-starting the local bound at arbitrary times without uniform H¹ control is circular.

## Executable receipt and priority

`scripts/ns_r735_local_w1_h1_majorant.py` and `tests/test_ns_r735_local_w1_h1_majorant.py`: **10 local SymPy tests passed**, checking exact comparison ODE, cutoff-independent lifetime, inhomogeneous H² budget, Sobolev and Holder exponents, small-data absorption, all-time weighted Hölder and a numerical-rational sample. Tests verify only the **scalar assembly**, not the cited functional-analysis lemmas or their Agda representation. No Agda/Lean kernel, exact-GitHub-head CI or Clay proof is claimed.

**Next Pareto max-cut:** for *general* data, source-specific signed cancellation between R735 W1 and W2 is essential; neither local nor small-data boundedness controls \(\sup_{T,N}\int C_N\) on arbitrary large data. Other frontier: A1 Bishop-real same-kernel/Gram identification, A2 low/high same-trajectory majorants, and A3 critical continuation; avoid duplicate conditional Miller/Lean #87 work. Preserve separate prior-art roots, proof status, and primary author attribution.


## Additional physical same-object contact

`tests/test_ns_r735_local_w1_physical_carrier.py` uses the ACTUAL
finite Fourier Galerkin projected nonlinear forcing on a real
transverse six-mode field, source-normalized helical projectors, and
both ordered cross-product derivatives. The exact finite polynomial
structure `M(u+eps F)=M(u)+eps Q(u,F)+eps²M(F)` passes at three
signed perturbations. A central finite difference also agrees with
the mixed energy nonlinear derivative `2 Re<M,Q>`, including the
physical Leray projection and conjugate reality constraints.

This is a NUMERICAL same-object contact regression, not a proof
of the Sobolev multiplier inequalities or Agda R691 type equality.
Combined with the ten exact scalar SymPy checks, **15 local tests passed across the independent local runs**: ten exact scalar algebra, two full-output numerical Leibniz contacts, and three source-selected numerical contacts.

## 26 October: NEW primary-source Pareto/snowball screen (claim-root firewall)

**Stan Palasek**, *A logarithmic regularity criterion for the
axisymmetric Navier--Stokes equations*, arXiv:2610.29012v1,
original 21 October 2026:
https://arxiv.org/html/2610.29012v1
Original Theorem 1.1 requires axisymmetry, R³ H² divergence-free
initial data, initial circulation Gamma_0 in L∞, and a time-uniform
near-axis bound |Gamma(t,r,z)|<=c_*(log(1/r))^(-5/4).
The improvement from the prior Lei--Zhang exponent 2 and Wei 3/2
stems from a sharper square-root-of-log-scales stretching estimate.
It is a conditionally published preprint theorem under axisymmetry;
it cannot be imported as a generic 3D periodic R735 W2 payment.
Original historical roots and source dates remain distinct.

**Ken Nakashima**, *Toward Global Regularity ... Signed Nonlinear
Transfer, Dynamical Quartic Regeneration, and Viscosity-Conditioned
Fourier Correlations*, Part II, author-uploaded 16 October 2026,
page dated/updated 21 October:
https://ken-theory.org/?page_id=25343
This is a more relevant signed-residual TECHNIQUE donor, because
it explicitly retains Galerkin cutoff-uniform closure as an OPEN
condition. The author reports 48 active ordered pathways and
grouped quartic coefficients A_8=2688/5,A_12=0,A_14=-4704/5.
The reported scalar exponential kernel is
 C(t)=336/(5nu)*(exp(-14nu*t)-exp(-8nu*t)).
Our independent EXACT scalar audit confirms its grouped-coefficient
algebra, C(t)<0 for t>0 and
  int_0^infinity C(t)dt=-18/(5nu²).
Crucially **the signs of C times an evolving complex Hermitian
correlation are NOT determined by the scalar kernel sign**; the
full real source amplitude and forcing-path phase must be carried.
The claimed **48-path enumeration is NOT independently reproduced**
in this cut. Neither finite scalar cancellation nor a candidate
conditional Gronwall coefficient is an unconditional source
producer for original R735 W2 or A3.
`tests/test_ns_nakashima_kernel_scalar_audit.py` had
3 locally executed exact SymPy checks. Do not vendor or
attribute the grouped coefficient calculation to DASHI.

**Cross-PR donors, nonpromotion:** The original source selected
Agda R691/R735 owners on master remain canonical. Agda #1255 and
Lean #87 already own Evan Miller's 2021 **conditional** anisotropic
A3 interface and finite algebra; do not re-prove/import it here.
Agda #1240 has independent VERID B4 rate-reference-shift invariance,
which cannot pay the invalid zero-padding-dependent original B4.
Agda #1271 owns this physical restricted W1 certificate only.
Avoid conflating downloaded copies, part I/II/III same-author papers,
and verified original PDE continuation results.

**Updated receipt:** previous 10 exact scalar + 2 physical numerical
tests; three NEW independently run selected-output numerical
checks; three NEW independently run source-scalar Nakashima checks.
Total 18 test cases across the independent cuts.
No Agda/Lean kernel typecheck, exact-GitHub-head whole-suite
run or unrestricted A/B theorem.

