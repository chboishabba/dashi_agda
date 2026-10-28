# R734 exact critical-energy residence: all-data \(L^2_t X_N\), sharpness and late-entry improvement

**Date:** 27 October 2026. **Existing original owner:** R734/R735 sharp-cube dyadic critical fold and full projected periodic Galerkin source. **Status:** analytical consequence of *classical* Fourier Cauchy interpolation and the *classical* unforced Navier–Stokes kinetic energy identity; source-specific dyadic weight sharpness on an exact heat shear. **Verification:** \`tests/test_ns_r734_critical_residence.py\` 13 local symbolic/exact arithmetic cases passed with the pre-existing 9 small-data tests (22 passed total on the local matching copy). No complete repo-head suite, no Agda/Lean kernel run, no all-data strong-solution continuation.

## Exact original-source definitions and hypothesis contract

Take a real, zero-spatial-mean, divergence-free, unforced periodic finite Fourier-Galerkin solution on the 3-torus with viscosity \(\nu>0\), the original cube output projection \(\|k\|_\infty\le N\), and Parseval-compatible Fourier normalisation. Let

\[
E_N(t)=\sum_{0\ne k,\,\|k\|_\infty\le N}|\widehat u_N(k,t)|^2,\quad
H_N(t)=\sum_{k}|k|_2^2|\widehat u_N(k,t)|^2,
\]
\[
X_N(t)=\sum_k w(k)|\widehat u_N(k,t)|^2,\quad
w(k)=2^{\lceil\log_2\|k\|_\infty\rceil}.
\]

For every nonzero integer mode, \(0<w(k)<2|k|_2\). Parseval/Cauchy yields
\[
X_N(t)\le 2\sum_k |k|_2|\widehat u_N|^2
\le2\sqrt{E_N(t)H_N(t)},\qquad
X_N(t)^2\le4 E_N(t)H_N(t).
\]
**The original full Galerkin equation** supplies
\[
E_N'(t)=-2\nu H_N(t);
\]
there is no forcing, no helical decimation, no signed dyadic critical cancellation assumed. Combining gives the exact *all-data, cutoff-uniform global-time integrability* bound
\[
\boxed{\displaystyle
\int_{t_0}^{T}X_N(t)^2\,dt
\le\frac{E_N(t_0)^2-E_N(T)^2}{\nu},\qquad
\int_0^\infty X_N(t)^2\,dt\le\frac{E_N(0)^2}{\nu}\le\frac{E_0^2}{\nu}.
}
\]
This means the **square of the critical-energy scalar** \(X_N=\|u_N\|_{\text{dyadic }\dot H^{1/2}}^2\) is integrable over time. It does NOT mean \(\sup_t X_N\) is bounded independently of \(N\), that the signed W2 derivative is nonpositive, or that \(\int\sqrt{X_N}D_N\) is controlled.

## Sharpness of the numerical constant for the literal dyadic weight

For the *actual* mean-zero, real, divergence-free, nonlinearity-free Fourier heat shear with only \(k=\pm(n,0,0)\), take transverse Fourier coefficients \((0,a,0)\) and their conjugates. It is an exact solution of the full **unforced** Galerkin ODE (the nonlinearity vanishes), and
\[
E_N(t)=2a^2e^{-2\nu n^2t},\qquad
X_N(t)=2w(n)a^2e^{-2\nu n^2t}
\]
for \(N\ge n\). Direct integration gives
\[
\frac{\displaystyle\int_0^\infty X_N(t)^2dt}
{E_N(0)^2/\nu}
=\frac{w(n)^2}{4n^2}.
\]
Choose \(n_j=2^{j-1}+1\), \(j\ge2\). Then \(w(n_j)=2^j\) and
\[
\frac{w(n_j)^2}{4n_j^2}
=\left(\frac{2^{j-1}}{2^{j-1}+1}\right)^2\nearrow 1.
\]
Thus the global bound's **constant 1 cannot be reduced uniformly** for the original dyadic multiplier, **even within exact physical heat shear solutions**. The limit uses increasing cutoffs \(N\ge n_j\). Classical energy/Cauchy supply the inequality; the exact dyadic-bin sharpness is a source-specific calculation, not a Waleffe global theorem.

## Quantified supercritical residence (not pointwise regularity)

For any threshold \(B>0\), using Chebyshev in time and the **same Galerkin trajectory**,
\[
\boxed{\operatorname{meas}\{t\ge t_0: X_N(t)>B\}
\le\frac{E_N(t_0)^2}{\nu B^2}
\le\frac{E_0^2e^{-4\nu t_0}}{\nu B^2}.}
\]
For the earlier small-critical absorption threshold \(B=\nu^2/C_{\rm crit}^2\), the time spent above that threshold has total measure at most \(C_{\rm crit}^4E_0^2/\nu^5\), common to every cutoff. This is **a temporal measure bound only**, not an upper bound for the height or number of distinct critical excursions and not an inequality on the original signed R734 \(\mathcal C_N\).

A synthetic spike \(X_H(t)=H\mathbf1_{[0,M/H^2]}\) has \(\int X_H^2=M\) for arbitrary \(H\). It is used **only as a logical countermodel** showing why an \(L_t^2 X\) estimate does not by itself bound \(\sup X\); it is explicitly not claimed to solve the Galerkin ODE.

## Pareto improvement: strictly better arbitrary-data critical-entry certificate

The previous R734 entry used the weaker averaging estimate
\[
X_N(s_N)\le \sqrt{2}\,E_N(t_0)/\sqrt{z},\qquad z=\nu L,
\]
obtained by separately bounding the energy and integrated enstrophy. Preserve their correlation instead:
\[
\int_{t_0}^{t_0+L}X_N(t)^2dt
\le E_N(t_0)^2/\nu,
\]
so some \(s_N\in[t_0,t_0+L]\) satisfies the **strictly stronger**
\[
X_N(s_N)\le E_N(t_0)/\sqrt{\nu L}
\le E_0e^{-2\nu t_0}/\sqrt z.
\]

Let \(C_{\rm crit}=4\cdot 3^{3/4}C_6C_3>0\), exactly as fixed in the existing R734 small-critical proof, \(B=\nu^2/C_{\rm crit}^2\), and now define
\[
A_{\rm new}=\frac{E_0}{B}=\frac{C_{\rm crit}^2E_0}{\nu^2}
=\frac{A_{\rm old}}{\sqrt2}.
\]
For any \(z>0\), the condition \(X_N(s_N)\le B\) is certified by
\[
t_0(z)=\max\bigl(0,\tfrac1{2\nu}\log(A_{\rm new}/\sqrt z)\bigr).
\]
The common entry terminal time is \(t_0(z)+z/\nu\). Minimising as in the previous accepted calculus proof gives
\[
\boxed{
T_{\rm residence}=
\begin{cases}
A_{\rm new}^2/\nu,&0<A_{\rm new}\le1/2,\\
(1/4+\tfrac12\log(2A_{\rm new}))/\nu,&A_{\rm new}\ge1/2.
\end{cases}}
\]
For zero initial energy the solution vanishes. This improves the previous \(T_*\) for every positive initial energy, with the small-energy bound improved by a factor **2**. The intermediate \(s_N\) can depend on cutoff, but forward invariance of \(X_N\le B\) guarantees at one **common** time \(T_{\rm residence}\)
\[
X_N(T_{\rm residence})\le B,\qquad
X_N(T)+\nu\int_{T_{\rm residence}}^T D_N(t)\,dt\le B
\]
for all cutoffs \(N\) and \(T\ge T_{\rm residence}\).

### Sharper post-entry pointwise decay

Once \(X_N\le B\), the already-proved restricted critical-energy inequality from the R734 owner gives
\[
X_N'+(2\nu-C_{\rm crit}\sqrt{X_N})D_N\le0,
\qquad D_N\ge X_N
\]
(the latter by nonzero integer frequencies, using the same \(w(k)\)). The coefficient is positive. For \(y=\sqrt{X_N}\) use the scalar comparison
\[
y'\le-\nu y+\tfrac12 C_{\rm crit}y^2.
\]
At initial \(y\le\nu/C_{\rm crit}\), comparison with its exact Riccati flow yields
\[
\boxed{X_N(T_{\rm residence}+\tau)\le
\frac{4\nu^2}{C_{\rm crit}^2(1+e^{\nu\tau})^2},\quad \tau\ge0.}
\]
This improves the simpler \(\exp(-\nu\tau)\) critical-energy tail to an asymptotic rate \(\exp(-2\nu\tau)\), **only after the paid entry time**, without claiming a bound on the arbitrary-data early interval. The scalar comparison and Riccati solution are classical.

## Tests, source roots, and exact claim ceiling

\`tests/test_ns_r734_critical_residence.py\` includes 13 locally executed exact-symbolic/arithmetic tests: all nonzero lattice cube modes \([-8,8]^3\), multi-mode Fourier interpolation, interval energy-identity algebra, physical shear integration, dyadic sharpness sequence, residence scalar threshold, improved averaging threshold, optimised recovery monotonicity, Riccati envelope, and explicit nonphysical spike countermodel. Executed with the existing nine \`tests/test_ns_r734_critical_small_data.py\` cases: **22 passed** on locally matched code. These finite checks are **not** a proof of physical Sobolev embedding, a complete exact-GitHub-head regression suite or an Agda/Lean kernel certificate.

Original mathematical authorship: Leray's viscous-energy framework, Fourier/Parseval interpolation and Cauchy–Schwarz, Fujita–Kato (1964) critical small-data theory (DOI 10.1007/BF00276188). Original helical-transfer source: Fabian Waleffe (1992), DOI 10.1063/1.858309, not invoked for the kinetic-energy identity. The **repository-specific** exact cube-dyadic sharpness/entry refinement belongs to this source-focused regression, while the original R734 fold and conditional compiler remain their prior DASHI owners. Palasek, arXiv:2610.29012 (2026-10-21), remains **conditional axisymmetric** research and supplies no unrestricted estimate here. BCH autoformalisation-fidelity PRs Agda #1273 and Lean #88 are independently credited for source-vs-kernel-discrepancy methodology, not counted as PDE producer proofs.

**Open original front:** phase-resolved all-large-data critical production/continuation before \(T_{\rm residence}\); no universal R734 signed W2 payment (counterexample already proved); R369 *actual same-operator* Gram Rayleigh, R406 source/continuum bridge and A1–A3/B7 noncircular continuation are separately unpaid. The all-data \(\int X_N^2\) bound does not by itself prevent singularity because it does not pay \(\int\sqrt{X_N}D_N\) or \(\sup X_N\).


## Exact *physical* no-go for absolute-majorant payment from residence alone

The same real, divergence-free heat shear supplies a stronger discriminator than the synthetic spikes. For fixed kinetic energy \(E_0>0\), choose the exact full unforced velocity \(u(x,t)=(0,A\cos(nx)e^{-\nu n^2t},0)\) on the torus, with \(A\) chosen so that \(E_0\) is constant as \(n\) varies. The nonlinear term \((u\cdot\nabla)u\) vanishes identically, so **actual** nonlinear signed critical production is identically **zero**. But writing \(w_n=2^{\lceil\log_2 n\rceil}\), the same solution gives
\[
X_n(t)=w_n E_0e^{-2\nu n^2t},\qquad
D_n(t)=w_n n^2 E_0e^{-2\nu n^2t}.
\]
The **absolute upper-majorant** used in the small-data proof has integral
\[
\boxed{
\int_0^\infty\sqrt{X_n(t)}D_n(t)\,dt
=\frac{w_n^{3/2}E_0^{3/2}}{3\nu}\xrightarrow[n\to\infty]{}\infty
}
\]
despite the valid sharp residence estimate \(\int X_n^2\le E_0^2/\nu\). Similarly \(\int_0^\infty D_n(t)dt=w_nE_0/(2\nu)\) diverges at fixed \(E_0,\nu\).

Thus the **attempted inference** "all-data \(\int X^2\) bound \(\Rightarrow\) all-data cutoff-uniform absolute \(\int\sqrt X D\) payment" is mathematically FALSE, even on physical same-equation solutions. It does **not** refute a more delicate *signed* cancellation: the true nonlinear production of this shear is exactly zero. This specific asymmetry is why the next proposed W2 argument must preserve signed full-Galerkin mode transfers rather than bounding them by this absolute majorant. The original R734 signed mixed-helicity W2 remains a different, already falsified universal hypothesis.

### Critical regularity scaling firewall

The new bound means \(u_N\in L_t^4\dot H_x^{1/2}\) with a uniform norm bound derived from finite energy. The standard Sobolev embedding gives an \(L_t^4L_x^3\) control, but its Serrin index is
\[
\frac2p+\frac3q=\frac24+\frac33=\frac32>1.
\]
It is **not** a Serrin regularity criterion (where the usual subcritical/critical index is at most one). On \(\mathbb R^3\), the Navier–Stokes scaling gives \(L_t^4\dot H_x^{1/2}\) scaling exponent \(-1/2\), reflecting precisely why concentration is not excluded. The \(\mathbb R^3\) dilation is a scaling discriminator, **not** a claimed literal dilation symmetry on a fixed periodic torus.

Three additional dedicated exact tests validate the physical shear's full NSE equation, the divergent upper-majorant formula, and the Serrin-index arithmetic. The total focused local receipt is now **22 passed** (13 new critical-residence tests plus the earlier nine small-data tests); no exact-head whole-repo pytest, Agda kernel or global-regularity promotion.
