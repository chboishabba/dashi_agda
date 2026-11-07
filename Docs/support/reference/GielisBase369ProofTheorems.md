# Gielis × Base369: mathematically closed theorems and non-promotion proof ledger

**Scope and trust.** These are explicit mathematical proofs for the selected
Gielis radial family, not an Agda kernel acceptance receipt. The companion
`scripts/gielis_base369_symbolic_certificates.py` independently checks the
elementary identities symbolically using SymPy. An external theorem (e.g.,
Rellich compact embedding, min–max or Faber–Krahn) is used *as a known theorem*
and is not thereby a new native Agda formalisation.

Let \(\mathbb T=\mathbb R/2\pi\mathbb Z\) and \(m\in\mathbb N_{>0}\).
Put

\[
 D_m(\theta)=3+\cos(m\theta),\qquad
 r_m(\theta)=2D_m(\theta)^{-1/2},\qquad
 X_m(\theta)=r_m(\theta)(\cos\theta,\sin\theta).
\]

## E01 — same closed-form Gielis specialization (mathematical proof)

The original Gielis formula with \(a=b=1\),
\(n_1=2,n_2=n_3=4\) reads

\[
(\cos^4(m\theta/4)+\sin^4(m\theta/4))^{-1/2}.
\]

For any real \(x\),

\[
 \cos^4x+\sin^4x
 =(1-2\sin^2x\cos^2x)
 =1-\tfrac12\sin^2(2x)
 =\tfrac14(3+\cos4x).
\]

Substituting \(x=m\theta/4\) proves **equality of functions**
with \(r_m\) on ordinary real numbers, not merely visual likeness.
Native Bishop-real sine/cosine and square-root promotion is G02/G03 OPEN.

## E02 — positivity, embedded smooth boundary and dihedral symmetry

Since \(-1\le \cos(m\theta)\le1\), we have
\(2\le D_m(\theta)\le4\), hence

\[
 1\le r_m(\theta)\le\sqrt2.
\]

Thus \(r_m\) is positive, smooth and \(2\pi\)-periodic.
The polar curve is an embedding of the circle: equal nonzero polar
positions determine equal angles mod \(2\pi\).
Its tangent is
\(X'_m=r'_m e_r+r_m e_\theta\); the orthonormal polar
basis gives \(\lVert X'_m\rVert^2=r_m^2+(r'_m)^2\ge1\).
It is therefore regular and bounds the smooth star-shaped domain

\[
 \Omega_m=\{(r,\theta):0\le r<r_m(\theta)\}.
\]

Moreover, \(r_m(\theta+2\pi/m)=r_m(\theta)\) and
\(r_m(-\theta)=r_m(\theta)\), giving the dihedral
\(D_m\) action via rotations and reflections. The discrete Agda owners
prove finite analogues, but a *native continuous* Agda morphism is OPEN.

## E03 — exact area theorem (closed ordinary mathematical proof)

Polar integration gives

\[
 A(\Omega_m)
 =\tfrac12\int_0^{2\pi}r_m(\theta)^2d\theta
 =2\int_0^{2\pi}\frac{d\theta}{3+\cos(m\theta)}.
\]

As \(m\) is a positive integer and the integrand is \(2\pi\)-periodic,
\(\phi=m\theta\) reduces this to
\(2\int_0^{2\pi}d\phi/(3+\cos\phi)\).
On the two tangent-half-angle branches, write
\(t=\tan(\phi/2)\), so
\(d\phi=2dt/(1+t^2)\) and
\(\cos\phi=(1-t^2)/(1+t^2)\). Consequently

\[
\int_0^{2\pi}\frac{d\phi}{3+\cos\phi}
=\int_{-\infty}^{\infty}\frac{dt}{t^2+2}
=\frac{\pi}{\sqrt2}.
\]

Therefore

\[
 \boxed{\forall m\in\mathbb N_{>0},\quad
       A(\Omega_m)=\sqrt2\,\pi.}
\]

This closes the elementary **mathematical** area result. G08 remains
OPEN specifically for the ordinary Bishop-real *Agda* integration proof.

## E04 — differential geometry, normals, curvature and nonconvexity

Differentiating yields

\[
 r'_m=\frac{m\sin(m\theta)}{D_m^{3/2}},\qquad
 r''_m=\frac{m^2(\sin^2(m\theta)+6\cos(m\theta)+2)}
                 {2D_m^{5/2}}.
\]

The (outward) unit normal and signed curvature are

\[
 n_m(\theta)=
 \frac{r_m e_r-r'_m e_\theta}
      {\sqrt{r_m^2+(r'_m)^2}},\qquad
 \kappa_m(\theta)=
 \frac{r_m^2+2(r'_m)^2-r_m r''_m}
      {(r_m^2+(r'_m)^2)^{3/2}}.
\]

At \(\theta=0\), \(r=1,r'=0,r''=m^2/8\), so

\[
 \boxed{\kappa_m(0)=1-\frac{m^2}{8}}.
\]

At \(\theta=\pi/m\),

\[
 \kappa_m(\pi/m)=\frac{m^2+4}{4\sqrt2}.
\]

Thus \(\Omega_3,\Omega_6,\Omega_9\) are *not convex*;
negative curvature at each inward radial indentation also explains
why reflection/grazing constraints need explicit treatment.
Native Agda G09 still OPEN.

## E05 — finite cyclic Fourier projectors (mathematical proof)

For \(a\mid N\), on \(V=\mathbb C^N\), set

\[
(P_af)(j)=\frac1a
\sum_{t=0}^{a-1}f(j+tN/a\bmod N).
\]

For the character \(\chi_k(j)=e^{2\pi i kj/N}\),

\[
(P_a\chi_k)(j)=\chi_k(j)\frac1a
  \sum_{t=0}^{a-1}e^{2\pi i kt/a}
 =\mathbf 1_{a\mid k}\chi_k(j).
\]

All \(N\) characters form an orthogonal basis, so \(P_a\) is
self-adjoint, idempotent, and

\[
 \boxed{P_aP_b=P_bP_a=P_{\operatorname{lcm}(a,b)}}
 \qquad(a,b\mid N).
\]

For \(N=18\), this proves \(P_6P_9=P_{18}\) and
\(P_3P_6=P_6,\ P_3P_9=P_9\) on **all** signals, not merely
sample vectors. Python checks this on all 18 rational basis vectors;
a native Agda scalar/character instantiation is G07 OPEN.

## E06 — sharp 18/36 aliasing and restricted Shannon reconstruction

Let \(f_k(\theta)=\sin(k\theta)\),
\(\theta_j^{(N)}=2\pi j/N\). On the 18-grid,

\[
 f_9(\theta_j^{(18)})=
 f_{27}(\theta_j^{(18)})=0\qquad(0\le j<18).
\]

At \(N=36,j=1\), the respective samples are \(+1\) and
\(-1\). The finite equality and separation witnesses have explicit
source in `GielisBase369NyquistPhase36Exact.agda`.

**Exact restricted reconstruction theorem.** Let

\[
 \mathcal B=\operatorname{span}_{\mathbb C}
 \{e^{ik\theta}: k\in\{0,\pm3,\pm6,\pm9\}\}.
\]

If \(N=36\), the exponents are distinct modulo 36. By the geometric
sum formula, for all \(f\in\mathcal B\),

\[
 c_k=\frac1{36}\sum_{j=0}^{35}
 f(\theta_j^{(36)})e^{-ik\theta_j^{(36)}},\qquad
 f(\theta)=\sum_{k\in\{0,\pm3,\pm6,\pm9\}}c_k e^{ik\theta}.
\]

Thus 36 samples reconstruct this *specified* 7-dimensional space exactly.
The same 18-sample map is not injective because \(f_9\ne0\)
but every sample is zero. This is a genuine restricted
Nyquist–Shannon theorem, **not** Shannon reconstruction for
arbitrary continuous functions nor the PNF semantic analogy.
Agda G10/G19 same-object instantiations remain OPEN.

## E07 — continuum Dirichlet operator and defensible spectral bounds

From E02, \(\Omega_m\) is a bounded \(C^\infty\) planar domain.
The form \(a[u,v]=\int_{\Omega_m}\nabla u\cdot\nabla\bar v\),
with domain \(H_0^1(\Omega_m)\), is closed, densely defined and
coercive by Poincaré. Its Friedrichs realization
\(-\Delta_{D,\Omega_m}\) is positive self-adjoint.
By Rellich compactness the resolvent is compact, hence the spectrum
consists of eigenvalues with finite multiplicity accumulating at \(+\infty\).

Also \(B_1\subseteq\Omega_m\subseteq B_{\sqrt2}\);
domain monotonicity and the first Bessel zero \(j_{0,1}\) yield

\[
 \frac{j_{0,1}^2}{2}\le\lambda_1(\Omega_m)\le j_{0,1}^2.
\]

Because all \(\Omega_m\) have area \(\sqrt2\pi\), the
Faber–Krahn inequality strengthens the lower bound to

\[
 \boxed{\frac{j_{0,1}^2}{\sqrt2}<\lambda_1(\Omega_m)
        \le j_{0,1}^2}.
\]

Strictness holds because none is a disk. This is a complete standard
**paper mathematical** proof using standard Rellich/Friedrichs/
Faber–Krahn theorems; not a self-contained new formalization of those
theorems in Agda. The existing grid41/grid61 solver is not an
error-certified discretization. G11 native owner and G12 numerical
spectral convergence/certified bounds remain OPEN.

## E08 — specular wall angular impulse and ideal power-to-torque law

Let a ray's unit incoming and outgoing momentum directions be \(d,d'\);
a unit surface normal be \(n\). Elastic specular reflection is

\[
 d'=d-2(d\cdot n)n,\quad |d'|=|d|.
\]

The momentum *delivered to the wall*, for photon energy \(E\), is
\(\Delta p_{\mathrm{wall}}=(E/c)(d-d')\).
The ray's own momentum change is its **negative**.
The wall's angular impulse about origin is

\[
 \Delta L_{\mathrm{wall}}=
 (E/c)\,r_{\rm hit}\times(d-d'),
 \quad
 \Delta L_{\mathrm{ray}}=-\Delta L_{\mathrm{wall}}.
\]

For optical source power \(P\) and equal-power emitted rays (N rays,
each representing P/N), averaging all collisions per ray gives the
**conditional ideal** time-averaged wall torque:

\[
 \boxed{\tau_{\mathrm{wall}}=
  \frac{P}{cN}\sum_{i=1}^{N}
  \sum_{h\in\mathrm{wall\ hits}_i}
  \bigl[r_{i,h}\times(d_{i,h}^{\rm in}-d_{i,h}^{\rm out})\bigr]_z}.
\]

Here \(P/c\) has force units and the bracket has metres, so the result
is N·m. The committed ray tracer now uses this wall sign convention
and offers `--power-watts` as a **conditional ideal model**;
no source-power measurement, real wall constitutive optical response,
radiative loss or experimental uncertainty is supplied.
G15 **physical model identity/calibration** still OPEN.

## E09 — polygon-to-smooth reflection, a conditional mathematical lemma

Let a selected smooth reflector segment be \(C^2\), with a family
of chordal polygonal approximants having angular mesh \(h\).
On compact regular subarcs the position discrepancy is \(O(h^2)\)
and the unit-normal discrepancy is \(O(h)\). Assume a fixed finite
number \(B\) of collisions, all transverse with
\(|d\cdot n|\ge\delta>0\), and that competing intersections remain
uniformly separated. The implicit-function theorem and local
Lipschitz continuity of the reflection map yield a constant
\(C_{B,\delta}\) such that

\[
 \max_{1\le i\le B}
 \bigl(|x_{i,h}-x_i|+|d_{i,h}-d_i|\bigr)
 \le C_{B,\delta}h
\]

for sufficiently small \(h\). The summed angular impulse
also converges at this order.
**This theorem explicitly excludes grazing, newly created
intersections, endpoint hits and unbounded reflection counts.**
It does not close G14's *unconditional original apparatus* acceptance
and has not been kernel-checked.

## E10 — identifiability obstruction and prefix-code proof

For the open spiral family

\[
 R_{m,\epsilon}(\theta)=
 \exp\left[(1-t)\log r_0+t\log r_1+
 h_{m,\epsilon}(\theta)
 -(1-t)h_{m,\epsilon}(0)-th_{m,\epsilon}(T)\right],
\]
where \(t=\theta/T\), \(h_{m,\epsilon}=-\tfrac12
\log[(3+\epsilon\cos(m\theta))/3]\),
at \(\epsilon=0\), \(h=0\) for every \(m\).
Thus \(R_{m,0}\) is the same logarithmic spiral for all \(m\):
**parameter recovery is not globally identifiable** (exact G17
counterexample). Both endpoint radii are fixed for every admitted
\(m,\epsilon\).

For operational MDL, put \(q=1000\epsilon\in\{0,\ldots,450\}\).
The codec emits `0` for \(q=0\), independent of \(m\).
For \(q>0\), it emits `1 gamma(m) gamma(q+1)`,
where \(\mathrm{gamma}(n)=0^{\ell(n)-1}\mathrm{bin}(n)\).
The unary length prefix determines how many binary bits to consume,
so each gamma word is self-delimiting. The tagged concatenation is
therefore prefix-free and invertible on *canonical parameters*.
It is a concrete prefix description code, not a proof of universal
Kolmogorov complexity optimality or Shannon source-code optimality.
Full noise, residual and rate-distortion programme G17/G20 OPEN.

## E11 — 27-carrier nonidentification (closed obstruction)

Although \(|C_{27}|=|C_3^3|=27\), the former contains an element of
order 27 while every element of the latter has order at most 3.
Therefore \(C_{27}\not\simeq C_3^3\). A genuine 27-hyperfabric
geometrical realization must carry an explicit product action;
matching cardinalities is not a proof. Positive transport G18 OPEN.

## Exact acceptance boundary

This document **mathematically discharges** E01–E08 and E10/E11
(with stated classical theorem dependencies); E09 is conditional on
nongrazing separated finite reflection histories.
It does **not** certify:
- `agda --safe` or ordinary-real Agda same-object realization (G01–G05);
- native finite/complex Fourier inversion (G07/G10);
- certified convergence/errors of the actual raster PDE solver (G12);
- original HTML SDF Kozyrev mirror parity and recorded source geometry (G13);
- physically calibrated momentum transfer and independent measurements
  (G15/G16/P5);
- empirical confidence intervals, fabrication, replication or a
  field-theoretic Yang–Mills/NS result.

Those remain literal roadmap leaves. The word "closed" here always
means **mathematical proof on the stated carrier**, never automatic
Agda or physical acceptance.


## E12 — Native Bishop quartic algebra (new source, Golden receipt open)

`DASHI/Geometry/GielisBishopPolynomialExact.agda` imports the actual
vendored `Real`, `RealProperties`, and the existing
`BishopPowerSeriesElementaryBridgeExact` sine/cosine owner.

It defines, on Bishop \(\mathbb R_B\),

\[
 Q(c,s)=c^4+s^4,\quad T(c,s)=(c^2+s^2)^2,\quad
 C_4(c,s)=c^4-6c^2s^2+s^4,
\]
and supplies the ring-solver target

\[
 \boxed{4Q(c,s)+3[1-T(c,s)] = 3+C_4(c,s)}
 \qquad(c,s\in\mathbb R_B).
\]

This universal polynomial equality does not require a trigonometric
or \(\pi\) premise. It is a **source-written** use of the repo's
existing `BishopP.ℝ-Solver`, NOT accepted until Agda --safe runs.

To get the actual Gielis inverse-square identity, the selected Bishop
trigonometric functions still owe these *same-object* certificates:

1. \(\cos_B^2x+\sin_B^2x\simeq1\), for the actual Round-11
   power-series data set (not a generic conditional `Set`);
2. \(\cos_B(4x)\simeq C_4(\cos_Bx,\sin_Bx)\), using the actual
   Bishop addition/quadrupling theorem;
3. the positive square-root reciprocal construction and canonical
   Bishop \(\pi\) phase, including 18/36 sample values.

Only after these three witnesses are constructed and the module is
kernel-accepted may G02/G03/G04/G05/G08/G09 be marked GOLDEN.
The earlier K05-PI and Bishop trigonometric interchangeable-series
frontiers are *relevant hard dependencies*, not bypassed by the
unconditional polynomial equality.

## E13 — exact cyclotomic 36-point Fourier algebra

Let \(K=\mathbb Q(\zeta)\) where
\(\Phi_{36}(X)=X^{12}-X^6+1\). The quotient
\(K=\mathbb Q[X]/(\Phi_{36})\) has basis \(1,\zeta,\dots,\zeta^{11}\).
Every \(K\)-element is thus an exact 12-component rational vector.
For \(0\le k,j<36\), define
\(\chi_k(j)=\zeta^{kj}\). Since \(\zeta\) has order 36,

\[
 \sum_{j=0}^{35}\chi_k(j)\overline{\chi_\ell(j)}
 =\begin{cases}36&k=\ell,\\0&k\ne\ell.\end{cases}
\]

`scripts/gielis_cyclotomic36_exact.py` implements reduction by
\(\zeta^{12}=\zeta^6-1\), rational multiplication and the full
36-character Gram calculation. A local exact run verified **1296
ordered character pairs** and coefficient/sample roundtrips for
the seven modes

\[
 \{0,\pm3,\pm6,\pm9\}\pmod{36}
  =\{0,3,6,9,27,30,33\}.
\]

This yields finite exact computational confirmation of Fourier
inversion and selected bandlimited reconstruction *without floating
roots*. The existing native Fourier-resolution owner remains to be
instantiated with this precise cyclotomic scalar and C36 index space;
Python verification is not Agda kernel closure of G07/G10/G19.

## E14 — certified O(m/N) continuum spectral geometry error

Select \(N\) angular sectors. At each angle take the radial value at
its nearest sector centre \(2\pi j/N\), yielding the sectorwise-constant
polar domain \(\Omega_{m,N}\). This is **not** the Cartesian 41/61-node
finite-difference domain.

From E04,

\[
 \left|\frac{dr_m}{d\theta}\right|
 =\frac{m|\sin(m\theta)|}
        {(3+\cos(m\theta))^{3/2}}
 \le\frac{m}{2\sqrt2}.
\]

Every angle lies within \(\pi/N\) of its nearest sample. Using the
rational inequalities \(\pi<22/7\), \(\sqrt2>7/5\),
we therefore have the *rigorous* error constant

\[
 |r_{m,N}-r_m|<\varepsilon_{m,N}
  :=\frac{55m}{49N}.
\]

Because \(r_m\ge1\), for \(\varepsilon_{m,N}<1\),

\[
 (1-\varepsilon)\Omega_m
 \subseteq\Omega_{m,N}
 \subseteq(1+\varepsilon)\Omega_m.
\]

Min–max domain monotonicity of the Dirichlet Laplacian and 2D dilation
scaling imply, for **every \(k\ge1\)**,

\[
 \boxed{
  (1+\varepsilon)^{-2}
  \le\lambda_k(\Omega_{m,N})/\lambda_k(\Omega_m)
  \le(1-\varepsilon)^{-2}.
 }
\]

This is an explicit **constructive geometric spectral convergence
theorem**, with O(m/N) relative bound. At m=9,N=2048 the fully
rational upper absolute relative error is

\[
 \frac{99103455}{9971420449}<0.01.
\]

`scripts/gielis_sector_spectral_certificate.py` outputs rational
endpoint quotients and the first N meeting a target. The local
independent certificate run passed. This CLOSES the continuum
*sector-boundary geometry error* sublemma of G12 on paper;
it does **not** certify the raster five-point finite-difference
eigenvalue error, native Bishop operator semantics, or numerical
eigensolver floating-point error. Those remain G11/G12 leaves.

## E15 — explicit continuum Rayleigh–Ritz upper bound

For any positive \(m\), let
\(u(r,\theta)=1-(r/r_m(\theta))^2\) on \(\Omega_m\).
This \(u\in H_0^1(\Omega_m)\) is nonzero, and direct radial
integration gives

\[
 \int_{\Omega_m}|\nabla u|^2\,dA
 =\int_0^{2\pi}\left(1+\frac{r_m'^2}{r_m^2}\right)d\theta,
 \qquad
 \int_{\Omega_m}|u|^2\,dA
 =\frac16\int_0^{2\pi}r_m^2d\theta.
\]

Using the tangent-half-angle identity

\[
 \int_0^{2\pi}\frac{\sin^2\phi}{(3+\cos\phi)^2}d\phi
 =2\pi\left(\frac3{2\sqrt2}-1\right),
\]

the Rayleigh quotient is

\[
 R_m=\frac3{\sqrt2}
 \left[2+\frac{m^2}{2}
   \left(\frac3{2\sqrt2}-1\right)\right].
\]

Hence \(\lambda_1(\Omega_m)\le R_m\). For \(m=3\),

\[
 R_3=\frac{81}{8}-\frac{15}{2\sqrt2}
 < \frac{1273}{264}=4.82196969\ldots,
\]

where the rational strict bound uses
\(\sqrt2<99/70\), since \(99^2>2\cdot70^2\).
The numerical estimate for the *true* continuum eigenvalue is thereby
rigorously bounded above, independently of any mesh. A local SymPy
integral/rational arithmetic check passed in
`scripts/gielis_rayleigh_spectral_bound.py`.

This improves E07's enclosing-disk estimate for m=3.
The Faber–Krahn lower bound remains
\(\lambda_1(\Omega_3)>j_{0,1}^2/\sqrt2\).
No 41/61 finite-difference convergence certificate is implied.

## E16 — independent first-hit and conditional optical sampling

For the *new* log-Gielis spiral, smooth positions are
\(X(\theta)=r(\theta)(\cos\theta,\sin\theta)\). A ray with
origin \(p\) and unit direction \(d\) meets the smooth curve only
if

\[
 F(\theta)=
  \operatorname{cross}\bigl(X(\theta)-p,d\bigr)=0,
 \quad t=(X(\theta)-p)\cdot d>0.
\]

`scripts/gielis_reflection_parity.py` independently brackets and
solves those roots, selecting the first forward intersection; it
compares the event with the segment-based ray/polyline solver.
A separate local audit of **80 matched rays** (m=3, epsilon=.12)
found maximum positional discrepancy

- 384 segments: \(2.229313372\times10^{-4}\) metres;
- 1536 segments: \(1.249194747\times10^{-5}\) metres,

a roughly **17.85×** improvement upon fourfold refinement.
This is *evidence for convergence on the chosen new scene only*;
a generic root bracketer can miss tangential double roots, and
the initial HTML SDF scene was not available to re-run. G13/G14
original-apparatus parity remains OPEN.

For source uncertainties, `scripts/gielis_optical_statistics.py`
draws matched pseudo-random directions uniformly on the circle.
Under the explicitly stated **IID uniform-angle source model**,
for any sample mean with \(X_i\in[a,b]\), Hoeffding implies

\[
 \Pr\{|\bar X-\mathbb E X|\ge t\}
 \le2\exp[-2n t^2/(b-a)^2].
\]

A ray reflects at most B times and its first-hit position stays within
radius 1.70 m, so total absolute wall angular impulse per unit
ray momentum is in [0,3.40 B] metres. For K designs and two
observables each (hit indicator, absolute wall impulse), setting
\(\alpha_{\mathrm{each}}=\alpha/(2K)\) yields simultaneous
coverage at least \(1-\alpha\) by the union bound.

This closes the *conditional random-angle statistical theorem*;
it does NOT provide a confidence interval for the earlier
deterministic 720-ray grid, nor infer independence of physical
emission events or empirical source calibration. G15/G16 physical
mechanism/measurement and original-scene controls remain OPEN.

### New exact acceptance ledger (E12–E16)

- E12: actual Bishop quartic polynomial proof source; Agda check plus
  genuine Bishop trig/π/sqrt suppliers **OPEN**.
- E13: \(\mathbb Q(\zeta_{36})\) all-pairs/7-mode exact computational
  result **LOCALLY VERIFIED**, native cyclotomic owner **OPEN**.
- E14: all-continuum-eigenvalues sector geometry relative O(m/N)
  mathematical theorem and exact rational certificate **LOCALLY
  VERIFIED**; Cartesian FD error **OPEN**.
- E15: explicit Rayleigh–Ritz first eigenvalue rational bound
  **MATHEMATICALLY CLOSED**, native Bishop/Hilbert formalisation OPEN.
- E16: new-scene first-hit evidence and conditional uniform-ray
  simultaneous intervals **MODELED**, old HTML SDF and measured
  torque/calibration/replication **OPEN**.

### P2 native Bishop reuse clarification

The existing concrete same-object bridge is not hypothetical new Gielis apparatus:

- DASHI/Analysis/BishopRound11ClassicalTrigObjectWeldExact.agda already has compileRound11Pythagorean and compileRound11DerivativeAuthority for the same Round11 data set.
- DASHI/Analysis/TrigonometricPythagoreanSourceAuthorityExact.agda identifies NIST DLMF 4.21.12 as the classical source, and explicitly refuses to promote it to Bishop without the source-function weld.
- GielisBishopPolynomialExact.agda now invokes compileRound11Pythagorean through an explicit witness W, rearranging sin^2+cos^2 to cos^2+sin^2 via BishopP.+-comm; this is a derived conditional transport, not proof that W is inhabited.
- The canonical shared-weld status records sameTrigObjectWeldClosed=false. G02/G03 require this source equality, genuine constructive quadruple-angle and pi/square-root transport. Never fabricate W merely to mark the consumer theorem closed.

### Original Kozyrev optical replay provenance

The historical original was spiral_raymarch_collision_export_forward.html with spiral_collision_events_forward.json and referee_spiral_events.py. The original HTML raymarcher modeled a distance-based finite-thickness stroke, while the independent solver used normal-offset wall thickness. First-forward positional discrepancy: median/max Archimedean 1.414/1.499 mm, logarithmic 1.729/1.832 mm, segmented 1.349/1.431 mm, across 132/132 intersections. That geometrical wall-definition mismatch is a distinct G13 obstruction; all E16 384/1536 segment convergence figures are for a newly selected analytic open-spiral scene and cannot resolve the original apparatus without its actual source and event data.


## E17 — Exact rational certification of the original raster FD operator

The existing five-point interior Cartesian discretisation has grid spacing
\(h=3/(n-1)\) and matrix
\[
A_{m,n}=h^{-2}(4I-B),
\]
with \(B\) the nonnegative nearest-neighbour adjacency matrix of
retained interior cells. **The diagonal remains four** even at
boundary-adjacent sites; missing neighbours have Dirichlet zero values.

For a connected grid graph, \(B\) is irreducible. Given any strictly
positive *rational* vector \(q\), Collatz–Wielandt yields
\[
\min_i\frac{(Bq)_i}{q_i}
\le\rho(B)\le
\max_i\frac{(Bq)_i}{q_i}.
\]
Since the first eigenvalue of \(A\) is
\(\lambda_1=h^{-2}(4-\rho(B))\), it follows that
\[
\boxed{
\min_i\frac{4q_i-\sum_{j\sim i}q_j}{h^2q_i}
\le\lambda_1(A_{m,n})\le
\max_i\frac{4q_i-\sum_{j\sim i}q_j}{h^2q_i}.
}
\]

The new script 'scripts/gielis_raster_fd_positivity_certificate.py'
reproduces the original Gielis Boolean interior mask and five-point
matrix, verifies connectivity, rounds a proposed floating eigenvector
to a strictly positive *integer* vector, then computes the enclosure
using exact rational arithmetic. The solver's numerical accuracy is
therefore **not a hypothesis** of the rational enclosure.

Independent local exact calculations gave these finite-matrix
eigenvalue intervals (decimal endpoints shown rounded):
| Mode | Grid | Lower | Upper |
|---|---|---|---|
| 3 | 41×41 | 4.222626933506416 | 4.222626933827854 |
| 6 | 41×41 | 4.487431020746635 | 4.487431021257153 |
| 9 | 41×41 | 4.6493512607746865 | 4.649351262121115 |
| 3 | 61×61 | 4.289131748459455 | 4.289131749856795 |

This certifies \(\lambda_1\) of the **original finite matrix**.
It does not establish convergence of this *Cartesian raster scheme*
to the continuum spectrum; E14 establishes a different sector-domain
approximation that cannot be silently composed with E17.

## E18 — Identical logarithmic centreline and normal-offset walls

The original canonical owners were located at
[Kozyrev PR #1404](https://github.com/chboishabba/dashi_agda/pull/1404),
head '337aabb00ed54bc1a4c28ada48364cb4dc54d46e'.

- 'kozyrev_first_forward_intersection_referee.py' provides the
  log-family centreline, normal-offset finite-thickness wall sides,
  flat end caps and a 0.003 m forward admission cutoff.
- 'kozyrev_optical_event_ledger.py' supplies the conservation-aware
  power, reflectivity, force and SI torque owner 'RayLedger'.
- 'kozyrev_matched_envelope_html.py' and
  'kozyrev_html_family_ternary_runner.py' consume the HTML
  'window.__spiralAudit' API.

At \(\epsilon=0\), the modulated Gielis spiral satisfies
\[
R_{m,0}(\theta)
=0.75\,e^{b\theta},\qquad
b=\frac{\log(1.55/0.75)}{3\pi}.
\]
This is the *same function* as the PR #1404 'family=log'
definition with inner=0.75, outer=1.55, turns=1.5, rotation=0
and growth=b.

Its tangent and positively oriented left unit normal are
\[
t=R'e_r+Re_\theta,\qquad
n_{\mathrm{left}}
=\frac{-Re_r+R'e_\theta}{\sqrt{R^2+(R')^2}}.
\]
For finite wall thickness \(w\), the normal-offset wall sides are
\[
X_\pm=Re_r\pm\frac{w}{2}n_{\mathrm{left}},
\]
and the same two flat end caps join their endpoints.

The adapter 'scripts/gielis_kozyrev_pr1404_bridge.py'
imports the **original PR #1404 source files**, validates their
actual Git blob hashes, constructs the same parameterised walls
independently and compares first-forward intersections using
the common 3 mm threshold. It also invokes the original
'RayLedger' to verify power-scaled angular-impulse conservation.

The original **HTML stroked-SDF wall** is not automatically
identical to the reference normal-offset wall. Historical
first-forward discrepancies were 1.35–1.83 mm; the original HTML
and event exports still require a direct collision replay.
The original PR source modules have been found, but the browser
export bytes were not available in this checkout.

## E19 — Conditional radiation-pressure torque and paired uncertainty

For optical input power \(P\ge0\), hit radius bounded by \(R\),
at most \(B\) reflections and reflected-power fraction
\(\eta\in[0,1]\), the power at hit \(k\) is at most \(P\eta^k\).
Since incoming/outgoing unit directions obey
\(\|d_{\rm in}-\eta d_{\rm out}\|\le1+\eta\),
triangle inequalities give the exact ideal optical bound
\[
\boxed{
|\tau_{\mathrm{wall}}|
\le\frac{PR}{c}(1+\eta)
\sum_{k=0}^{B-1}\eta^k
\le\frac{2PRB}{c}.
}
\]
The script 'scripts/gielis_optical_force_envelope.py'
computes it over exact rational numbers. For *hypothetical*
\(P=9000\) W, \(R=1.7\) m and \(B=8\), the bound is
approximately \(816.565\,\mu\mathrm{N\,m}\) at \(\eta=1\)
and \(669.920\,\mu\mathrm{N\,m}\) at \(\eta=0.95\).
This does **not** bound thermal, electrostatic, mechanical
or other non-optical forces, or establish measured torque.

For K candidate geometries, 'gielis_optical_statistics.py'
uses common IID uniform source angles for matched comparisons.
For each candidate \(a\) and baseline \(0\), the per-ray
difference \(D_{i,a}=X_{i,a}-X_{i,0}\) is bounded:
focus difference in \([-1,1]\), and absolute impulse difference
in \([-M,M]\) where \(M=2RB\).
Although paired model outcomes within the same ray are dependent,
distinct input ray angles remain independent. Hoeffding plus a
union bound gives simultaneous model-source \(1-\alpha\)
intervals for all \(2(K-1)\) paired differences with
\[
\alpha_{\rm each}=\frac{\alpha}{2(K-1)}.
\]
Neither the source-angle distribution nor the optical power
has been independently measured for the original apparatus.

## Acceptance status for E17–E19

- **E17:** original finite raster FD (lambda_1)
  rigorously enclosed by exact rationals, with
  an independent local numerical reproduction;
  full Cartesian **continuum** mesh convergence OPEN.
- **E18:** original PR #1404 owners and exact baseline
  functional equality identified, finite-thickness
  same-owner adapter source committed; its
  source-pinned execution and original HTML event
  replay OPEN until both refs are materialized.
- **E19:** unconditional mathematical photon-momentum
  envelope under the explicitly stated ideal
  hypothesis and paired Hoeffding model theorem,
  with runnable rational/statistical source;
  material/power measurements and replication OPEN.


### Reproducing E18 with the literal original owner files

The new `scripts/check_gielis_kozyrev_pr1404_original.sh`
performs an explicit, hash-pinned Git fetch of PR #1404
(if `--fetch` is given) and runs reference-wall checks at zero
thickness and at (w=0.156) m using the original Kozyrev
source modules. The command changes no working tree source
and does not require Nix or Chrome:

```bash
bash scripts/check_gielis_kozyrev_pr1404_original.sh --fetch
```

This command is an **acceptance procedure**, not a completed
run receipt. Only the original historical HTML SDF and
collision-export replay can close G13c's remaining geometry
semantics mismatch.


## E20 — Exact SI dimensional and nominal-role transport

The repo already has a **seven-exponent SI carrier** in
`DASHI.Physics.Units.SI`, its explicit metrology/uncertainty
bridge `DASHI.Physics.Units.SIMetrologyBridge`, and the exact
mechanical M/L/T dimension algebra in
`DASHI.Physics.Units.MechanicalDimensionExact`.
The accepted mechanical-to-SI mapping is owned by
`DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact`.
We reuse all four, without defining an independent SI universe.

In base dimensions \((M,L,T)\),

\[
[P]=M L^{2}T^{-3},\qquad [c]=L T^{-1},
\qquad [R]=L,
\]

so the **mechanical torque dimension law** is

\[
 \boxed{[P/c]\,[R]=M L^{2}T^{-2}=[\tau]}.
\]

At the same time,

\[
 [F]=MLT^{-2},\qquad [L_{\mathrm{angular}}]
   =ML^{2}T^{-1}.
\]

The torque SI exponents coincide with the exponents of work/energy,
but **a torque observable is not interchangeable with an energy
observable**. Their conventional SI unit symbols are \(\mathrm{N\,m}\)
(torque) and \(\mathrm{J}\) (energy).
A nominally role-indexed quantity therefore adds information that
dimension exponents alone cannot encode.

The new source
`DASHI/Geometry/GielisSIPerronOwnerWeldExact.agda`
imports the actual SI, mechanical-dimension and metrology modules.
It derives the power/speed/radius dimension, defines distinct
nominal roles for optical power, momentum flux, wall torque, energy
and angular impulse, and retains typed SI measurements with
their uncertainty/source/version fields.

The **exact speed-of-light integer**, by SI definition, is
**not a free numerical model parameter**:

\[
 \boxed{c=299\,792\,458\ \mathrm{m\,s^{-1}}.}
\]

Its canonical in-repo carrier is
`DASHI.Promotion.SIExactConstantParsedCarrierRequest.
canonicalCMetrePerSecondIntegerCarrier`,
which records the literal natural number. The new Agda bridge
uses that existing carrier and proves an integer-value equality by
definitional reduction.

Python `scripts/gielis_si_owner_adapter.py` reads that canonical
Agda carrier and verifies the SI Power/Force/Energy dimensions.
Both the ray simulator and rational optical-force bound now use
the one canonical value, not independent copies.
That source-level check is **not** itself an Agda kernel result.

**Authority boundary:** an exact SI defining constant and
dimensionally valid quantities do not certify a real experimental
power source, material reflectivity, torque sensor, geometric
alignment or measurement uncertainty. No fabricated
`EmpiricalOpticalCalibration` value exists in the new Agda source.

## E21 — Reusing the repository's nonnegative-matrix/Perron machinery

The existing finite matrix owners are:

1. `DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact`:
   *actual* native finite rational sum/distributivity, nonnegative
   influence majorants and a theorem that a uniform row-mass bound
   propagates to all positive matrix powers, conditional on a
   separately supplied nonnegative-powers proof.
2. `DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact`:
   weighted nonnegative matrix powers and row control.
3. `DASHI.Physics.YangMills.BalabanClayUniformPerronContractionExact`:
   distinguishes finite-stage cone contraction from a **uniform**
   modulus; it does not supply the Gielis raster's spectral radius
   or an accepted original Collatz–Wielandt certificate.
4. `DASHI.Core.FiniteTypedBranchingKernelExact`: contains finite
   Perron-root-related *interface* and explicitly records that the
   full spectral-radius theorem is **not** constructed in that owner.

There are also many Collatz/Syracuse *integer iteration* modules,
which must not be confused with **Collatz–Wielandt**, the
positive-matrix variational formula.

The new native source reuses the actual finite influence powers
and the full row-power bound through
`finiteInfluenceRowPowerBoundReuse`, and imports the existing
R³ Hodge/torque owner. It does **not** redeclare a fictitious
Agda proof of spectral-radius Collatz–Wielandt.

For the *original finite Gielis raster*,
E17 already provides the exact accepted mathematical proof:

\[
 \boxed{\min_i \frac{4q_i-(Bq)_i}{h^2q_i}
  \le \lambda_{\min}\!\left(h^{-2}(4I-B)\right)
  \le \max_i\frac{4q_i-(Bq)_i}{h^2q_i}}
\]

for every positive rational vector \(q\), provided the finite
adjacency graph is connected. An independently checked positive
integer \(q\) and exact rational sums make this certificate
constructive at each specific finite matrix.
Transporting this calculation into an *in-repo Agda
Collatz–Wielandt spectral-radius theorem* remains a native proof
leaf if that formal endpoint is demanded; it is not necessary to
re-prove the entire classical Perron–Frobenius theory just to
use a finite positive-rational enclosure.

**Acceptance distinction:** typed SI exponents and the exact
finite rational eigenvalue interval are established on their
respective selected carriers. A continuum FD convergence proof
and independently calibrated physical power/torque remain distinct
gates, not consequences of Perron–Frobenius or SI dimensional typing.


## E22 — Magnitude-level type-indexed optical torque

The actual source DASHI/Geometry/GielisSIPerronOwnerWeldExact.agda
now uses the **existing** Mechanical.Quantity and multiplyQuantity
for rational scalar magnitudes. It constructs typed power,
inverse-speed and radius values and proves the scalar equation

\[
\operatorname{magnitude}(\operatorname{modelOpticalTorque}
  (Q_P,Q_{c^{-1}},Q_R))=(P c^{-1})R.
\]

The same source transports the resulting value through the existing
YangMillsSIScalingEndpointExact.mechanicalQuantityToSI and proves
the same magnitude on the SIIndexedQuantity, not just matching
unit names. The signed dimensionless ray-response parameter g is
then included in a further scalar identity

\[
 \operatorname{magnitude}
 (\operatorname{modelOpticalTorqueWithDeflection}
  (Q_P,Q_{c^{-1}},Q_R,Q_g))
 = ((P c^{-1})R)g.
\]

This distinguishes torque (N m) from energy (J) at the nominal
physical-role level even though both have \(ML^2T^{-2}\).
g can have either sign or vanish. Source-written equalities still
require a native Agda check; no measured watt value is assumed.

## E23 — Continuum eigenvalue length scaling in exact SI

The new GielisSpectralSIScaleExact.agda reuses
Mechanical.inverseAreaDimension, Mechanical.areaDimension,
and YangMillsSIScalingEndpointExact. It proves source-level
MLT/SI dimension equalities and carries a rational-valued
dimensionless eigenvalue times an inverse-area scale onto an
actual SIIndexedQuantity with units \(\mathrm{m}^{-2}\).

For the *continuum* m=3 selected domain, \(r_3\le\sqrt2\)
implies \(\Omega_3\subset(-\sqrt2,\sqrt2)^2\).
The first Dirichlet eigenvalue of this enclosing square is
\(\pi^2/4\); \(\pi>3\) implies
\(\lambda_1(\Omega_3)>9/4\).
E15 supplies \(\lambda_1(\Omega_3)<1273/264\).
Under a Euclidean scaling \(x\mapsto Lx\),
\(\lambda_1(L\Omega_3)=\lambda_1(\Omega_3)/L^2\).
Consequently, given assumed SI length \(L\in[L_-,L_+]\),

\[
 \boxed{\frac{9}{4L_+^2}<
 \lambda_1(L\Omega_3)<
 \frac{1273}{264L_-^2}\;\mathrm{m}^{-2}.}
\]

For hypothetical \(L\in[0.99,1.01]\) m, exact rational
endpoints computed by the new
scripts/gielis_physical_spectral_si.py are

\[
  \frac{22500}{10201}
  <\lambda_1(L\Omega_3)
  <\frac{1591250}{323433}\;\mathrm{m}^{-2}.
\]

No numerical wave frequency follows without selecting and
calibrating a constitutive wave equation and speed.
The native continuum eigenfunction pullback remains OPEN.
Finite Cartesian-matrix eigenvalues are transported separately;
they are not identified with the continuum spectrum.

## E24 — Exact rational assumed SI uncertainty propagation

For explicitly supplied nonnegative intervals
\(P\in[P_-,P_+]\), \(R\in[R_-,R_+]\),
\(\eta\in[\eta_-,\eta_+]\subseteq[0,1]\), and
at most B wall reflections, E19 yields

\[
 \boxed{|\tau_{\mathrm{wall}}|
 \le \frac{P_+R_+}{c}(1+\eta_+)
 \sum_{k=0}^{B-1}\eta_+^k.}
\]

Since signed ray torques may cancel, the only unconditional
lower bound on absolute torque from these inputs is zero.
The associated signed torque lies in \([-\tau_+,\tau_+]\).
scripts/gielis_si_optical_interval.py computes this entirely
with Fraction rationals and the original exact SI c owner.
Its intervals are **model assumptions**, not measurements,
and do not constrain mechanical, thermal, electrostatic or
gravitational non-optical forces.

### E22–E24 acceptance boundary

The magnitude-level Agda terms and numerical source are
committed; exact-head Agda elaboration is still unverified.
E23's continuum scaling is mathematically proved with
standard Dirichlet monotonicity/dilation, not proof of the
actual Cartesian FD-to-continuum limit. E24 does not
construct a measured optical calibration or confidence interval.


## E25 — Bishop-real Gielis quartic from actual same-object trig inputs

The original concrete source
DASHI/Geometry/GielisBishopPolynomialExact.agda now proves
this setoid consequence, for the configured Bishop sine/cosine:

\[
 \bigl(\cos_B(x)^2+\sin_B(x)^2\simeq1\bigr)
 \quad\land\quad
 \bigl(\cos_B(4x)\simeq
  \cos_B(x)^4+\sin_B(x)^4
  -6\cos_B(x)^2\sin_B(x)^2\bigr)
\]
\[
 \Longrightarrow\qquad
 \boxed{4(\cos_B(x)^4+\sin_B(x)^4)
 \simeq 3+\cos_B(4x).}
\]

The proof is a *real* setoid derivation, not a statement-only
record: bishopUnityCorrection is a native Bishop ring-solver proof;
bishopCorrectedQuarticFromPythagorean transports the
Pythagorean equivalence under squaring, negation, multiplication
and addition; bishopGielisConfiguredTrigIdentity composes it
with the previously proved universal quartic normal form and
the selected actual cosine quadrupling.

The input fields belong to BishopGielisConcreteTrigInputs
on the same chosen BishopElementaryPowerSeriesData and
Bishop real angle; an unrelated axiom about a formal terminal
real carrier cannot discharge them. The existing
Round11ClassicalTrigObjectWeldExact Pythagorean compiler
is already consumed for one of the two analytic inputs.
The other continuous same-object cosine quadruple-angle
producer, canonical \(\pi\), positivity/sqrt/area, and exact-head
Agda kernel acceptance still remain open.

## E26 — Native finite rational ground-state edge-square identity

For a symmetric finite raster adjacency matrix \(B\) and
a strictly positive rational vector \(q\), set \(x_i=q_i u_i\).
On each undirected edge \(\{i,j\}\), the following **rational
polynomial identity**, requiring NO spectral theorem, holds:

\[
q_iq_j(u_i-u_j)^2
+2q_iq_ju_iu_j
=q_iq_j(u_i^2+u_j^2).
\]

Summing this identity over any finite edge list and adding
the diagonal potential gives the exact *ground-state transform*

\[
\boxed{
x^\top(4I-B)x
=\sum_i\frac{4q_i-(Bq)_i}{q_i}x_i^2
 +\sum_{\{i,j\}\in E}q_iq_j
    \left(\frac{x_i}{q_i}-\frac{x_j}{q_j}\right)^2.
}
\]

The second term is nonnegative whenever every \(q_i>0\).
Consequently,
\[
\min_i\frac{4q_i-(Bq)_i}{h^2q_i}
\le\lambda_1(h^{-2}(4I-B)).
\]
The complementary upper bound follows by inserting the
positive test vector \(x=q\) into the Rayleigh quotient
and using its weighted-mean bound by the largest row ratio.
**No irreducibility, connectedness or Perron–Frobenius
eigenvector theorem is needed** for this enclosure.

The new Agda
DASHI/Geometry/GielisFiniteGroundStateEdgeExact.agda
actually invokes the existing rational ring solver for the
edge identity, the repo's native nonnegative-square and
nonnegative-scale owners for its sign, and original
finite-sum add/congruence lemmas to prove the identity for
*any finite list of weighted edges*. It does NOT yet
complete the native vertex/adjacency assembly for all
specific raster sites, which remains a separately identified
instance, nor the continuum FD convergence proof.

The original executable raster certificate now checks the
exact ground-state identity for additional rational test
vectors, alongside its already-existing exact positive-vector
rational eigenvalue enclosure. In independent local work,
120 graph/vector instances were checked over exact Python
Fractions with zero algebraic residuals. These are
validation checks, NOT Agda kernel receipts.

### E25/E26 refined acceptance

- E25: nontrivial conditional concrete Bishop-real theorem is
  SOURCE-WRITTEN; cosine quadrupling and the analytic
  Round11 same-object suppliers remain OPEN.
- E26: finite arbitrary-edge-list algebra and positivity are
  SOURCE-WRITTEN; actual raster site/edge enumeration in
  Agda and kernel verification OPEN. The standalone finite
  matrix *mathematical theorem* itself is now elementary and
  independent of a new PF library.
- CI and original HTML scene remain DEFERRED in the active
  work priorities, as requested.


## E27 — Corrected Cartesian FD operator: a qualitative continuum spectral convergence theorem

**Critical discovered exact-target defect.** The original five-point
raster code used the fixed, nonvanishing radial boundary shrinkage
\(10^{-12}\) in *dimensionless normalized coordinates*. Its
mathematical \(h\to0\) limit targets the **shrunken** domain
\(\{|x|<r_m(\arg x)-10^{-12}\}\), not literally \(\Omega_m\).
The code now uses

\[
\delta(h)=\min(10^{-12},h^2)\longrightarrow0
\quad\text{as }h\downarrow0.
\]

At the original \(n=41\) and \(n=61\) grids, \(h=3/(n-1)\)
and \(\delta(h)=10^{-12}\), so all existing finite
certificate grid masks are **exactly the legacy masks**.
At sufficiently small \(h\), the new inward shrinkage
decreases, selecting the *unshrunken* intended domain.

**Theorem (exact-boundary idealization, standard compactness).**
Let \(m\ge1\) be fixed, and define \(S_h\) as the
interior nodes of the Cartesian mesh of width \(h=3/(n-1)\)
inside the exact analytic star boundary satisfying
\(\lvert x_i\rvert<r_m(\arg x_i)-\delta(h)\).
Let \(A_h=h^{-2}(4I-B_h)\) be the original zero-exterior
five-point Dirichlet matrix, including diagonal 4 at all
interior nodes. For every fixed positive integer \(k\),

\[
\boxed{
  \lambda_k(A_h)\longrightarrow
  \lambda_k(-\Delta_{D,\Omega_m})
  \quad (h\downarrow0,\;\text{odd }n\to\infty).
}
\]

This is a **qualitative** theorem; no explicit uniform
error rate or numerical n=41/n=61 continuum error bound
is claimed by this statement.

**Proof.**

1. **Geometry and boundary convergence.** E02 gives a
   compact smooth positive radial embedding, with
   \(B_1\subseteq\Omega_m\subseteq B_{\sqrt2}\).
   The centered grid box \([-1.5,1.5]^2\) therefore
   contains the full domain for every n.
   Since \(\delta(h)\to0\), each fixed compact subset
   \(K\Subset\Omega_m\) is eventually contained in the
   selected grid interior. Every piecewise-constant
   grid-cell extension of \(S_h\) is supported inside
   the \(O(h+\delta(h))\) neighbourhood of \(\overline
   {\Omega_m}\).

2. **Exact finite energy.** Extend an arbitrary finitely
   supported grid vector \(u_i\) by zero to all
   \(\mathbb Z^2\). The original matrix satisfies
   \[
   u^\top(4I-B_h)u
     =\sum_{i\in\mathbb Z^2}\sum_{j=1}^2
        (u_{i+e_j}-u_i)^2\ge0.
   \]
   The equality holds *including all boundary edges*
   because the original diagonal coefficient is exactly
   4; it is not the degree of an induced subgraph.
   The script scripts/gielis_fd_energy_mosco.py
   verifies this with exact rational/integer arithmetic
   on four independent selected test-vector families.

3. **Reconstruction in \(L^2\).** Set \(U_h\) equal to
   \(u_i\) on the \(h\times h\) cell centred at grid
   point \(i\), and zero elsewhere. Then exactly
   \[
   \|U_h\|_{L^2}^2=h^2\sum_i u_i^2,\quad
   \sum_{j=1}^2\|D_j^hU_h\|_{L^2}^2
   =u^\top(4I-B_h)u,
   \]
   where \(D_j^h=(T_{he_j}-I)/h\) is the finite
   difference quotient. Thus the finite Rayleigh
   quotient is the quotient of a nonnegative discrete
   \(H^1\)-energy by the exact reconstructed \(L^2\)-mass.

4. **Recovery / limsup.** For every
   \(\varphi\in C_c^\infty(\Omega_m)\), assign
   \(u_i=\varphi(x_i)\). For all sufficiently fine
   meshes its support avoids the boundary and
   the sampling and Riemann-sum rules yield
   \(\|U_h\|_2\to\|\varphi\|_2\) and
   \(\sum_j\|D_j^hU_h\|_2^2
      \to\int_{\Omega_m}|\nabla\varphi|^2\).
   Density of \(C_c^\infty(\Omega_m)\) in \(H_0^1(\Omega_m)\)
   and the min–max theorem give
   \(\limsup_h\lambda_k(A_h)\le\lambda_k(\Omega_m)\).

5. **Compactness / liminf.** Normalize the first k
   discrete eigenvectors in the reconstructed \(L^2\)
   norm. The recovery estimate bounds their energies.
   The discrete difference quotient bound, bounded
   spatial support, and Kolmogorov–Riesz translation
   criterion give a strongly \(L^2\)-convergent subsequence.
   The discrete derivatives have weakly convergent
   \(L^2\) subsequences, whose distributional limits are
   the weak derivatives. Limits therefore lie in
   \(H^1(\mathbb R^2)\), vanish outside \(\Omega_m\),
   and by its smooth/Lipschitz boundary have zero trace,
   hence lie in \(H_0^1(\Omega_m)\).
   Strong \(L^2\) convergence preserves the k
   orthonormal directions. Weak lower semicontinuity
   of the Dirichlet form applied to each linear
   combination and the min–max principle yield
   \(\lambda_k(\Omega_m)\le
     \liminf_h\lambda_k(A_h)\).

6. **Conclusion.** The matching liminf/limsup prove the
   asserted spectral convergence. There is no
   pollution of each *fixed low Dirichlet eigenvalue*,
   but this does not assert norm-resolvent convergence,
   quantitative mesh errors or statements about
   increasingly high mode numbers \(k=k(h)\).

**Implementation caveat.** The above mathematical
convergence theorem selects *exact real evaluation* of
the analytic \(r_m\) in the grid predicate. The
current Python simulator evaluates trigonometric functions
in binary64, so the finite selected masks must be
cross-checked (or evaluated by certified/precision-growing
interval arithmetic) to transfer the asymptotic theorem
to literal floating-point execution. A fixed binary64
roundoff error cannot be silently treated as \(o(1)\).
The exact FD energy identity itself holds for **any**
realized finite mask, regardless of how it was selected.
The Agda source still owes explicit raster vertex/edge
enumeration, analytic discrete compactness and operator
identification; this note is a rigorous *paper theorem*
using standard compactness, not an Agda kernel receipt.

The old YM Mosco/recovery/liminf modules were inspected as
methodological donors. They explicitly record those
theorems as **not constructed** and cannot be used as
kernel evidence of the present Gielis continuum result.

### E27 accepted mathematical cut versus remaining exact leaves

- Mathematical exact-boundary, vanishing-tolerance
  original Cartesian five-point scheme: fixed-k
  **qualitative** Dirichlet spectral convergence CLOSED
  on paper, using stated classical theorems.
- Original n=41/n=61 finite mask, exact positive-vector
  eigenvalue enclosure and discrete energy algebra:
  retained and source-checked; no numerical continuum
  error width inferred.
- Literal binary64 mesh predicate, machine-verified
  convergence rate and native Agda continuum proof:
  OPEN; no false promotion from E27.


## E28 — Native selected four-phase Fourier inversion and Nyquist separation

The existing GielisBase369NyquistPhase36Exact.agda supplies
the actual Phase36 sample carrier. It proves that m=9
and m=27 sine modes are identically zero when sampled on
the coarser 18 even phases, and that fine j=1 samples
resolve their opposite signs.

The new GielisNineModeFourierExact.agda constructs an
actual selected rational 4-phase Fourier transform using
the **same** Nyquist.Phase36 samples j=0,1,2,3.
For arbitrary rational samples \(f=(f_0,f_1,f_2,f_3)\),
its Fourier coefficients are

\[
 a=(f_0+f_1+f_2+f_3)/4,\quad
 b=(f_0-f_2)/2,\quad c=(f_1-f_3)/2,\quad
 d=(f_0-f_1+f_2-f_3)/4.
\]

The exact inverse is

\[
 (f_0,f_1,f_2,f_3)
 =(a+b+d,a+c-d,a-b+d,a-c-d).
\]

These are the four real character rows
\(1,\cos(9\theta_j),\sin(9\theta_j),\cos(18\theta_j)\)
for \(\theta_j=2\pi j/36\).
Both directions of the original 4x4 rational transform
are source-written using the repository's rational
ring solver and record-coordinate extensionality,
without a hypothetical FFT or assumed Fourier operator.

The original \(\mathbb Q(\zeta_{36})\) twelve-rational-
coordinate implementation is reused in
scripts/gielis_nine_quarter_fourier_exact.py. It
independently establishes the exact character rows

\[
 \cos9=[1,0,-1,0],\quad
 \sin9=[0,1,0,-1],\quad
 \cos18=[1,-1,1,-1]
\]

inside the actual cyclotomic quotient, and checks
both forward/inverse identities for 625 rational
sample vectors by exact Fraction arithmetic.

This is a **selected m=9 quarter-wave reconstruction
result**, not proof of the entire C36 cyclotomic DFT
over arbitrary 36 signals. The latter requires an
Agda native twelve-dimensional field carrier and
all 36 character-resolution relations.
Exact-head Agda acceptance remains to be established.

## E29 — Reduce concrete Bishop four-angle to same-object doubling

The source GielisBishopPolynomialExact.agda now
contains BishopConcreteDoubleAngleInputs on the
**same actual configured Bishop sine/cosine dataset**.
Its three proof inputs are

\[
 \cos_B(2x)\simeq\cos_B(x)^2-\sin_B(x)^2,\quad
 \sin_B(2x)\simeq2\cos_B(x)\sin_B(x),
\]
and
\[
 \cos_B(4x)\simeq
 \cos_B(2x)^2-\sin_B(2x)^2.
\]

The reducer bishopCosineQuadrupleFromTwoDoubleAngles
uses actual Bishop setoid congruence and the
previous native polynomial quartic equality to
derive the ordinary concrete four-angle identity

\[
 \cos_B(4x)\simeq
 \cos_B(x)^4-6\cos_B(x)^2\sin_B(x)^2
 +\sin_B(x)^4.
\]

The consumer bishopGielisFromPythagoreanAndTwoDoubleAngles
then applies the previously source-written Gielis
Pythagorean/quartic reducer to prove the selected
rational radial identity from these smaller native
analytic leaves.

The remaining analytical producer is now precisely
the two sine/cosine doubling equations on the
original Round11 Bishop sine/cosine power-series
carrier, including \(4x=2(2x)\) setoid argument
transport. The current module does NOT manufacture
those inputs, nor identify them with a new formal
sine/cosine object. The analytic power-series
product/addition theorem and exact-head Agda kernel
check remain outstanding.


## E30 — Native full six-phase Fourier via existing cyclotomic C3 and CRT

The repository already proves **two-sided** Fourier inversion
on the actual rational cyclotomic field
\(\mathbb Q(\omega)=\mathbb Q[x]/(x^2+x+1)\)
in DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda.
There is therefore no justification for rebuilding a
new complex scalar to treat a six-phase selected Gielis
signal: the cyclic Chinese-remainder isomorphism

\[
 C_6\xrightarrow{\cong} C_2\times C_3,\qquad
 j\mapsto (j\bmod2,j\bmod3)
\]
makes a \(C_6\) transform the tensor of the
two-point rational Hadamard transform and the
already-existing native three-point cyclotomic transform.

The *actual Phase18 sample indexing* is

\[
 \begin{array}{ll}
  (\mathrm{even},0,1,2)&\leftrightarrow (0,4,2),\\
  (\mathrm{odd},0,1,2)&\leftrightarrow (3,1,5).
 \end{array}
\]

The new Agda module
DASHI/Geometry/GielisSixPhaseCyclotomicFourierExact.agda
uses these exact original Phase18 positions. For the
two-point component it defines

\[
 F_2(x,y)=(x+y,x-y),\quad
 F_2^{-1}(u,v)=((u+v)/2,(u-v)/2)
\]

over the original \(\mathbb Q(\omega)\) carrier.
Both directions of this two-point inversion and
their three-coordinate lifts have source-written
proofs via the original rational ring solver.
It then composes with
C3.oneDimensionalFourierInversion and
C3.oneDimensionalFourierForwardInverse
to derive the literal original six-sample forward
and inverse identities.

The direct \(C_6\) DFT Fourier modes correspond to
the CRT pair \((r,s)\) via
\[
 k=(3r+2s)\bmod6,
 \quad k=(0,2,4,3,5,1).
\]
A separate exact interoperability computation,
scripts/gielis_six_phase_cyclotomic_exact.py,
compares the native-style \(C_2\times C_3\)
transform to the **original**
\(\mathbb Q(\zeta_{36})\) direct six-phase DFT,
where the embedding of \(C_6\) is
\(\zeta_{36}^6\) and the \(C_3\) root is
\(\zeta_{36}^{12}\).
For **729** six-sample vectors with each coordinate
in \(\{-1,0,1\}\), the original exact quotient
field gives perfect forward Fourier coefficient
agreement and both directions of inversion, without
any floating-point tolerance.

**What E30 closes:** a genuine six-point
cyclotomic signal Fourier operator and inversion
source-written by reusing an existing native
three-point Fourier theorem; its original
Agda kernel acceptance remains to be established.

**What E30 does not close:** the full arbitrary
36-sample \(\mathbb Q(\zeta_{36})\) Fourier resolution,
the ordinary-real Bishop cosine/sine sampling identity,
or the actual continuum Shannon reconstruction
theorem. Those are separate G07/G10/G19
acceptance types, not consequences of selecting
only six samples.


## E31 — Exact unshrunken rational Gielis grid membership, no floating geometry

**This supersedes E27's remaining binary64 *boundary-classification*
obstruction for all selected integer modes.** The original
finite-difference solver, rational eigenvalue referee and
zero-exterior discrete-energy checker now use
scripts/gielis_exact_rational_raster_geometry.py,
not floating-point evaluation of sine, cosine or
square roots to decide node membership.

**Theorem (exact integer-mode rational predicate).**
Fix an integer mode \(m>0\) and rational coordinates
\(x,y\). Put \(q=x^2+y^2\) and
\(u_m=\operatorname{Re}((x+iy)^m)\in\mathbb Q\).
At \(q=0\), the point is strictly inside the selected
Gielis domain. At \(q>0\), since
\(\cos(m\arg(x+iy))=u_m/q^{m/2}\), the analytic
radial inequality is exactly equivalent to

\[
\boxed{(3q-4)q^{m/2}+q u_m<0.}
\]

If \(m=2k\) is even, this is a strict comparison of
two *rational polynomials*. If \(m=2k+1\) is odd, write

\[
 A=(3q-4)q^k,\qquad B=q u_m,
\]
so membership is the sign test \(A\sqrt q+B<0\),
decidable **without calculating \(\sqrt q\)**:

\[
\begin{array}{ll}
 A=0: & B<0,\\
 A>0: & B<0\ \land\ A^2q<B^2,\\
 A<0: & B\le0\ \lor\ A^2q>B^2.
\end{array}
\]

All strict comparisons retain equality semantics,
so the boundary is excluded. These three cases are
proved by moving a strictly signed term to the other
side and squaring **only after sign checking**.
The rational complex power is constructed by integer
polynomial multiplication, and every comparison is
performed by exact Python Fraction integer arithmetic,
without arbitrary precision approximations or a
fixed radial tolerance.

**Concrete selected legacy parity:** The strict
*unshrunken exact-domain* predicate gives the same
mask as the old floating radius-minus-1e-12 predicate
at all four original computational fixtures:

| Mode | Grid | Exact interior nodes | Legacy disagreements |
|---|---|---:|---:|
| 3 | 41×41 | 792 | 0 |
| 6 | 41×41 | 779 | 0 |
| 9 | 41×41 | 792 | 0 |
| 3 | 61×61 | 1788 | 0 |

These are independent local exact Fraction checks
against the old NumPy mask. For **new** fine grids,
the solver now always uses the exact unshrunken
membership; the 1e-12 cutoff is no longer the actual
membership convention. Accordingly the earlier
vanishing-tolerance family E27 is *superseded* at
the numerical source level by the stronger zero
tolerance/exact analytic predicate, which also
satisfies the E27 recovery/compactness proof
assumptions.

**Native Agda owner:**
DASHI/Geometry/GielisExactRationalGridPredicateExact.agda
source-writes the actual RationalComplex integer
power, rational strict less-than decisions, and
selected 3/6/9 membership booleans, including exact
origin and positive-x axis boundary laws.
It does not insert a new postulate or an artificial
real carrier. Agda kernel acceptance and the
same-object Bishop-real analytic cosine/radial
connection remain distinct proof obligations.

**What now closes:** Binary64 geometry classification
is **removed from the actual raster algorithms** for
integer Gielis modes; the original four selected
legacy masks agree exactly. G12's exact arithmetic
raster-to-continuum paper theorem applies to the
algorithm's mathematical membership predicate.

**Remaining G12:** A quantitative, validated bound
for the *finite* n41/n61 eigenvalues against continuum
spectrum still requires explicit interpolation/truncation
constants, and native Agda formalisation of the
min-max/compactness and graph-to-grid operators.
An exact finite eigenvalue bracket (E17/E26) is not
the same as a continuum discretisation error bound.


## E32 — Signed original ray cross-product to the actual typed SI torque

The older E22 used an abstract dimensionless signed ray response
\(g\). Its physical geometric value is no longer opaque.

For a selected ray hit \(\mathbf r=(x,y)\), unit input direction
\(\mathbf d_{\rm in}=(i_x,i_y)\), output direction
\(\mathbf d_{\rm out}=(o_x,o_y)\), and reflected power fraction
\(\eta\in[0,1]\), conservation of optical momentum gives
the **wall's** radiation-pressure force

\[
 \mathbf F_{\rm wall}
   =\frac{P}{c}
      (\mathbf d_{\rm in}-\eta\mathbf d_{\rm out}).
\]

Its right-hand-rule signed \(z\)-torque is therefore

\[
 \boxed{
 \tau_z
 = \frac{P}{c}\left[
 x(i_y-\eta o_y)-y(i_x-\eta o_x)
 \right]\quad \mathrm{N\,m}.}
\]

The new native source
DASHI/Geometry/GielisOpticalTorqueCrossSIExact.agda
constructs this *exact rational* signed lever as
signedWallLever, proves

\[
 \operatorname{signedWallLever}
  = \operatorname{rationalCrossZ}
     (\mathbf r,\mathbf d_{\rm in}-\eta\mathbf d_{\rm out})
\]
and its anti-symmetry, sign reversal under exchanging
input/output directions when \(\eta=1\),
zero torque from zero direction change, and invariance
under simultaneous \(180^\circ\) rotation of both position
and ray directions.

Crucially, the theorem
modelWallTorqueSIMagnitude invokes the previous
**actual** Mechanical.Quantity SI transport
from E22 with the *computed signed lever*:

\[
 \operatorname{magnitude}_{SI}
  (\operatorname{modelWallTorqueSI})
 = (P c^{-1})\,
 \operatorname{signedWallLever}
  (\mathbf r,\mathbf d_{\rm in},\mathbf d_{\rm out},\eta).
\]

There is no separate unattested SI carrier.
The existing R3HodgeCrossExact.hodgeWedgeEqualsCross
is reused for the established right-handed spatial
convention. Its underlying general-real group is **not**
identified automatically with the finite rational
carrier: an explicit rational-to-real embedding is still
needed to assert a fully same-carrier Hodge equality.

An independent executable event example uses the
original exact SI constant and \(P=9000\) W,
\(\mathbf r=(1,0)\) m, initial/outgoing directions
\((0,1),(0,-1)\), \(\eta=1\).
Its exact model torque is

\[
 \tau_z=\frac{18000}{299792458}\,\mathrm{N\,m},
\]
and the opposite directional swap gives its negative.
A radial reversal at \(\mathbf r=(1,0)\) gives zero
torque, while a simultaneous half-turn of the
entire geometry leaves the signed torque unchanged.
scripts/gielis_exact_signed_optical_torque.py checks
all these statements by Fraction arithmetic.

**What E32 closes:** the *finite* same-source
optical wall-angular-impulse coordinate expression,
its sign convention, and its typed SI scalar magnitude.
The earlier abstract \(g\) no longer needs to be
invented or accepted by assumption in this selected
planar model.

**Still necessary for real-world claims:**
measured emitted power, material reflectivity,
actual incident/outgoing directions and hit
locations with physical uncertainty, the original
apparatus model and independent replication.
A typed and dimensionally correct expression is
not a measurement receipt. Agda kernel acceptance
of the source-written E32 theorem also remains open.


## E33 — One actual Bishop imaginary-axis exponential producer implies all Gielis doubling

The native Round11 Bishop sine and cosine series are already
the specified real-valued functions; the repository separately
constructs complex values as Cartesian pairs of those same
Bishop reals in BishopSetoidComplexExact.agda.
Furthermore BishopExponentialCauchyProductExact.bishopExpAdd
already proves exponential additivity for the **real**
Bishop exponential series. It is a real analytic donor,
not by itself complex analytic additivity.

The new source
DASHI/Geometry/GielisBishopImaginaryExponentialReducerExact.agda
reduces the three concrete input identities from E29 to
**one same-function imaginary-axis exponential multiplier**.
Write the configured actual Bishop complex value
\[
 E_B(ix)=\cos_B(x)+i\sin_B(x).
\]
The only new analytic input needed for the doubling part is
\[
 \boxed{E_B(i\,2x)\simeq E_B(ix)\,E_B(ix).}
\]
This is a complex-setoid equality on the original
BishopSetoidComplexExact carrier, *not* a
syntactic assertion about an unrelated complex value.

The proof extracts the REAL component of this equality
using Complex.reEquivalent to obtain
\[
 \cos_B(2x)\simeq\cos_B(x)^2-\sin_B(x)^2.
\]
It extracts the IMAGINARY component with
Complex.imEquivalent and applies the original Bishop
ring solver's identity \(cs+sc=2cs\) to obtain
\[
 \sin_B(2x)\simeq2\cos_B(x)\sin_B(x).
\]
The existing Bishop sine/cosine setoid congruence
theorem transports \(4x\simeq2(2x)\); the
source proves this numeric angle identity by
the existing Bishop real polynomial solver.

The result
concreteDoubleAngleInputsFromImaginaryExp then
constructs **all three E29 double-angle source fields**
from that single complex analytic law.
Finally gielisRound11FromOneImaginaryExponentialLaw
uses the pre-existing shared Round11 classical/Bishop
Pythagorean weld plus the original Gielis polynomial
normal-form proof to establish

\[
 \boxed{
  4(\cos_B(x)^4+\sin_B(x)^4)
  \simeq3+\cos_B(4x)
 }
\]
on that actual same Bishop real/complex trigonometric
object.

The real exponent addition donor is imported and
re-exported as realBishopExpAddAlreadyProved,
without falsely asserting that a real exponential
identity proves the **complex** series product.

**Exactly one complex analytic leaf remains for
the trigonometric doubling/quadrupling portion:**
prove the imaginary-axis complex exponential
multiplication law for the literal selected Bishop
sine/cosine series, by complex factorial-series
Cauchy products and tail/limit identification
reusing the available real Bishop Cauchy machinery.
The other analytic leaves remain the earlier
shared Round11 Pythagorean same-object weld,
positive real reciprocal square root and radial
integration/derivatives. Agda kernel acceptance of
this new source has not been verified here.


## E34 — Same-object Bishop complex algebra for factorial Cauchy products

The E33 trigonometric reducer now has a precise remaining
analytic input \(E_B(i\,2x)\simeq E_B(ix)^2\). The existing
BishopSetoidComplexExact.agda owns the literal Cartesian
Bishop complex carrier and operations but does not expose
every commutative algebra law needed for that Cauchy
product. The new
DASHI/Geometry/GielisBishopComplexCauchyAlgebraExact.agda
constructs them using the original complex operations
and the **existing Bishop real polynomial ring solver**:

\[
 z+w\simeq w+z,\qquad (z+w)+v\simeq z+(w+v),
\]
\[
 zw\simeq wz,\qquad (zw)v\simeq z(wv),
\]
\[
 z(w+v)\simeq zw+zv,\qquad
 (z+w)v\simeq zv+wv.
\]

These are genuine source-written complex setoid
equalities, with real and imaginary coordinate
proofs; the right distributive law reuses the
proved commutative and left-distributive laws.
No second complex carrier or postulate is added.

The original BishopExponentialFiniteCauchyCoefficientExact
already proves real factorial binomial/Cauchy
coefficients, and BishopExponentialCauchyProductExact
already proves real exponential additivity via the
rectangle/triangle/tail convergence machinery.
Those sources are exact donors, NOT a ready-made
complex series theorem.

**Remaining complex analytic lemma:** construct
the same semiring/binomial Cauchy coefficient
identity for the original BishopComplex exponential
factorials, prove its absolute series convergence
and limit interchange, and identify its even/odd
imaginary-axis components with the original
Round11 cosine/sine power series. E34 has paid
the algebraic rearrangement portion but not the
full analytic infinite-product theorem.
Native Agda kernel acceptance is still unverified.


## E35 — Improved first Dirichlet eigenvalue lower bound for ALL Gielis modes

For every positive integer \(m\) in the selected
special Gielis family,
\[
 r_m(\theta)^2=\frac{4}{3+\cos(m\theta)}
\quad\Longrightarrow\quad
|\Omega_m|
 =\frac12\int_0^{2\pi}r_m(\theta)^2\,d\theta
 =\sqrt2\pi.
\]
The exact area is independent of \(m\). The classical
Faber–Krahn inequality therefore gives
\[
 \lambda_1(\Omega_m)\ge
 \frac{j_{0,1}^{\,2}\pi}{|\Omega_m|}
 =\frac{j_{0,1}^{\,2}}{\sqrt2},
\]
where \(j_{0,1}\) is the first positive zero of
the Bessel \(J_0\) function.

The irrational Bessel zero itself need not be
numerically guessed to obtain a **strict rational**
bound. At \(x=12/5\), the absolutely convergent
\(J_0\) alternating series has terms
\(a^k/(k!)^2\), \(a=x^2/4=36/25\). The terms
decrease after \(k=1\), so the **odd truncation
through degree five** is a rigorous lower bound:

\[
 J_0(12/5) >
 S_5=
 1-\frac{36}{25}+\frac{324}{625}
 -\frac{1296}{15625}
 +\frac{2916}{390625}
 -\frac{104976}{244140625}
 =\boxed{\frac{608149}{244140625}}>0.
\]

For \(0<x\le12/5\),
\[
 J_1(x)=\frac x2\sum_{k=0}^{\infty}
  \frac{(-1)^k(x^2/4)^k}{k!(k+1)!}.
\]
The alternating magnitudes decrease from \(k=0\)
because their first ratio is at most
\((36/25)/2=18/25<1\). The inner series
is therefore at least \(1-18/25=7/25>0\).
Since the classical derivative identity is
\(J_0'=-J_1\), the function \(J_0\) is strictly
decreasing throughout \((0,12/5]\).
Combining monotonicity with \(J_0(12/5)>0\)
shows \(j_{0,1}>12/5\).

Finally,
\((99/70)^2>2\) implies
\(\sqrt2<99/70\), whence
\[
 \boxed{\lambda_1(\Omega_m)>
  \left(\frac{12}{5}\right)^2\frac{70}{99}
  =\frac{224}{55}\approx4.07272727}
\]
for **every positive integer mode m**.

This sharpens E23's former elementary square
lower bound \(9/4\) to \(224/55\) (a gain of
roughly 81%) without depending on any
finite-difference eigensolver. The previously
derived m=3 Rayleigh upper certificate E15
gives
\[
 \boxed{\frac{224}{55}<\lambda_1(\Omega_3)
  <\frac{1273}{264}.}
\]
The dimensional SI bound for assumed physical
scale \(L\in[L_-,L_+]\) becomes
\[
 \boxed{
 \frac{224}{55L_+^2}<
  \lambda_1(L\Omega_3)<
 \frac{1273}{264L_-^2}\quad\mathrm{m}^{-2}.}
\]

**Executable provenance:** The source
scripts/gielis_continuum_faber_krahn_bound.py
verifies all displayed finite rational inequalities
using only Python Fraction. The actual SI spectral
consumer gielis_physical_spectral_si.py now uses
the stronger constant; no physical frequency is
deduced without an independently selected wave
equation and speed.

**Native Agda:** The new
GielisBesselFaberKrahnRationalExact.agda
source-writes exact normalized rational equalities,
strict positivity of the truncated \(J_0\)
series, the \(J_1\) coefficient lower bound,
rational upper bound on \(\sqrt2\), and the
arithmetic for \(224/55\), all on the original
Agda rational carrier.

**Exact acceptance limit:** The native finite
arithmetic terms are source-written but not
kernel-accepted in this environment. The
analytic Faber–Krahn theorem, Bessel derivative,
alternating-series convergence and exact
area-to-domain identification are classical
external mathematical donors at the paper
level, not formally completed native Agda
theorems merely because their rational
consequences were checked.


## E36 — Prior-owner recovery and exact remaining same-object acceptance (audit, not a newly proved theorem)

This section corrects the overbroad original P0–P3 "missing"
table. The following are EXISTING source-level original
Agda theorem owners or cross-PR interfaces. Their native
proofs should be consumed, not duplicated.

### P0 — Bishop real/complex algebra, series, π, root and polar

- DASHI/Analysis/BishopComplexSeriesConvergenceExact.agda:
  componentwise absolute-series input, complexSeriesLimit,
  complexSeriesLimitConvergence, and complexSeriesLimitUnique.
  This module's BishopComplex is its own record over actual
  vendored reals. DASHI/Analysis/BishopSetoidComplexExact.agda
  has a separately declared BishopComplex with actual expC,
  powC and setoid congruence; literal record identity must
  NOT be presumed despite matching coordinate semantics.
- DASHI/Analysis/BishopComplexAlgebraExact.agda:
  exact actual complex arithmetic and powers on the FIRST
  complex record. E34's complex ring-law proof on the
  SECOND complex record is an added convenience, not
  evidence that the project lacked complex algebra.
- DASHI/Foundations/BishopExponentialFiniteCauchyCoefficientExact.agda
  and BishopExponentialCauchyProductExact.agda:
  actual real factorial coefficients, Cauchy product,
  limiting series and bishopExpAdd. All already owned.
- DASHI/Foundations/BishopMachinPiRationalWindowExact.agda:
  actual constructive Machin π_M bounded strictly
  between 3 and 22/7. What remains is equality with
  the selected trig period/first positive zero, NOT
  construction of a π candidate from nothing. The
  BishopSetoidComplexExact source explicitly sets
  selectedPiIdentifiedWithClassicalPi=false.
- DASHI/Foundations/BishopNatSquareRootSemanticSquareExact.agda:
  semantic sqrt(N)^2=N on the actual Bishop carrier for
  natural-number radicands. Variable 3+cos(mθ) is a
  separate positive-real root/reciprocal application.
- DASHI/Physics/QuantumVacuum/BishopPolarJacobianSameTrigWeldCompilerExact.agda:
  original selected Round11 trig derivatives and
  polar determinant equals radius.
  BishopPolarMeasureSourceWeldReducedExact.agda
  explicitly records measureTheoreticWeldClosed=false.
  The remaining Gielis area step is genuine specific
  measure/domain/integrand identification, not a new
  generic polar Jacobian theorem.

### P1 — Generic native Fourier machinery already exists

- DASHI/Algebra/Quantum/ShorCyclicCharacterResolutionExact.agda:
  generic Fin Q cyclic transform/inversion reducing the
  QFT to concrete character-resolution laws.
- DASHI/Algebra/Quantum/ShorCyclicDFTLeanCrossProverWeldExact.agda:
  externally pinned Lean normalized cyclic DFT proof;
  identifies index/coefficient same-object ABI as its
  remaining obligation.
- DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierInversionFromResolutionExact.agda:
  derives full generic finite Fourier inverse from a
  specified kernel-resolution/character-orthogonality
  datum. The associated ParsevalFromInversion owner
  proves the generic finite Parseval transport.
- DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda:
  original native Q(ω) C3 and tensor C3³ forward/inverse;
  E28/E30 consume selected 4/6 subcarriers. The full
  C36 coefficient model is **not** Q(ω): it needs the
  original 12-rational-coordinate cyclotomic quotient
  Q[x]/(x^12-x^6+1), its 36-character resolution, and
  same-carrier normalized Fourier map.

### P2 — Operator/spectrum reuse already exists

The YM repo includes finite Hermitian Rayleigh,
operator domain, Mosco recovery/liminf and
spectral-transfer owners, e.g.
BalabanClayGate4FiniteMatrixSpectrumDeterminantAssemblyExact.agda
and CarrierMoscoConvergenceFromPhysicsReceipt.agda.
The latter explicitly reports required domain/density
proofs and failed norm-resolvent promotion rather than
a complete generic spectral-convergence authority.
Gielis E26/E27/E31 have already paid the exact finite
matrix, correct-domain mask and paper-level fixed-mode
convergence. The narrow remaining producer is the
selected Gielis **same-form** native minmax/compactness
instance and quantitative n=41/61 continuum error.

### P3 — Original optical momentum/torque model already exists

Kozyrev PR #1404 is the original owner, not an
undocumented external apparatus:
scripts/kozyrev_optical_event_ledger.py supplies
RayLedger.emit, RayLedger.hit and RayLedger.close,
where each hit computes
\(p_{\rm in}=(P/c)d_{\rm in}\),
\(p_{\rm out}=(P\eta/c)d_{\rm out}\),
the wall-force increment and signed
\(r\times\Delta p\) wall torque, and tracks
absorption/power and terminal state.
The same PR includes the log-spiral/segmented
geometry optimizer, source-matched family
comparison, first-forward independent polygonal
intersection referee and optical/energy checks.
E32 is the Agda signed-torque expression of
that ALREADY EXISTING conventional physical law.

The outstanding G15/G16 requirement is to match
the selected Gielis finite event to the original
Kozyrev event ledger and **physical calibration**
of P, reflectivity, hit positions, directions,
normal conventions, instrument errors and
uncertainty/replication if the consumer asserts
real apparatus behaviour. Synthetic or arbitrary
rational input numbers cannot substitute for
actual measurements.

### Revised actual max-cut

1. Bishop: original **complex** factorial-product
   same-object relation with Round11 sine/cos,
   selected Machin-π to trigonometric period,
   variable Bishop positive root and Gielis
   polar measure/integrand.
2. Fourier: instantiate the existing general
   cyclic/finite kernel-resolution theorems on
   the original C36 cyclotomic scalar, not
   write another Fourier theorem from scratch.
3. Spectrum: original Dirichlet Gielis
   same-form native eigenvalue transport and
   quantified numerical finite-grid error.
4. Physical: original RayLedger same-event
   Gielis input and empirical calibration
   receipt only if real-device conclusions
   are intended.

**Status:** this is a SOURCE ARCHAEOLOGY / REUSE
correction, not an independent E36 proof of
the four remaining promoted results.


## E37 — Original Bishop complex-series same-carrier transport

The existing BishopComplexSeriesConvergenceExact and
BishopSetoidComplexExact declare different BishopComplex
record types with the identical vendored Bishop-real
coordinates. GielisBishopComplexSeriesSameCarrierExact.agda
constructs total conversion maps and proves both round
trips by definitional equality. It also proves the
correspondence of addition, multiplication, zero and one
with BishopComplexAlgebraExact, transports the componentwise
setoid relation in both directions, and reuses the
ORIGINAL complexSeriesLimitConvergence and
complexSeriesLimitUnique theorems on the actual complex
carrier consumed by the Gielis exponential.

This closes the *generic complex-series ABI transport* at
source level. Remaining: select the actual imaginary-axis
factorial sequence, prove its absolute componentwise
convergence and Cauchy product, identify its real/imaginary
parts with original Round11 sine/cosine, and identify
the selected pi with the trigonometric period. Agda
kernel acceptance has not been obtained here.

## E38 — Full unrestricted exact cyclotomic C36 signal inversion

The original scripts/gielis_cyclotomic36_exact.py
implements K=Q[x]/(x^12-x^6+1), with zeta^36=1 and
the complete 1296 exact cyclic character-resolution
pairs. Its prior selected-mode recovery was not the
full input space. The new script
scripts/gielis_cyclotomic36_unrestricted_exact.py
explicitly defines

\[
 F(k)=\sum_{j=0}^{35} f(j)\zeta^{-kj},\qquad
 f(j)=\frac1{36}\sum_{k=0}^{35}F(k)\zeta^{kj}.
\]

It checks every original character-resolution pair
and **both** transforms of all 36 standard basis
vectors in the original 12-rational-coordinate field,
plus non-basis cyclotomic examples. The identity
on the basis and finite field-linearity prove
inversion for arbitrary K^36 signals, not just the
seven selected frequency modes.

Thus unrestricted C36 Fourier inversion is CLOSED at
the exact algebraic/computational level. Still OPEN:
construct this precise original cyclotomic K coefficient
carrier and its complete 36-character-resolution
instance natively in Agda, then invoke the already
existing Shor/NSTriad generic Fourier inverse.
A computational proof is not an Agda kernel receipt.

## E39 — Rigorous quantitative a posteriori Cartesian FD error

For the selected m=3 continuum Gielis domain,
the independently proved E35/E15 interval is
\(224/55<\lambda_c<1273/264\).
The original E17/E26 finite 5-point matrix on
the same unshrunken Gielis domain gives a
rational positive-vector enclosure
\(L_h\le\lambda_h\le U_h\).
Consequently every pair consistent with the
two original theorem certificates satisfies

\[
 \boxed{|\lambda_h-\lambda_c|
 <\max\bigl(0,1273/264-L_h,U_h-224/55\bigr).}
\]

It also gives strict relative error upper bound
obtained by dividing by 224/55.
scripts/gielis_certified_continuum_fd_error.py
loads the ORIGINAL exact finite-grid referee
and continuum bounds; its output is a fully
rational finite n=41 or n=61 error enclosure.
It fails closed for other m, where the continuum
upper bound is not established.

This **does pay a quantitative error bound** at the
selected finite meshes, but it is necessarily loose.
It does NOT prove an asymptotic \(O(h^p)\) rate,
native Agda compactness/minmax, or a sharp
mesh interpolation bound. Those stay explicit.

## E40 — Actual original Kozyrev RayLedger exact-event interface

The original PR #1404 owns RayLedger.emit/hit/close,
power depletion, reflectivity, signed r-cross-delta-p
torque, source/terminal momenta and absorption.
Earlier Gielis code already compared zero-modulation
log spirals with the original first-impact owners.

The new
scripts/gielis_kozyrev_same_event_original_owner.py
accepts an exact decimal/rational source, sequence
of directed wall hits, axis origin, reflectivities
and a terminal state. It independently computes
the same event's exact Fraction optical wall-force,
signed torque, absorbed/output power and full
momentum/energy/angular budgets. It dynamically
loads the ACTUAL original PR #1404 RayLedger
owner, verifies the exact expected Git blob SHA
from gielis_kozyrev_pr1404_bridge, replays the
same events and compares all observables.

For the nontrivial two-hit synthetic fixture:
power 9000 W, axis (-1,1), source (-2,0) along
+x, hit (0,0) outgoing +y at reflectivity 19/20,
hit (0,2) outgoing -x at reflectivity 4/5,
escape at (-2,2). Exact rational calculation gives
\[
 \tau_z=\frac{1080}{149896229}\ {\rm N\,m},
 \quad P_{\rm absorbed}=2160\ {\rm W},
 \quad P_{\rm escaped}=6840\ {\rm W}.
\]
The exact total momentum, angular and energy
budget residuals vanish. This is conventional
optical mathematics, NOT a measured Kozyrev effect.

The original PR source is on a DIFFERENT Git ref.
Runtime comparison must be supplied the byte-identical
PR #1404 source; absent/mismatched owner fails
closed and actual original runtime parity is
NOT YET CHECKED here. A Gielis solver-produced
multi-hit event receipt and independent
apparatus calibration remain separate physical
acceptance gates.
