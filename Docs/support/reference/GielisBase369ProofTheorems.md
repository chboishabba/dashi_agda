# Gielis × Base369: mathematically closed theorems and non-promotion proof ledger

**Scope and trust.** These are explicit mathematical proofs for the selected
Gielis radial family, not an Agda kernel acceptance receipt. The companion
\`scripts/gielis_base369_symbolic_certificates.py\` independently checks the
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
source in \`GielisBase369NyquistPhase36Exact.agda\`.

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
and offers \`--power-watts\` as a **conditional ideal model**;
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
The codec emits \`0\` for \(q=0\), independent of \(m\).
For \(q>0\), it emits \`1 gamma(m) gamma(q+1)\`,
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
- \`agda --safe\` or ordinary-real Agda same-object realization (G01–G05);
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

\`DASHI/Geometry/GielisBishopPolynomialExact.agda\` imports the actual
vendored \`Real\`, \`RealProperties\`, and the existing
\`BishopPowerSeriesElementaryBridgeExact\` sine/cosine owner.

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
existing \`BishopP.ℝ-Solver\`, NOT accepted until Agda --safe runs.

To get the actual Gielis inverse-square identity, the selected Bishop
trigonometric functions still owe these *same-object* certificates:

1. \(\cos_B^2x+\sin_B^2x\simeq1\), for the actual Round-11
   power-series data set (not a generic conditional \`Set\`);
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

\`scripts/gielis_cyclotomic36_exact.py\` implements reduction by
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

\`scripts/gielis_sector_spectral_certificate.py\` outputs rational
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
\`scripts/gielis_rayleigh_spectral_bound.py\`.

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

\`scripts/gielis_reflection_parity.py\` independently brackets and
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

For source uncertainties, \`scripts/gielis_optical_statistics.py\`
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


## E17 — exact Perron–Frobenius certification of the ORIGINAL raster FD λ₁

The existing `gielis_base369_experiments.laplacian_eigenvalues`
builds a five-point grid on Cartesian coordinates
`linspace(-1.5,1.5,n)` and keeps cells satisfying
`hypot(x,y) < r_m(atan2(y,x))-1e-12`.
For every interior point the discrete Dirichlet matrix is exactly

[
  A_{m,n}=h^{-2}(4I-B),quad
  h=rac{3}{n-1},
]
where (B) is the unweighted nearest-neighbour adjacency
matrix of the retained interior nodes. The `4` diagonal is
**not** replaced by the number of interior neighbours: missing
neighbours represent zero Dirichlet boundary data.

On each connected interior graph, (B) is nonnegative and
irreducible. Given **any** strictly positive rational vector
(q=(q_i)), Collatz–Wielandt bounds the Perron root:

[
 min_irac{(Bq)_i}{q_i}le ho(B)le
 max_irac{(Bq)_i}{q_i}.
]
Because (A_{m,n}=h^{-2}(4I-B)),
the first discrete eigenvalue satisfies the **exact rational**
enclosure

[
 oxed{
 min_irac{4q_i-sum_{jsim i}q_j}{h^2q_i}
 le lambda_1(A_{m,n}) le
 max_irac{4q_i-sum_{jsim i}q_j}{h^2q_i}.
 }
]

The new independent referee
`scripts/gielis_raster_fd_positivity_certificate.py`
uses SciPy only to *propose* (q), then rounds every entry
to a positive **integer**, checks graph connectivity and
computes both bounds using Python `Fraction` integer rational
arithmetic. The conclusion holds regardless of the floating
eigenvector's alleged correctness. It cross-checks the actual
original five-point eigsh value.

Independent local reproduction yielded:

| m | n | rational enclosure endpoints (decimal approximations) |
|---|---|---|
| 3 | 41 | [4.222626933506416, 4.222626933827854] |
| 6 | 41 | [4.487431020746635, 4.487431021257153] |
| 9 | 41 | [4.6493512607746865, 4.649351262121115] |
| 3 | 61 | [4.289131748459455, 4.289131749856795] |

This **closes a rigorous first-discrete-eigenvalue error
certificate** for the original finite matrix. It does
**not** prove spectral convergence of that *Cartesian raster
scheme* to the continuum Dirichlet spectrum; E14 is a
different, sectorwise continuum approximation theorem.
G12 continuum/FD weld is still OPEN, but the error of
the *individual discrete eigenvalue computation* is paid.

## E18 — precise Kozyrev PR #1404 same-object baseline and offset-wall weld

The original canonical owners are accessible in
[Kozyrev PR #1404](https://github.com/chboishabba/dashi_agda/pull/1404),
head `337aabb00ed54bc1a4c28ada48364cb4dc54d46e`:

- `scripts/kozyrev_first_forward_intersection_referee.py`:
  `surfaces(g,samples)` defines an `inner*exp(growth*theta)`
  logarithmic centreline, *normal-offset* finite-thickness wall
  sides and two end caps; `first_cross` has a **0.003 m**
  first-forward admission threshold.
- `scripts/kozyrev_optical_event_ledger.py`: canonical
  `RayLedger`, `specular`, wall momentum, optical
  reflection/absorption and physical SI torque.
- `scripts/kozyrev_matched_envelope_html.py`,
  `scripts/kozyrev_html_family_ternary_runner.py`,
  `scripts/kozyrev_geometry_optimizer.py`: the original
  matched-scene/sweep and geometry donor interfaces.

The Gielis open spiral for (epsilon=0) has
(h_{m,0}(	heta)=0) for every mode m, whence

[
 R_{m,0}(	heta)=0.75exp(b	heta),
 qquad
 b=rac{log(1.55/0.75)}{3pi}.
]

In PR #1404's `family="log"` with
`inner=0.75, outer=1.55, turns=1.5, srot=0`,
`growth=b`, the centreline is **the identical
mathematical function**, not a geometric approximation.
For any finite wall thickness w, both normal-offset
reference walls can be written

[
 X_pm(	heta)=R_{m,0}e_r
 pm 	frac{w}{2}
 rac{-,R_{m,0}e_r'+R'_{m,0}e_r}{sqrt{R_{m,0}^2+(R'_{m,0})^2}}
]

with consistent orientation and the same two flat end caps.
Here (e_r'=e_	heta); equivalently, use the normal
((-t_y,t_x)/|t|) for the positively oriented tangent.
The **sign label** of (pm) may be swapped without altering
the union of two wall sides. The actual normal orientation
used by the Python adapter is exactly PR #1404's tangent
convention.

`scripts/gielis_kozyrev_pr1404_bridge.py` imports
those two original Python module files from a local
checkout, checks their *literal Git blob hashes*, rebuilds
both reference walls independently, and compares first
forward hits with the **same 3 mm threshold**. Its
`RayLedger` check verifies
((P/c)r	imes(d_{m in}-d_{m out})) and
linear/angular momentum conservation for the same ray.

This establishes the exact *parameter identity* of
the log baseline and permits executable finite-thickness
referee parity. It does **not** identify the original
browser HTML **stroked SDF wall** with the normal-offset
reference wall. The historical HTML first-hit differences
(1.35–1.83 mm) and actual event-file replay remain G13
acceptance obligations, not a citation problem.

## E19 — conditional radiation-pressure torque envelope and paired CI

For source power (Pge0), maximum hit radius (R),
at most B wall reflections and reflected power fraction
(etain[0,1]) at each hit, each individual unit-direction
change satisfies

[
 |d_{m in}-eta d_{m out}|le1+eta.
]

As the surviving ray power at hit k is (Peta^k),
the total optical wall torque obeys

[
 oxed{|	au_{m wall}|
 le rac{PR}{c}(1+eta)
       sum_{k=0}^{B-1}eta^k
 le rac{2PRB}{c}.}
]

This remains true for signed angular momentum contributions
because absolute value is bounded by the sum of individual
magnitudes. It is an **ideal radiation-pressure-only**
inequality, not a bound on thermal, electrostatic,
gravitational or mechanical forces.

`scripts/gielis_optical_force_envelope.py` computes
this inequality entirely over `Fraction` rationals.
For a *hypothetical model input* (P=9000) W,
(R=1.7) m, (B=8), the perfect reflector bound
is about (816.565 mumathrm{N,m}), and
the (eta=0.95) bound about
(669.920 mumathrm{N,m}). These are not
observed apparatus readings.

For the numerical comparison of K geometries,
the same IID random ray directions are reused across
all K geometries as **paired** source samples.
For each nonbaseline design (a), write
(D_{i,a}=X_{i,a}-X_{i,0}).
Then focus differences belong to ([-1,1]), and
absolute-impulse differences to ([-M,M]) with
(M=2RB). Distinct ray directions remain independent,
even though geometry outcomes within each ray are
deliberately paired. Hoeffding and a union bound give
simultaneous model-source intervals for all
(2(K-1)) paired differences with
(alpha_{m each}=alpha/[2(K-1)]).
This corrects the unpaired-comparison inefficiency,
but it does **not** claim experimentally measured
confidence intervals or an actual physical emitter's
statistical independence.

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
