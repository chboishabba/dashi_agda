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
