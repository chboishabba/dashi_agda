# YM N1 — ORIGINAL SU(2) Wilson renormalized plaquette variance has a cutoff/volume UNIFORM positive lower bound

Date: 2026-11-09. **Actual finite-lattice noncollapse theorem** (under genuine compact Haar/Wilson realization), not a continuum interacting field or Clay N1.02 closure.

## Statement: same original four-dimensional Wilson Gibbs source

Take any periodic 4D SU(2) hypercubic Wilson measure with side L>=3 and beta>=1, normalized product SU(2) Haar and the original action \(\exp(\beta\sum_p t(U_p))\), where \(t(W)=\tfrac12\operatorname{Re}\operatorname{Tr}(W)\). Fix any original plaquette \(p\). Define the **same-source gauge-invariant renormalized elementary plaquette observable**

\[
F_{\beta,p}(U)=\beta\bigl(t(U_p)-\mathbb E_{\mu_\beta}t(U_p)\bigr).
\]

Then for every such finite periodic volume and all beta>=1:

\[
\boxed{\mathrm{Var}_{\mu_\beta}(t(U_p))\ge
  \frac{1}{73728(1+6\beta)^2}.}
\]

Consequently,

\[
\boxed{\mathbb E_{\mu_\beta}[F_{\beta,p}^2]
=\beta^2\mathrm{Var}_{\mu_\beta}(t(U_p))
\ge\frac1{73728\cdot49}
=\frac1{3612672}>0.}
\]

This is a **positive quantitative renormalized-variance witness**, uniform in finite lattice volume and position of the actual original plaquette, and requires neither independent plaquettes nor a synthetic alternative Wilson measure.

## Exact proof from the original one-link conditional SU(2) law

Fix one positive link of p and condition on all other links. The original six staples \(V_1,\ldots,V_6\in SU(2)\) have quaternion sum \(S=\sum_j V_j=R V\), with \(R\in[0,6]\) and \(V\in SU(2)\) when R>0. By Haar invariance \(Q=U_\ell V\in SU(2)=S^3\) has conditional density

\[
d\nu_\kappa(Q)=Z_\kappa^{-1}\exp(\kappa q_0)dH(Q),
\quad \kappa=\beta R\in[0,6\beta],
\]

where \(q_0\) is the real quaternion coordinate, and \(Z_\kappa=\mathbb E_H e^{\kappa q_0}\). For R=0, choose any V; then \(\kappa=0\) and \(\nu_0\) is Haar.

The plaquette trace \(X=t(U_p)\) is \(q\cdot w\) for a unit quaternion \(w\in S^3\) determined by the *other three links of the fixed plaquette*. This is a real linear functional of Q on S^3. Rotational symmetry fixing the scalar q0-axis makes the conditional covariance diagonal: one scalar eigenvalue \(\mathrm{Var}_{\nu_\kappa}(q_0)\), and three identical imaginary eigenvalues \(\mathrm{Var}_{\nu_\kappa}(q_i)=\mathbb E_{\nu_\kappa}(1-q_0^2)/3\), with zero mixed covariance. We bound **both eigenvalues below**.

### Case 0<=kappa<=1

Since \(e^{-1}\le e^{\kappa q_0}\le e\), \(Z_\kappa\le e\), the conditional density is \(\ge e^{-2}\) relative to Haar. For every real constant a,

\[
\mathbb E_{\nu_\kappa} (X-a)^2
\ge e^{-2}\mathbb E_H(X-a)^2
\ge e^{-2}/4 \ge1/36.
\]

The final inequality uses \(e<3\) and the Haar S^3 covariance \(\mathrm{Var}_H(q\cdot w)=1/4\). Hence \(\mathrm{Var}_{\nu_\kappa}(X)\ge1/36\).

### Case kappa>=1: explicit two-interval cap variance

Haar's marginal density of \(q_0=x\) is \(\frac2\pi\sqrt{1-x^2}\,dx\), \(-1\le x\le1\). Put \(y=\kappa(1-x)\). After cancelling the common positive normalization factors, the density in y is proportional to

\[
f_\kappa(y)= e^{-y}\sqrt{y(2-y/\kappa)},
\qquad 0\le y\le 2\kappa.
\]

Its normalization satisfies \(A_\kappa=\int_0^{2\kappa}f_\kappa(y)dy\le2\), because \(\sqrt{y(2-y/\kappa)}\le\sqrt{2y}\le1+y\) and \(\int_0^\infty e^{-y}(1+y)dy=2\).

On the two disjoint intervals \(I=[1/8,1/4]\) and \(J=[3/4,1]\), for all kappa>=1, we have \(f_\kappa(y)\ge e^{-1}\sqrt{1/8}\ge1/12\). Their probabilities satisfy

\[
\Pr_{\nu_\kappa}(y\in I)\ge \frac{1}{192},
\quad
\Pr_{\nu_\kappa}(y\in J)\ge\frac{1}{96}.
\]

For any x in the first interval and x' in the second, \(|x-x'|\ge1/(2\kappa)\). The independent-pair identity \(\mathrm{Var}(q_0)=\tfrac12\mathbb E[(q_0-q_0')^2]\), with two independent **auxiliary copies of this single conditional law** (not independent Wilson plaquettes), implies

\[
\mathrm{Var}_{\nu_\kappa}(q_0)
\ge \frac1{192\cdot96\cdot4\kappa^2}
=\frac1{73728\kappa^2}.
\]

On interval J, \(1-q_0^2=(y/\kappa)(2-y/\kappa)\ge3/(4\kappa)\). Therefore every imaginary coordinate satisfies

\[
\mathrm{Var}_{\nu_\kappa}(q_i)
=\tfrac13\mathbb E(1-q_0^2)
\ge \frac{1}{96}\frac{1}{4\kappa}
=\frac1{384\kappa}
\ge\frac1{73728\kappa^2}.
\]

It follows for **every unit direction w** that
\[
\mathrm{Var}_{\nu_\kappa}(q\cdot w)
\ge\frac1{73728\kappa^2}
\ge\frac1{73728(1+\kappa)^2}.
\]
This and the kappa<=1 case establish the same final bound for all kappa>=0.

### Original Gibbs mixture and volume independence

Because \(\kappa=\beta R\le6\beta\), the actual one-link conditional variance obeys
\[
\mathrm{Var}(t(U_p)\mid U_{E\setminus\{\ell\}})
\ge\frac1{73728(1+6\beta)^2}
\]
for **every exterior link configuration**, including frustrated staple arrangements. The law of total variance on the true original Wilson measure gives the unconditional lower bound. Finally \(\beta/(1+6\beta)\ge1/7\) for beta>=1, yielding the stated positive, volume-independent rescaled variance.

## What it does and DOES NOT prove

**Paid analytically:** an **actual positive source-calibrated finite-volume N1 precursor** for the original Wilson physical observable \(F_{\beta,p}\), with explicit nonzero lower bound uniform in volume, position, and bare beta>=1. The earlier fixed-length **unrenormalized** plaquette trace collapse is not contradicted: multiplication by beta changes the variance scale.

**Still OPEN N1.02/E1:** this is an ultraviolet elementary-plaquette observable. It is NOT yet a fixed-physical-support renormalized local field in an interacting \(\mathbb R^4\) continuum QFT. A variance lower bound alone does not prove a continuum nonzero variance without suitable tightness, uniform integrability/moment bounds and identification of the limiting field in the **same** E1 Schwinger theory. The \(\beta\)-rescaled variance may also diverge; the source needs an upper moment/renormalization analysis. The theorem does not prove continuum non-Gaussianity, full OS reconstruction, D1 CMP116 connecting-polymer decay, D2 common-exponent gap, or group coverage.

**Exact next original-source lemmas:**
- `N1-SU2-01` prove the quaternion conditional law as the *literal original* four-dimensional SU(2) product-Haar Wilson one-link disintegration in the pinned native SU(N) carrier (not a new synthetic Gibbs law)
- `N1-SU2-02` formalize both conditional covariance eigenvalue lower bounds and the original total variance identity in Agda's real/Haar APIs
- `N1-SU2-03` use a fixed-physical-support renormalized field/loop family with **upper** moment/tightness and a noncollapsing limit, proving the same original E1 Schwinger distribution carries a nonzero observable
- `N1-SU2-04` rule out the continuum being merely Gaussian/free by a genuine interacting multi-point witness, if required for the physical E1 interpretation
- `G1-N1-01` extend the local quantitative lower bound to the selected faithful Wilson representations of each compact simple G, then pay that group's actual E1/N1 continuum source.

Numerical scalar constants are conservative and proved from elementary inequalities; no Monte Carlo or assumed independent plaquettes. This is analytical source mathematics, not yet an Agda 2.9 kernel proof and not a Clay mass-gap claim.
