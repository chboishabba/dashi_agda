# Literal plane-wave contraction: real carrier and small-momentum obstruction

## Sources

Kenneth G. Wilson, “Confinement of Quarks,” *Physical Review D* **10**
(1974), 2445–2459. DOI: [10.1103/PhysRevD.10.2445](https://doi.org/10.1103/PhysRevD.10.2445).

Walter Rudin, *Fourier Analysis on Groups*, Wiley, 1962. No DOI was assigned
to this monograph.

## What the literal side-four carrier can pair

`BalabanP33LiteralWilsonFPHaarFourthJetExact.agda` defines its external
arguments as real rational SU(2) bond fields.  The side-four character table
therefore cannot be inserted as a complex-valued field without an explicit
scalar extension.  There is, however, a fully real formulation.

For a momentum \(k\in C_4^4\), use the **base-site convention** for a positive
link (rather than a midpoint convention):

\[
 A^{a}_{\mu,k,c}(x)=e^a e_\mu\,c_k(x),\qquad
 A^{a}_{\mu,k,s}(x)=e^a e_\mu\,s_k(x),
\]

where

\[
 \chi_k(x)=c_k(x)+i s_k(x),
 \qquad c_k(x),s_k(x)\in\{0,1,-1\}.
\]

These are genuine arguments of the current rational contraction functions;
no complex field type is needed.  The base-site convention is important:
link-centred phases would introduce \(e^{ip_\mu/2}\), which on a side-four
torus includes eighth roots of unity and is not represented by the current
Gaussian-rational table.  A link-centred convention may be recovered later by
an explicit phase change, but it must not be silently presumed here.

For every real symmetric bilinear kernel \(B\), its complex plane-wave
diagonal is recovered from the two real evaluations:

\[
 B_\mathbb C(e\chi_k,e\overline{\chi_k})
 =B(ec_k,ec_k)+B(es_k,es_k).\tag{1}
\]

Indeed, bilinearity gives four terms, and the two mixed terms cancel by
symmetry.  Thus a same-object Fourier pairing for a real effective-action
two-jet need only prove symmetry and evaluate the two real fields above.
This applies to the Wilson AAqq term, the cubic bubble after its standard
effective-action symmetry factor, the Haar insertion, and the reduced-FP
second jet.  Equation (1) also keeps the current rational carrier honest.

## Exact side-four momenta and transversality

With the base-site convention, a backward lattice divergence has Fourier
symbol

\[
 \overline p_\mu=1-e^{-ip_\mu}.
\]

On the side-four carrier \(p_\mu=\frac{\pi}{2}k_\mu\), hence
\(\overline p_\mu\in\mathbb Q(i)\).  A complex polarization obeys

\[
 \sum_{\mu=0}^{3}\overline p_\mu e_\mu=0.\tag{2}
\]

Splitting (2) into real and imaginary parts produces two rational linear
constraints on the real and imaginary polarization components.  Consequently
the transverse external fields can be constructed entirely in the existing
rational coordinate carrier, once a momentum and a polarization are selected.
The \(1/256\) character normalization established in
`BalabanSide4GaussianFourierNormalizationAnalyticProof.md` is then the
normalization of their coordinate pairing.

## The decisive obstruction: side four cannot extract beta

The beta coefficient is a local small-momentum coefficient of the transverse
vacuum polarization.  A typical definition has the shape

\[
 \Gamma_{\mu\nu}^{(2)}(p)
 = (\delta_{\mu\nu}\widehat p^2-\widehat p_\mu\widehat p_\nu)
   \bigl(C_A\tfrac{11}{24}+r\bigr)+O(|p|^4),
 \qquad \widehat p_\mu=2\sin(p_\mu/2).
\]

But the only side-four momenta are

\[
 p_\mu\in\{0,\pi/2,\pi,3\pi/2\}.
\]

There is no sequence of nonzero side-four momenta converging to zero.  Hence
neither a finite difference at side four nor the four-orbit value enclosure
can prove the coefficient multiplying \(\widehat p^2\).  It can only test a
finite-volume value of a *previously identified* scalar integrand.

This is not a missing compiler or a normalization detail: it is a mathematical
non-identifiability result.  If \(F(p)\) is any function on the side-four
momentum set and
\[
 q(p)=\sum_{\mu=0}^{3}\sin^2(2p_\mu),
\]
then \(q\) vanishes on every side-four momentum, but
\(q(p)=4|p|^2+O(|p|^4)\) near zero.  Thus \(F\) and \(F+cq\) have identical
side-four data for every \(c\), while their extensions have different
quadratic Taylor coefficients at zero.  A finite grid without a shrinking
momentum spacing cannot determine the beta coefficient.

## Forced next theorem

The highest-value next theorem is therefore not another side-four orbit
calculation.  It is the following arbitrary-side, same-object statement:

\[
 \boxed{
 \text{For every }L\ge L_0,\ \Gamma^{(2)}_{L,\mu\nu}(p)
 \text{ from the literal Wilson+reduced-FP+Haar action equals its
 transverse lattice tensor decomposition, uniformly for }|p|\le p_0,
 \text{ with an }L\text{-uniform }O(|p|^4)\text{ remainder.}}
\tag{3}
\]

Only (3), followed by a signed bound on its scalar remainder, can establish
the positive physical beta inequality.  The existing arbitrary-side Wilson
fourth-jet surface and the arbitrary-side local Haar action jet already supply
two summands.  The corresponding arbitrary-side reduced-FP determinant, free
Green kernel, and uniform low-momentum remainder are not yet constructed.
That is the literal mathematical frontier; it should replace further
side-four refinement.
