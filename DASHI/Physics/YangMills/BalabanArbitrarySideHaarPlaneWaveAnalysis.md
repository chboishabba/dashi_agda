# Arbitrary-side Haar plane-wave diagonal and its Ward consequence

## Sources

Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed.,
Springer, 2015. DOI: [10.1007/978-3-319-13467-3](https://doi.org/10.1007/978-3-319-13467-3).

Kenneth G. Wilson, “Confinement of Quarks,” *Physical Review D* **10**
(1974), 2445–2459. DOI: [10.1103/PhysRevD.10.2445](https://doi.org/10.1103/PhysRevD.10.2445).

## Exact local evaluation

Unlike the reduced-FP and Green ingredients, the Haar action is already
defined on every finite periodic \(L^4\) carrier in
`BalabanLiteralSU2HaarFourthJetExact.agda`:

\[
 H''_L(A)=\frac23\sum_{x,\mu,a}(A^a_\mu(x))^2.\tag{1}
\]

Take a base-site Fourier mode with a real Lie/polarization amplitude
\(e=(e^a_\mu)\), and write its two real rational representatives as

\[
 A_{k,c}^a{}_{\mu}(x)=e^a_\mu c_k(x),\qquad
 A_{k,s}^a{}_{\mu}(x)=e^a_\mu s_k(x).
\]

At every site, \(c_k(x)^2+s_k(x)^2=1\).  Therefore (1) gives the exact
identity

\[
 H''_L(A_{k,c})+H''_L(A_{k,s})
 =\frac23 L^4\sum_{\mu,a}(e^a_\mu)^2.\tag{2}
\]

There is no dependence on \(k\).  After the usual \(L^{-4}\) external-mode
normalization, this is the constant \(\frac23\lVert e\rVert^2\).

The same conclusion holds on side four with the established \(1/256\)
normalization, but (2) is an arbitrary-side identity and does not need the
side-four character table.

## Consequence for the physical two-point kernel

A transverse gauge-invariant two-point function has the form

\[
 \Gamma_{\mu\nu}^{(2)}(p)
 =(\delta_{\mu\nu}\widehat p^2-\widehat p_\mu\widehat p_\nu)\rho(p)
\]

and hence vanishes at \(p=0\).  The bare Haar diagonal (2) is a nonzero
momentum-independent local term whenever \(e\ne0\).  Therefore it cannot be
identified, by itself, with a transverse physical vacuum-polarization
contribution.

This corrects a potential category error.  In the one-loop effective action,
the Haar density is a fluctuation-measure insertion.  Its contribution to a
background two-jet requires the background dependence and Wick contraction
against the same free Green operator; the bare expression (2) is only one
local ingredient of that calculation.  If a proposed contraction instead
treated (2) itself as the physical two-point kernel, it would violate the Ward
identity at \(p=0\).

Accordingly, the first analytic target inside the arbitrary-side
reduced-FP/Green construction is to derive the *full* Ward-symmetric
Wilson--FP--Haar background two-jet before estimating any term absolutely.
Only then is it meaningful to isolate and bound its uniform \(p^2\)
coefficient.
