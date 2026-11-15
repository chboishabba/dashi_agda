# Exact Fourier normalization on the literal side-four carrier

## Scope and source

This note completes the finite calculation that follows the explicit
Gaussian-rational \(C_4\) character table in
`BalabanSide4ScalarGreenKernelComputed.agda`.  It is not a continuum Fourier
argument and it does not assert a beta-function estimate.

Primary reference: Walter Rudin, *Fourier Analysis on Groups*, Wiley, 1962.
No DOI was assigned to this monograph.

The coordinate carrier is

\[
X=K=C_4^4,\qquad |X|=|K|=4^4=256,
\]

and its literal character is the product already used by the Green-kernel
calculation,

\[
 \chi_k(x)=\prod_{\mu=0}^{3}\chi^{(1)}_{k_\mu}(x_\mu),
 \qquad \chi^{(1)}_a(b)=i^{ab}.
\]

All values are Gaussian rationals, so every displayed equality below is a
finite rational identity after replacing \(i\) by the pair \((0,1)\).

## The one-coordinate calculation

For \(a,b\in C_4\), put \(d=a-b\pmod 4\).  Then

\[
\begin{aligned}
 \sum_{x=0}^{3}\chi^{(1)}_a(x)\overline{\chi^{(1)}_b(x)}
 &=\sum_{x=0}^{3}i^{dx}\\
 &=
 \begin{cases}
  4,&d=0,\\
  1+i-1-i=0,&d=1,\\
  1-1+1-1=0,&d=2,\\
  1-i-1+i=0,&d=3.
 \end{cases}
\end{aligned}
\]

Thus the exact finite table is

\[
 \sum_{x=0}^{3}\chi^{(1)}_a(x)\overline{\chi^{(1)}_b(x)}
 =4\,\delta_{ab}.\tag{1}
\]

`BalabanSide4GaussianCharacterOrthogonalityExact.agda` contains all sixteen
instances of (1) as direct rational-ring proof terms.  Its proof level remains
`conditional`, rather than `machineChecked`, because this workstream is under
an explicit no-Agda-run instruction.

## Four-coordinate orthogonality

Finite distributivity permits the four sums to be evaluated independently:

\[
\begin{aligned}
 \sum_{x\in C_4^4}\chi_k(x)\overline{\chi_\ell(x)}
 &=\prod_{\mu=0}^{3}
   \left(\sum_{x_\mu\in C_4}
    \chi^{(1)}_{k_\mu}(x_\mu)
    \overline{\chi^{(1)}_{\ell_\mu}(x_\mu)}\right)\\
 &=\prod_{\mu=0}^{3}4\delta_{k_\mu\ell_\mu}\\
 &=256\,\delta_{k\ell}.\tag{2}
\end{aligned}
\]

This is the correct normalization for the concrete side-four character table;
there is no unspecified volume factor.

## Inversion and Parseval with their literal constants

For a Gaussian-rational scalar field \(f:X\to\mathbb Q(i)\), define the
unnormalized forward transform by

\[
 \widehat f(k)=\sum_{x\in X}\overline{\chi_k(x)}f(x).
\]

Equation (2) gives, with no limiting operation,

\[
 f(x)=\frac1{256}\sum_{k\in K}\chi_k(x)\widehat f(k),\tag{3}
\]

and for scalar fields \(f,g\),

\[
 \sum_{x\in X}\overline{f(x)}g(x)
 =\frac1{256}\sum_{k\in K}
   \overline{\widehat f(k)}\widehat g(k).\tag{4}
\]

Equations (3)--(4) are the exact finite normalizations that a literal
plane-wave contraction must use.  They rule out the common normalization error
of treating the coordinate-space contractions as if their Fourier transform
had unit volume.

## What remains physically nontrivial

This calculation only turns the side-four Green-kernel data into a normalized
finite Fourier carrier.  It does **not** establish any of the following:

\[
 \Gamma^{(2)}_{\mathrm{Wilson+FP+Haar}}(p)
 =\Gamma^{(2)}_{\mathrm{literal\ coordinate\ action}}(p),
 \qquad
 \beta_j(G)\ge b_*>0.
\]

The shortest next physical assertion is a same-object contraction theorem:
the coordinate-space quadratic, cubic-bubble, quartic, Haar, and reduced-FP
terms already written in `BalabanP33LiteralWilsonFPHaarFourthJetExact.agda`
must be paired with the transverse external characters using (2)--(4), with
the Ward projection and the same \(1/256\) normalization.  Only after that
identity is proved can the four-orbit finite remainder enclosure be regarded
as an enclosure of the literal Wilson/reduced-FP/Haar beta coefficient.
