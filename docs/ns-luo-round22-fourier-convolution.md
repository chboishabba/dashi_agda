# Round 22 physical Fourier convolution bridge

Round 22 now connects the finite defect-diffusion carrier to literal periodic vorticity modes rather than stopping at anonymous rational eigenvalues.

## Mode-pair defect

`NSTriadKNLuoGalerkinFourierModePairExact.agda` reuses the repository's `NonzeroVorticityMode` carrier. For two transverse modes \(k,\ell\), it defines

\[
A(k,\ell)=|\widehat\omega(k)\times\widehat\omega(\ell)|^2
\]

and constructs the corresponding pair-frequency diffusion cell with eigenvalues \(|k|^2\) and \(|\ell|^2\). Consequently,

\[
2\nu\kappa A(k,\ell)
\le
\nu\bigl(|k|^2+|\ell|^2\bigr)A(k,\ell)
\]

whenever both inputs lie above the shell floor \(\kappa\).

The explicit witness

\[
k=e_1,\qquad \ell=-e_1,\qquad
\widehat\omega(k)=e_2,\qquad
\widehat\omega(\ell)=e_3
\]

has

\[
k+\ell=0,\qquad A(k,\ell)=1,\qquad
\nu(|k|^2+|\ell|^2)A=2
\]

for unit viscosity. Thus output-frequency damping is genuinely the wrong variable for high-high interactions: the output can be zero while both input frequencies retain full diffusion.

## Fourier vorticity nonlinearity

`NSTriadKNLuoGalerkinFourierVorticityConvolutionExact.agda` defines the real carrier of the periodic Biot--Savart velocity by

\[
\widehat u(p)=|p|^{-2}\bigl(p\times\widehat\omega(p)\bigr),
\]

with the common complex phase factored out. The ordered vorticity interaction at output \(p+r\) is

\[
F(p,r)
=
\bigl(\widehat\omega(p)\cdot r\bigr)\widehat u(r)
-
\bigl(\widehat u(p)\cdot r\bigr)\widehat\omega(r).
\]

The finite convolution contains both ordered pairs. Using transversality of each vorticity and velocity mode, the module proves

\[
(p+r)\cdot\bigl(F(p,r)+F(r,p)\bigr)=0.
\]

This is the exact Fourier preservation of the divergence-free vorticity constraint at the symmetrized pair level.

## Remaining interface

The following are still analytic/formal producers rather than proved consequences:

- restoration of the common complex phase and reality pairing;
- finite enumeration of all Galerkin pairs \(p+r=k\);
- proof that the literal shell-range constructors exhaust the projected convolution;
- derivation of the five named source classes with constants uniform in \(q,Q,N\);
- critical taxation of those sources with total viscosity coefficient below one.

Primary metadata in the Agda headers includes Roger Temam, DOI `10.1090/chel/343`; Jean-Michel Bony, DOI `10.24033/asens.1404`; Bahouri--Chemin--Danchin, DOI `10.1007/978-3-642-16830-7`; Constantin--Fefferman, DOI `10.1512/iumj.1993.42.42034`; and Cheskidov--Shvydkoy, DOI `10.1007/s00021-014-0167-4`.
