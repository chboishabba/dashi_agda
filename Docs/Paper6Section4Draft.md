# 4. The Wolfenstein A Parameter

> **Superseded 2026-05-31.** This section is retained as a historical
> diagnostic route.  The current ledger treats `A` as a Wolfenstein input or
> quotient unless independently derived from carrier arithmetic.  No such
> carrier derivation is currently promoted.  Use
> `Paper6FinalDraftOutline.md` for the current Paper 6 boundary.

The Wolfenstein parameter \(A\) is not introduced here as an independent
arithmetic carrier.  In the Wolfenstein convention it is defined, to the order
relevant for this diagnostic, by
\[
|V_{cb}| = A\lambda^2,
\]
and hence
\[
A = \frac{|V_{cb}|}{\lambda^2}.
\]
The DASHI value of \(A\) therefore follows from the two carrier quantities
already described in Sections 2 and 3.

Using
\[
\lambda_{\mathrm{carrier}} = 0.22441
\]
from the discriminant \(-3\) Cabibbo lane, and
\[
|V_{cb}|_{\mathrm{carrier}} = 0.04072
\]
from the \(T_{13}\) Hecke correspondence with modular-volume
normalisation, one obtains
\[
A_{\mathrm{carrier}}
= \frac{0.04072}{(0.22441)^2}
= 0.8086.
\]
The comparison value used in this draft is
\[
A_{\mathrm{PDG}} = 0.814,
\]
so the relative discrepancy is
\[
\frac{0.8086 - 0.814}{0.814} = -0.67\%.
\]

This computation should not be read as a third independent CKM derivation.
The parameter \(A\) is structurally a quotient of two lower-level
Wolfenstein-sector quantities.  Its carrier status is therefore inherited:
\[
A_{\mathrm{carrier}}
=
\frac{
\left(\alpha_1^2 \cdot 14 \cdot \frac{4\pi}{3\sqrt{6}}\right)
}{
\left(\alpha_1\pi\sqrt{3}\right)^2
}.
\]
The numerator is the \(|V_{cb}|\) carrier, whose arithmetic content is the
degree of the inert correspondence \(T_{13}\) on the Hilbert modular surface
for \(\mathbb{Q}(\sqrt{21})\), together with the stated modular-volume
normalisation.  The denominator is the square of the Cabibbo carrier, whose
geometric content is the discriminant \(-3\) Eisenstein lane.  Thus the
formula for \(A\) is a ratio of two independently specified carrier
constructions rather than a new primitive constant.

There is a useful distinction here between tautology and prediction.  If
\(\lambda\) and \(|V_{cb}|\) were taken from experiment and \(A\) were then
formed by division, the result would be only a change of variables inside the
Wolfenstein parametrisation.  In the present draft the inputs are not inserted
as CKM fit values: \(\lambda\) is supplied by the disc \(-3\) CM geometry, and
\(|V_{cb}|\) is supplied by the \(T_{13}\) / modular-volume lane.  The
resulting agreement of \(A\) is therefore non-trivial as a consistency check
between independently derived carrier quantities.

At the same time, the conclusion remains deliberately limited.  The paper does
not claim an independent derivation of \(A\) beyond the derivations of
\(\lambda\) and \(|V_{cb}|\), nor does it promote this quotient to a full CKM
matrix theorem.  The \(A\)-value records that the two promoted carrier lanes
are mutually compatible with the observed Wolfenstein hierarchy at the
sub-percent level.
