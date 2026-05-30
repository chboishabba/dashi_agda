# 3. The Vcb Lane from the T13 Hecke Correspondence

The \(|V_{cb}|\) diagnostic uses the interaction between the discriminant
\(-3\) and \(-7\) quark lanes.  Their product field has real quadratic
subfield
\[
\mathbb{Q}(\sqrt{(-3)(-7)}) = \mathbb{Q}(\sqrt{21}).
\]
The corresponding Hilbert modular surface is the natural home for the
two-lane Hecke correspondence.

The relevant prime is \(p = 13\).  It is inert in
\(\mathbb{Q}(\sqrt{21})\), since
\[
\left(\frac{21}{13}\right) = -1.
\]
For an inert prime on this Hilbert modular surface, the Hecke correspondence
\(T_p\) has degree \(p+1\).  Hence
\[
\deg(T_{13}) = 13 + 1 = 14.
\]
This explains the base degree in the \(2\)-\(3\) CKM lane without appealing to
the older point-count pattern match.

The modular-volume normalisation uses the \(N_3 = 7\) target lane volume and
the geometric mean of the source-lane index functions.  With
\[
\psi(N) = N\prod_{p\mid N}\left(1+\frac{1}{p}\right),
\]
we have \(\psi(4)=6\), \(\psi(3)=4\), and
\[
\frac{\mathrm{vol}(X_0(7))}{\sqrt{\psi(4)\psi(3)}}
= \frac{8\pi/3}{\sqrt{24}}
= \frac{4\pi}{3\sqrt{6}}.
\]

The carrier formula for the \(|V_{cb}|\) lane is therefore
\[
\boxed{|V_{cb}| =
\alpha_1^2 \cdot 14 \cdot \frac{4\pi}{3\sqrt{6}}}.
\]
Numerically,
\[
|V_{cb}|_{\mathrm{carrier}} = 0.04072.
\]
The reference comparison value used in this draft is
\[
|V_{cb}|_{\mathrm{PDG}} = 0.04080,
\]
giving
\[
\frac{0.04072 - 0.04080}{0.04080} = -0.20\%.
\]

This result is a sub-percent arithmetic diagnostic for the \(V_{cb}\)-scale
Wolfenstein lane.  It does not by itself derive the full CKM matrix.  The
\((1,3)\) entry and the CP phase require additional carrier mechanisms not
currently identified.
