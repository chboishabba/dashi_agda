# Uniform fifth-order remainder for a literal SU(2) Wilson plaquette

## Sources

- Kenneth G. Wilson, *Confinement of Quarks*, Physical Review D 10 (1974),
  2445--2459, DOI [10.1103/PhysRevD.10.2445](https://doi.org/10.1103/PhysRevD.10.2445).
- Brian C. Hall, *Lie Groups, Lie Algebras, and Representations: An
  Elementary Introduction*, 2nd ed., Springer (2015),
  DOI [10.1007/978-3-319-13467-3](https://doi.org/10.1007/978-3-319-13467-3).

## Statement

Take the four literally oriented factors of one SU(2) plaquette in the order
used by `BalabanP33RationalQuaternionWilsonFourthJetExact`:

\[
P(t)=U_0e^{\sigma_0tX_0}U_1e^{\sigma_1tX_1}
     e^{\sigma_2tX_2}U_2^{-1}e^{\sigma_3tX_3}U_3^{-1},
\]

where the placement of the inverse-oriented exponentials is understood exactly
as in the source module (the displayed typography only records their four
generators), \(\sigma_i\in\{\pm1\}\), and all `U` are unit quaternions.
Put \(r_i=\lVert X_i\rVert\) and \(R=r_0+r_1+r_2+r_3\).  For the Wilson
plaquette scalar \(W(t)=1-\operatorname{Re}P(t)\),

\[
\left|W(t)-\sum_{k=0}^{4}\frac{W^{(k)}(0)}{k!}t^k\right|
\leq\frac{R^5|t|^5}{120}. \tag{W}
\]

The derivatives through order four are exactly the ordered noncommutative
Leibniz jets already materialized in
`BalabanP33RationalQuaternionWilsonFourthJetExact.agda`.  Thus (W) supplies
the missing analytic remainder behind that literal jet, with no volume or
cutoff-dependent constant per plaquette.

## Proof

For real `s`, unit-quaternion multiplication and the SU(2) exponential preserve
the Euclidean quaternion norm.  Repeated product differentiation gives

\[
P^{(5)}(s)=
 \sum_{n_0+\cdots+n_3=5}
 \frac{5!}{n_0!\cdots n_3!}\,
 F_{0,n_0}(s)F_{1,n_1}(s)F_{2,n_2}(s)F_{3,n_3}(s),
\]

where each factor has norm at most \(r_i^{n_i}\): the fixed links and the
remaining exponentials have norm one, and differentiating an exponential
`n_i` times inserts \((\sigma_iX_i)^{n_i}\).  Submultiplicativity and the
multinomial theorem give

\[
 \lVert P^{(5)}(s)\rVert\leq(r_0+r_1+r_2+r_3)^5=R^5.
\]

Taking a real part cannot increase the norm, so \(|W^{(5)}(s)|\le R^5\).
Taylor's integral remainder, or the real-variable Lagrange remainder, now
gives (W).

## Lattice consequence and boundary

In a four-dimensional periodic lattice, every positive bond occurs in exactly
six oriented plaquettes: for each of the other three axes it occurs once at
each of the two translated plaquette positions.  The convexity inequality

\[
(r_0+r_1+r_2+r_3)^5\leq4^4(r_0^5+r_1^5+r_2^5+r_3^5)
\]

therefore gives

\[
\sum_p R_p^5\leq 6\cdot4^4\sum_b r_b^5
=1536\sum_b r_b^5.
\]

Summing (W) consequently produces the explicit Wilson local-density bound

\[
\left|\mathcal R_{W,5}(g)\right|
\leq \frac{64}{5}|g|^5\sum_b r_b^5. \tag{W-volume}
\]

If the selected small-field ball also has the pointwise amplitude bound
\(r_b\leq h\), then

\[
\left|\mathcal R_{W,5}(g)\right|
\leq \frac{64}{5}|g|^5h^3\sum_b r_b^2. \tag{W-energy}
\]

Together with the Haar estimate
\(mathcal R_H\leq\frac{2}{175}|g|^4\sum_b r_b^4\), the same small-field
ball gives

\[
0\leq\mathcal R_H\leq\frac{2}{175}|g|^4h^2\sum_b r_b^2. \tag{H-energy}
\]

Thus the explicit Wilson and Haar analytic remainders are locally dominated
by the same quadratic bond energy with coefficients
\(\frac{64}{5}|g|^5h^3\) and
\(\frac{2}{175}|g|^4h^2\), respectively.  This is the form a small-field
polymer majorant can absorb.  It is not yet a beta remainder bound: the missing
work is to prove a cutoff-uniform polymer/Green majorant for the FP, gauge and
localization channels and then perform the required low-order cancellations.

There is also a useful chart-only simplification.  The shared Haar chart
condition \(|g|h\leq\tfrac12\) implies

\[
\frac{64}{5}|g|^5h^3+
\frac{2}{175}|g|^4h^2
\leq\left(\frac85+\frac1{350}\right)g^2
=\frac{561}{350}g^2. \tag{WH-chart}
\]

Hence if the gauge-fixed quadratic reference action obeys
\(\mathcal Q(q)\geq\lambda\sum_b r_b^2\) on the selected slice, then the
Wilson-plus-Haar analytic tails consume at most half this local gap whenever

\[
g^2\leq\frac{175\lambda}{561}. \tag{WH-absorb}
\]

This explicit threshold isolates the unresolved analytic content: establish the
same \(\lambda\), chart radius and localized FP/gauge/localization bounds on
the literal Bałaban state, rather than merely asserting that a sufficiently
small coupling exists.
