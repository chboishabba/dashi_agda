# Explicit SU(2) Haar chart remainder

## Sources

- Brian C. Hall, *Lie Groups, Lie Algebras, and Representations: An
  Elementary Introduction*, 2nd ed., Springer (2015),
  DOI [10.1007/978-3-319-13467-3](https://doi.org/10.1007/978-3-319-13467-3).
- E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed.
  (1927), Ch. VII: Euler's product for sine.  No DOI assigned.

## Statement

Let `X` be an SU(2) tangent generator in the quaternion convention and put
`r² = |X|²`.  The exponential-coordinate Haar density is

\[
J(gX)=\operatorname{sinc}(gr)^2,
\qquad \operatorname{sinc}(x)=\frac{\sin x}{x}.
\]

For \(|g|r\leq\tfrac12\), its negative logarithm obeys the **uniform,
one-link bound**

\[
0\leq -\log J(gX)-\frac{g^2r^2}{3}
 \leq \frac{2}{175}g^4r^4. \tag{H}
\]

Consequently, on any finite periodic lattice, provided every link is in this
same chart,

\[
0\leq -\log J_{\rm Haar}(gq)
 -\frac{g^2}{3}\sum_b |q_b|^2
\leq \frac{2}{175}g^4\sum_b |q_b|^4. \tag{H-volume}
\]

The constant is independent of volume, cutoff and the link; only the displayed
local fourth-power sum remains.  This is precisely the Haar part of the
fourth-order local-remainder estimate, not a claim about the full Wilson/FP
beta coefficient.

## Proof

Set \(x=|g|r\).  Euler's product gives, for \(|x|<\pi\),

\[
-\log\operatorname{sinc}(x)^2
=2\sum_{n\geq1}-\log\!\left(1-
  \frac{x^2}{n^2\pi^2}\right).
\]

For \(0\leq y<1\), the power series for \(-\log(1-y)\) gives

\[
0\leq -\log(1-y)-y
=\sum_{m\geq2}\frac{y^m}{m}
\leq \frac{y^2}{2(1-y)}. \tag{1}
\]

The linear terms in the product are exactly

\[
2\sum_{n\geq1}\frac{x^2}{n^2\pi^2}
=\frac{x^2}{3},
\]

using \(\sum n^{-2}=\pi^2/6\).  If \(x\leq1/2\), then

\[
y_n=\frac{x^2}{n^2\pi^2}\leq\frac1{36},
\qquad \frac1{1-y_n}\leq\frac{36}{35},
\]

where the elementary lower bound \(\pi^2\geq9\) suffices.  Applying (1)
termwise therefore yields

\[
\begin{aligned}
0 &\leq -\log\operatorname{sinc}(x)^2-\frac{x^2}{3}\\
  &\leq \sum_{n\geq1}\frac{y_n^2}{1-y_n}\\
  &\leq \frac{36}{35}\frac{x^4}{\pi^4}
       \sum_{n\geq1}\frac1{n^4}
   =\frac{36}{35}\frac{x^4}{90}
   =\frac{2}{175}x^4,
\end{aligned}
\]

using \(\sum n^{-4}=\pi^4/90\).  Substitution \(x=|g|r\) proves (H), and
summing the nonnegative one-link inequalities proves (H-volume).

## What this discharges, and what it does not

This supplies the analytic fourth-order **Haar chart** estimate with a visible
constant.  It does not identify the chart action with the complete Haar factor
on a common weak-coupling ball, contract the resulting term into a
background-dependent polarization, or bound the Wilson, reduced-FP,
localization and history remainders.  Those remain separate physical estimates.
