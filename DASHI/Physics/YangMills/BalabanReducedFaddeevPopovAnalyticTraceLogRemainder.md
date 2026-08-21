# Reduced Faddeev--Popov trace-log: explicit fifth-order tail

## Sources

- L. D. Faddeev and V. N. Popov, *Feynman Diagrams for the Yang--Mills
  Field*, Physics Letters B 25 (1967), 29--30,
  DOI [10.1016/0370-2693(67)90067-6](https://doi.org/10.1016/0370-2693(67)90067-6).
- Nicholas J. Higham, *Functions of Matrices: Theory and Computation*, SIAM
  (2008), DOI [10.1137/1.9780898717778](https://doi.org/10.1137/1.9780898717778).

## Finite reduced-carrier estimate

Let \(M(g)=M_0(I+X(g))\) be the reduced Faddeev--Popov operator after the
anchored flat inverse has been factored out.  On the existing physical side-four
carrier, `X(g)` is a \(765\times765\) rational matrix at each Taylor
coefficient.  If an operator norm satisfies

\[
\lVert X(g)\rVert\leq \rho<1,
\]

then the principal finite-dimensional trace logarithm has the exact expansion

\[
-\log\det(I+X)
=\sum_{m=1}^{4}\frac{(-1)^m}{m}\operatorname{Tr}(X^m)+R_5(X),
\]

with the explicit bound

\[
 |R_5(X)|\leq \frac{765\,\rho^5}{5(1-\rho)}
 = \frac{153\,\rho^5}{1-\rho}. \tag{FP}
\]

In particular, if the literal background/operator comparison proves
\(\lVert X(g)\rVert\leq K|g|\) on \(|g|\leq g_*\) with
\(Kg_*<1\), then

\[
 |R_5(X(g))|
 \leq \frac{153 K^5}{1-Kg_*}|g|^5. \tag{FP-g}
\]

This supplies the exact analytic tail needed to identify the repository's
first four reduced-ghost trace-log coefficients with the actual finite
determinant on the selected ball.  It does not itself prove the required
operator comparison \(\lVert X(g)\rVert\leq K|g|\), nor does a fixed
765-dimensional bound establish the arbitrary-volume local trace estimate.

## Proof

For \(\lVert X\rVert<1\), the absolutely convergent matrix logarithm series
is

\[
-\log\det(I+X)=\sum_{m\geq1}\frac{(-1)^m}{m}\operatorname{Tr}(X^m).
\]

For a \(d\times d\) matrix, the trace bound
\( |\operatorname{Tr}(X^m)|\leq d\lVert X\rVert^m \) follows by applying
the operator norm to each diagonal matrix element (or from the trace norm).
Thus, with \(d=765\),

\[
\begin{aligned}
 |R_5(X)|
 &\leq 765\sum_{m\geq5}\frac{\rho^m}{m}\\
 &\leq \frac{765}{5}\sum_{m\geq5}\rho^m
 =\frac{765\rho^5}{5(1-\rho)}.
\end{aligned}
\]

Substitution of \(\rho=K|g|\leq Kg_*\) gives (FP-g).

## Physical boundary

The bound is deliberately local to the explicit reduced carrier.  Promoting it
to the RG trajectory requires a volume-independent **localized trace norm** or
polymer norm for the perturbation \(X(g)\); a global matrix trace norm would
grow with volume and is not an acceptable substitute.
