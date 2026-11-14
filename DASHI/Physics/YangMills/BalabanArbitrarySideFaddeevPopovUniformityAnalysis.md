# Why a global reduced-FP trace-log expansion cannot be volume-uniform

## Sources

L. D. Faddeev and V. N. Popov, “Feynman Diagrams for the Yang--Mills Field,”
*Physics Letters B* **25** (1967), 29–30.
DOI: [10.1016/0370-2693(67)90067-6](https://doi.org/10.1016/0370-2693(67)90067-6).

Nicholas J. Higham, *Functions of Matrices: Theory and Computation*, SIAM,
2008. DOI: [10.1137/1.9780898717778](https://doi.org/10.1137/1.9780898717778).

Tadeusz Bałaban, “Propagators for Lattice Gauge Theories in a Background
Field,” *Communications in Mathematical Physics* **99** (1985), 389–434.
DOI: [10.1007/BF01240355](https://doi.org/10.1007/BF01240355).

## The finite side-four estimate is not an arbitrary-volume estimate

The existing exact finite FP jet uses

\[
 M_A M_0^{-1}=I+X_A
\]

on a reduced \(765\)-coordinate side-four ghost carrier.  Its analytic
remainder bound is

\[
 |R_5|\le \frac{153\rho^5}{1-\rho},\qquad \lVert X_A\rVert\le\rho<1.
 \tag{1}
\]

The coefficient \(153=765/5\) is the dimension cost in
\(|\operatorname{Tr}X^m|\le765\lVert X\rVert^m\).  For an arbitrary side
\(L\), the reduced SU(2)-adjoint ghost carrier has dimension

\[
 d_L=3(L^4-1),
\]

so the identical global argument gives only

\[
 |R_{5,L}|\le
 \frac{3(L^4-1)\rho_L^5}{5(1-\rho_L)}.\tag{2}
\]

It is necessarily extensive.  No manipulation of the finite trace-log series
can make (2) an absolute volume-uniform bound, because the log determinant is
itself an extensive quantity.

## The infrared obstruction in the global inverse

On the zero-mean scalar sector of the periodic \(L^4\) lattice, the flat
Faddeev--Popov operator is the lattice Laplacian.  Its Fourier eigenvalues are

\[
 \lambda_L(n)=4\sum_{\mu=0}^{3}\sin^2\!\left(\frac{\pi n_\mu}{L}\right),
 \qquad n\ne0.
\]

The spectral gap is attained at \(n=(1,0,0,0)\):

\[
 \lambda_{\min}(L)=4\sin^2(\pi/L),
 \qquad \lVert M_0^{-1}\rVert_{2\to2}
 =\frac1{4\sin^2(\pi/L)}\sim\frac{L^2}{4\pi^2}.\tag{3}
\]

Consequently, an estimate formed only from a global bound on
\(M_A-M_0\) followed by

\[
 \lVert(M_A-M_0)M_0^{-1}\rVert
 \le\lVert M_A-M_0\rVert\,\lVert M_0^{-1}\rVert
\tag{4}
\]

cannot yield a fixed weak-coupling radius uniform in \(L\), unless the
perturbation is given an artificial \(L^{-2}\) smallness.  This is a direct
infrared obstruction to promoting the present finite-dimensional determinant
proof by a global Neumann norm.

## The correct replacement: density/locality, not a global determinant

For a translation-invariant relative operator with
\(\lVert X_L\rVert\le\rho<1\), the normalized trace does have the uniform
bound

\[
 \frac1{L^4}\,|\operatorname{Tr}X_L^m|
 \le \frac{d_L}{L^4}\rho^m
 \le3\rho^m.
\]

Hence its **trace density** remainder obeys

\[
 \frac1{L^4}|R_{5,L}|
 \le\frac{3\rho^5}{5(1-\rho)}.\tag{5}
\]

Formula (5) removes only the unavoidable volume factor.  It does not cure
the \(L^2\) divergence in (3), and it does not apply directly to a local
background or marked external two-jet, which breaks translation invariance.

The required physical theorem is therefore a localized replacement for (4):
after inserting the two external background variations, prove a polymer or
weighted-kernel estimate for the connected trace density, with its two marked
bonds fixed and all unmarked internal sums summable uniformly in \(L\).  Such
an estimate can exploit derivatives at the FP vertices and the Ward
cancellation before the massless inverse is bounded.  A global
\(\lVert M_0^{-1}\rVert\) estimate cannot.

This identifies a real analytic frontier:

\[
 \boxed{\text{derive the marked, connected reduced-FP two-jet in a local
 norm before taking the arbitrary-volume limit.}}
\]

It is stronger and more precise than asking for “an arbitrary-side FP
determinant,” and it is the first missing ingredient that could legitimately
feed the uniform physical beta estimate.
