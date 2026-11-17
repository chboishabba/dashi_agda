# Original Bishop K04d/K05: analytic proof and effective majorants

2026-11-06. Selected data: original pinned vendor/bishop Real, RealProperties and Sequence; original source Exp.bishopExp, NativeLog.sourceNegativeLogValue, Machin.bishopAtanHalfBall, and BishopSetoidComplexExact.expC.

**Mathematical derivation, not Agda acceptance.** The algebra below is mathematically provable constructively. The native termwise differentiation, nested-composition interchange and limit transports must still be elaborated and checked by Agda before any theorem is marked machine-checked.

## Shared finite geometric identity

For P_N(q) = sum_(k=0)^(N-1) q^k,

\[
(1-q)P_N(q)=1-q^N. \tag{F1}
\]

This exact all-N Bishop-real theorem is source-written in BishopLogAtanFiniteDerivativeGeometricExact.geometricPolynomialTelescope. For the literal negative-log and arctangent series, their finite formal derivatives are respectively P_N(x) and P_N(-t²), so

\[
(1-x)P_N(x)=1-x^N,\qquad
(1+t^2)P_N(-t^2)=1-(-t^2)^N. \tag{F2}
\]

On |t| <= 1/2 the second remainder is bounded by 4^(-N). On |x| <= r < 1 the first remainder is bounded by r^N. To turn finite formal derivatives into original Bishop factor derivatives, reuse BishopFactorDerivativeExact, the source power derivative and a uniform derivative-limit interchange theorem; F1/F2 do not by themselves prove differentiation of the infinite sums.

## Original negative logarithm and exponential

Define the *literal source* L(x)=sum_(k>=1) x^k/k, with 0<x<1, and F(x)=exp_B(-L(x)). Choose two strict radii x<r<R<1. The nonnegative majorant is

\[
M_L(R)=\sum_{k\ge1}\frac{R^k}{k}\le\frac R{1-R}.
\]

The total absolute mass of every ordered nested exponential composition is

\[
\sum_{m\ge0}\frac1{m!}
 \sum_{k_1,\ldots,k_m\ge1}
 \frac{R^{k_1+\cdots+k_m}}{k_1\cdots k_m}
=\exp_B(M_L(R))
\le\exp_B\!\left(\frac R{1-R}\right)=E_L(R). \tag{L1}
\]

The equality is an assertion about constructive limits of finite nonnegative sums; use existing Bishop finite Cauchy row/triangle reindexing and unique absolutely convergent limits. If a_n are the reorganized coefficients of exp(-L), the effective degree-tail bound is

\[
\sum_{n>N}|a_n|r^n\le
 E_L(R)(r/R)^{N+1}. \tag{L2}
\]

For the formal power series, L'(X)=1/(1-X). Therefore F'(X)=-F(X)/(1-X), F(0)=1, and, writing F(X)=sum a_n X^n,

\[
a_1=-1,\qquad (n+1)a_{n+1}+(1-n)a_n=0\quad(n\ge1). \tag{L3}
\]

Hence a_2=0 and by induction a_n=0 for every n>=2. Existing BishopNegativeLogExpFormalRecurrenceUniquenessExact proves the universal solved-recursion uniqueness. Combining the actual native nested-series-to-coefficient equality justified by L1/L2 with this coefficient theorem and Bishop limit uniqueness yields, on the original carrier,

\[
\boxed{\exp_B(-L(x))\simeq 1-x}. \tag{L4}
\]

At original x_n=(n+1)/(n+2), the rational gap is 1/(n+2). Use the already established original exp(x)exp(-x)=1 and BishopInverseSquareProductExact.inverseFromCancellation to derive

\[
\boxed{\exp_B(L(x_n))\simeq n+2}. \tag{L5}
\]

The source-written all-N compiler is BishopK04dNatLogFromOriginalGapExact. It is *conditional on L4* until that source-composition proof is kernel accepted.

## Original arctangent and Cayley phase

On the original Machin source define

\[
A(t)=\sum_{k\ge0}(-1)^k t^{2k+1}/(2k+1).
\]

Set r=1/4 and R=1/2. The absolute coefficient majorant at R is at most R/(1-R²)=2/3. For G(t)=exp_C(2i A(t)) the total nested composition majorant and effective degree-tail estimate are

\[
\sum_{n\ge0}|g_n|R^n\le
 \exp_B(2R/(1-R^2))=\exp_B(4/3)=E_A, \tag{A1}
\]
\[
\sum_{n>N}|g_n|r^n\le E_A\,2^{-(N+1)}. \tag{A2}
\]

F2, its geometric remainder 4^(-N), native source term derivatives, and uniform interchange imply A'(t)=1/(1+t²) on |t|<=r. Factorial absolute convergence and the original Round11 signed even/odd factorial encoding then give the formal differential identity

\[
(1+t^2)G'(t)=2iG(t),\qquad G(0)=1. \tag{A3}
\]

For G(t)=sum g_n t^n, the finite coefficient recurrence is

\[
g_1=2i,\quad
(n+1)g_{n+1}+(n-1)g_{n-1}=2ig_n\quad(n\ge1). \tag{A4}
\]

The Cayley series C(t)=(1+it)/(1-it)=1+sum_(n>=1)2i^n t^n satisfies the same recurrence. Its quotient-rule numerator identity

\[
N'D-ND'=2iN,\qquad N=1-t^2+2it,\quad D=1+t^2 \tag{A5}
\]

is an unconditional all-rational polynomial theorem newly source-written as BishopCayleyRationalDifferentialEquationExact.cayleyQuotientDifferentialPolynomialExact, reusing the original rational Q[i] carrier. Formal recurrence uniqueness gives G=C. The degree-tail bound A2 permits the actual absolute series rearrangement and evaluation:

\[
\boxed{\exp_C(2i A(t))\simeq_C (1+it)/(1-it)}
\quad (|t|\le1/4). \tag{A6}
\]

Both original points 1/5 and 1/239 belong to the interval. The source-written BishopMachinTwoPointCayleyCompositionExact consumes those two evaluations, uses the existing original K05 signed-factorial product, and gives

\[
\exp_C(2i(4A(1/5)-A(1/239)))
=C(1/5)^4\overline{C(1/239)}=i.
\]

The original quarter equality, first sine zero and sign proofs are then derivable via the already-written consumers. **The source analytic passage A1/A2/A3/A6 still requires native Agda acceptance**; the finite Cayley polynomial theorem alone is insufficient.

## Original exponential and Dirichlet continuity

On any bounded real interval |x|<=M and cutoff N>=2M, the exact factorial-tail domination is

\[
\sum_{k\ge N} M^k/k! \le 2M^N/N!. \tag{C1}
\]

This follows from the consecutive-term ratio <=1/2, so it is an effective Bishop-real uniform modulus. It applies to original exponential and original signed sine/cosine series, and the finite power series are sequentially continuous by vendor Sequence algebra. Uniform approximation plus BishopUniformLimitSequentialContinuityExact then proves original exp_B, sin_B, cos_B sequential continuity, and thus componentwise source exp_C continuity.

For the original complex Dirichlet term exp_C(-s L_n), scalar multiplication and source exp_C continuity give finite-term continuity. The source Basel bound and BishopDirichletUniformBaselTailsExact give a single cutoff for all Re(s)>2, so the actually constructed Dirichlet sum is sequentially continuous. The new concrete source curve s_eta(t)=3+t²+i eta has independently proven Re(s)>2 membership and does not stand in for all-neighborhood complex analyticity.

**Irreducible original semantic weld:** RiemannAnalyticSubstrate.ZetaHalfPlaneLayer.ZetaEqualsDirichletSeries and CompletedRiemannZeta.CompletedDefinition are Set-valued descriptions, not typed equalities of source function evaluations. They do not prove original zetaHalfPlane equals the Bishop Dirichlet sum or original xi equals (1/2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s). The exact original function instance, selected gamma factor, original pi/exponential and proof-relevant equality must be recovered or constructed. No arbitrary constant function or fake CompletedDefinition witness may be substituted.

## Kernel completion conditions

1. Native Bishop source finite-term derivative normalization and uniform derivative-limit interchange for F2, at the original log and arctan definitions.
2. Native absolutely-convergent nested exponential composition/reindexing with effective radius-gap estimates L1/L2 and A1/A2, yielding unconditional original L4 and A6.
3. Native factorial C1 continuity of original exp/sin/cos and actual finite Dirichlet sums, followed by existing original Basel uniform-limit compiler.
4. Concrete actual zetaHalfPlane/xi/gamma semantics with proof-relevant value identities, not opaque Set labels.
5. Exact-head run of scripts/run_agda29_parallel_check.sh --safe for all newly written owners and all three golden TOE roots, retaining evidence.

**No completion claim:** this text is the constructive mathematical proof route; finite algebra source modules are written, but the native analytic transports and true original zeta/xi source identifications have not yet been kernel accepted.
