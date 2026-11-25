# Paper 9 — scalar reciprocal residual and normalized cusp window (25 Nov 2026)

Start #1546 4c4f847d688cb215dd3609c2979941577de43508, Lean companion
research/paper9-original-eisenstein-derivative-20261125.
New Lean source 1e47c955558efcb0555139cd381b41006c27e967,
32057f677a9185175cbf32b172131ce263b54cc0 (Paper9ScalarReciprocal),
4e0df23da0f7718d29ed673f11cd74ec581f7508 (Paper9CMNormalizedCuspWindow).
No CI. Lean/Lake/Agda unavailable in local container; all new source uncompiled.

## A5: eliminate bivariate analytic division as well as mixed cubic extraction

Reuse actual chart 0 with determinant-one T^-1 S=[-1,-1;1,0],
chart 1 with S, Paper9Hecke41ChartGeometry, Paper9ActualCMPoint,
Paper9SeparatedCusp.actualSymmetry, centeredJTaylor and actualSlice.
The new reverseChartAt/reverseChartValue and forwardChartValue are
source-written bindings; productSplit preserves the remaining 40
indices and all multiplicity. No Smith observer identification.

In the previous disk coordinate let x(w)=J(w)-K=w X(w), X(0)=A, X'(0)=B,
x_+=x(alpha*w), x_-=x(alpha^-1*w). Define actual remaining polynomial
R_w(Y)=prod_{i other than 0,1}(K+Y-chartValue(i,undisk(w))).
Then F(w,v)=(x(v)-x_+)(x(v)-x_-)*R_w(x(v)).
By existing symmetry and actual fixed slice S, S(Y)=Y^2 R_0(Y)
as polynomials (equality on infinite j-image or locally nonconstant j).
Thus R_0(0)=S2 and R_0'(0)=S3; neither requires nonvanishing
of each remaining factor. Exact finite telescoping:
R_w(Y)-R_w(0)=Y T_w(Y); T_0(0)=S3.
Use list recursion diffAt with prodAt (productDifference);
no division by a possibly zero Y, and no distinct root assumption.

The normalized products N=(x_+ x_-)/w^2 and
M=(x-x_+)(x-x_-)/w^2 extend via original scalar Taylor.
N0=A², N1=-(81/41)AB,
M0=(163/41)A², M1=(163/1681)AB.
For shifted complements s(Y)=S(Y)/Y² and p(Y)=P(Y)/Y²
(exact polynomial factor, not numerical division), the two germs are:
s(x(w))*X(w)^2=N(w)*R_w(0),
p(x(w))*X(w)^2=M(w)*(R_w(0)+w X(w) T_w(x(w))).
Only ordinary scalar product/chain rules are needed. In the derivative
of w*X*T, the derivative of T is multiplied by zero. Let r0=R_0(0),
r1=(d/dw)R_w(0)|0. The four equations are:
S2 A²=A² r0; P2 A²=(163/41) A² r0;
S3 A³+2 S2 AB=-(81/41)AB r0+A² r1;
P3 A³+2 P2 AB=(163/1681)AB r0+(163/41)A²(r1+A S3).
Eliminate r0,r1: 41 P2=163 S2;
2 B/A²=(41 P3-326 S3)/(163 S2).
Use existing diskJetCorrection and actualLiteralPrefixPeriod.
New scalarPeriodAlgebra, scalarGermPeriod and periodFromScalar
are source-written. Remaining A5: actual disk germ (including forward/
reverse disk equations and local upper half-plane), actual remaining
polynomial/finite difference attachment, literal shifted complement
coefficients, and instantiation of scalarGermPeriod. Existing analytic
symmetry proof still uncompiled. No bivariate analytic division or
mixed cubic extraction left as mathematical requirements.

## A4: stable original cusp normalization instead of tiny quotient

r=|q|<=2^-36, q nonzero. Existing divisor sum majorants with k=3,5
and ratio <=1/2 give two-prefix Fourier errors
|E4-(1+240q+2160q²)|<=38880 r³,
|E6-(1-504q-16632q²)|<=734832 r³.
Let u=E4-1, v=E6-1. Exact rational bounds give
|u|<=241r, |u-240q|<=2161r²,
|v|<=505r, |v+504q|<=16633r².
Expand cube/square:
E4³=1+720q+179280q²+eN, |eN|<=17232484 r³<20M r³;
E6²=1-1008q+220752q²+eY, |eY|<=18252361 r³<20M r³.
Here cube error =3*38880+3*2161*481+241³,
square error=2*734832+16633*1009.
Original Delta unit D=(E4³-E6²)/(1728q)
=1-24q+eD, |eD|<=24000r², |D|>=1/2.
Original J=q*j=E4³/D. Subtract (1+744q):
|E4³-(1+744q)D| <=
(197136+20M*r+48000)r², using |1+744q|<=2.
Thus |j-1/q-744|<=500000r<1/4. No tiny discriminant division,
no new j, no integrality/class-number theorem.
At cmTau, q=-exp(-pi sqrt163) by existing cmQPhase.
Reuse original 128-bit pi/sqrt endpoints pL,pH,sL,sH over D=2^128.
xL=pL*sL/D², xH=pH*sH/D². Positive 180-term prefix E(x);
upper E(xH)+2*xH^180/180!. Exact rational comparison passes
640320³+744-1/4 < E(xL) <= E(xH)+2*xH^180/180! <
640320³+744+1/4, and 2*xH<181.
New expWindowOK, halfUnitFromCusp, actualHalfUnit, rootFromCuspChecks
source-written, with exp and actual Fourier norm premises explicit.
The actual exponential prefix tail and Fourier coefficient majorant
attachment to pinned source remain uncompiled/unpaid; proof of bounds
above is mathematical, not a Lean kernel result.

## Actual executed receipts, this turn

Local SymPy 1.14: 11 exact identities PASS (forward/reverse disk,
inverse coordinate, matrix inverse, reciprocal trace, N0/N1/M0/M1,
zero and first normalized residual coefficients), plus a separate
symbolic replay of the exact scalarPeriodAlgebra linear combination.
164 finite integer product-difference cases PASS (degrees 0..40,
four seeded cases each including zeros/repeated values).
Local Python Fraction: all displayed Fourier constants and small-r
inequalities, and 180-term exponential window, PASS.
Approximate displays only: exp endpoint minus center
-7.499274099153538e-13 and -7.499273976413151e-13;
500000*2^-36=7.275957614183426e-6.
Original committed signed packet read-back blob
17ed967d83d1aacafdb0f19d7bd81e6afc5887a4, JS BigInt shift replay
83+43 coefficients, four zeros, S2 nonzero, quadratic relation,
kappa and dominance all PASS. No full A3c residual recomputation
this turn. These are independent exact arithmetic tests, not
kernel checks, not execution of Lean declarations.

## Remaining cut

A3c literal native residual execution, shifted S/P coefficient binding;
A4 original exp/Fourier tail semantic attachment to above window;
A5 existing cusp symmetry, reciprocal scalar germ attachment and
actual four scalar equations; A7 existing period consumer with
its two inputs. F1/F5 native original Bishop same-real and exact-source
acceptance unchanged. Do not promote kernel, record, or performance claims.
Original attribution: classical fractional-linear fixed-point geometry,
Klein, Machin, Chudnovsky, existing DASHI and pinned Mathlib sources.
New work is the selected scalar finite-product/normalized-cusp weld.
