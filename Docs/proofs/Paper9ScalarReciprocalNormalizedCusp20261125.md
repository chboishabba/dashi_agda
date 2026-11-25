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


## Monster / signed 240, -504 source reuse (25 Nov, continuation)

User explicitly recalls Monster coefficient geometry. Recovered on this same
branch: JInvariantEisensteinThreeB54CoefficientBridgeExact (blob
3ec26c200c3bad423c75dcf489f50d4263884742), coefficient tower
68b8f84ed7ba853b78322781931a276507c1525d, AbelE8RootE4FirstCoefficientExact
4b58516b08fe5fc58ac6e68e03edd5dff1237e37, Monster196884FibreInterferenceExact
6dd5b94be3403164f4efd750705a6f408725f02c, JInvariantThreeBTate66UltrametricExact
aa7c26a6ec11fba00717b09c5d11e86960169c67, original Bishop majorant
f5ccee66a45e2264f7174963071630bce2e9d50f.
See Paper9EisensteinThreeB54Derivative20261125.md for original attribution and
classical X0(3) premise. No new root enumeration or Monster module.

For signed first coefficients a=240,b=-504, the unimodular matrix
[[1,-1],[3,-2]] sends (a,b) to (744,1728). Reverse a=1728-2*744,
b=1728-3*744. The original signed E4/E6 second coefficients 2160,-16632
give numerator N=E4^3=1+720q+179280q^2+..., E6^2=1-1008q+220752q^2+...
and D=Delta/q=1-24q+... . Thus 744=720+24 from the actual normalized cusp
division, independently agrees with a-b. The 3B signed Tate residual 66-12=54
gives 1728=32*54 and oscillator coefficient 324=6*54. The original classical
level-three coordinate t=q^-1-12+54q+... gives
j=t+756+196830/t+19131876/t^2+387420489/t^3
=q^-1+744+196884q+...; 196884=196830+54=196560+324.
These are cross-chart coefficient checks; not representation isomorphisms.
The 66->6->6 indexed fibre address is not a valuation of the integer 66.
No new level-three analytic premise introduced into A4; prime 3 does not
replace the degree-41 CM self-isogeny.

Lean companion Integration/Paper9SignedEisensteinCuspTail.lean, commits
e351ecac4d713fbf89b3368f78c2a2980557ebda and
80940423a18d7fb1d406bbb3628b2276719f7558: source-written signed normalization
inverse, omitted-index inequality n+3<=3*2^n, termBound using existing
sigma_le_pow_succ, normTail using geometric sum, e4TwoTailAt/e6TwoTailAt
using original Paper9OriginalEisensteinCoeff.e4HasSum/e6HasSum and xAtQ/yAtQ,
and stable normalized cuspRemainder consumer. No compiler available.
The Fourier tail source attachment is now written (not elaborated), not
assumed as a new Monster premise. Remaining: elaborate those declarations;
propagate actual E4/E6 tails through cube/square and bind D=Delta/q to
original deltaUnitSourceOnDisk, then consume cuspRemainder and the original
halfUnit/rootOfChecks. Actual exponential semantic finite-prefix comparison,
scalar Hecke germ and kernel replay still needed.

Fresh local SymPy checks: signed low-order N and E6^2 coefficients, -24
normalized Delta coefficient, determinant-one matrix, eta ratio signed
prefix and rational level-three j expansion through q all PASS.
Fresh Python Fraction: all displayed remainder constants and inequalities
PASS (Cn=17232484, Cy=18252361, Cd=35484845/1728<24000;
conservative 500000*r<1/4 at r=2^-36); exact 180-term exponential window
PASS using the original 128-bit dyadics; endpoint offsets displayed
approximately -7.499274099153538e-13 and -7.499273976413151e-13.
No full packet replay, Agda/Lean kernel, CI or performance claim this turn.
