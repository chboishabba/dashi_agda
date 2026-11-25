# Paper 9 — reciprocal Möbius disk period cut (25 Nov 2026)

Source boundary: Agda #1546 at 8982ab6bbda458586370b2165b603f863b6af6f1,
Lean companion research/paper9-original-eisenstein-derivative-20261125 at
0e3271e3fbca831b8dae77acfd1bdd153589c178 (new Integration/Paper9MobiusDiskPeriod.lean).
Existing Agda SmithChartMobiusMatrixExact and JInvariantSmithChartMobiusMatrixBridgeExact
are structural donors only; no Smith/Gamma/modular-j identification. Actual owners:
Paper9EulerMobiusTransport.mobiusAt/mobiusDeriv, Paper9Hecke41ChartGeometry.evalMul,
chartEval, reverseChart, Paper9ActualCMPoint.tangentRatio, tangentPolynomial,
signedOrientation, Paper9OriginalCMChartWeld.centeredJTaylor, Paper9SeparatedCusp.actualSymmetry.
No CI or kernel acceptance claimed. All new Lean source uncompiled.

## A5d: eliminate the mixed cubic gate by reciprocal fixed-point geometry

Let t=cmPoint, d=2t+1, c=-1-t, h(z)=-41/(z+1), hInv(z)=-41/z-1.
The literal matrices are [0,-41;1,1] and [-1,-41;1,0] (product -41 I);
h is chart 1 followed by S, hInv chart 0 followed by S and T^-1.
Both t and c solve t²+t+41=0. Reuse existing jInvariant and actual charts
to attach the reverse branch, not a new correspondence. Set
w=(z-t)/(z-c), z=t+d*w/(1-w).
Then w(h(z))=alpha*w(z), w(hInv(z))=alpha^-1*w(z),
alpha=tangent t; alpha+alpha^-1=-81/41. All denominators are nonzero
locally on the original upper half-plane, with d nonzero.
The sign is the original signed orientation, not a square root chosen later.

Let J(w)=jExt(t+d*w/(1-w)). Existing centeredJTaylor gives
J(w)=K+A*w+B*w²+O(w³), A=a*d, B=a*d+b*d²/2.
Actual two-point product in these disk coordinates has the two factors
J(v)-J(alpha*w) and J(v)-J(alpha^-1*w). Each is divisible analytically
by the corresponding linear difference. For example the first divided
difference extends via the actual scalar series:
sum_{n>=1} J_n sum_{k=0}^{n-1} v^(n-1-k)(alpha*w)^k.
Only its first-order expansion A+B*(v+alpha*w)+O((|v|+|w|)^2) is needed.
Multiply both divided differences by the actual remaining 40 chart factors.
No assumption that the remaining factors are individually nonzero is needed.
This constructs U, analytic locally, with
F(w,v)=Q(w,v)*U(w,v),
Q=(v-alpha*w)(v-alpha^-1*w)=w²+v²+(81/41)wv.
Q is symmetric. Actual symmetry gives U symmetric away from Q=0, then
everywhere locally by continuity. U(w,0)=U0+U1*w+O(w²);
U(w,w)=U0+2*U1*w+O(w²) by the symmetric first differential.
This is the only remaining analytic A5d weld: chart 0 S/T inverse binding,
actual divided differences and symmetric first-order residual, followed by
scalar Taylor comparison. It replaces the bivariate mixed cubic extraction.

Use the original shifted fixed slice S(X)=S2*X²+S3*X³+... and
diagonal P(X)=P2*X²+P3*X³+... . With X=J(w)-K:
S2*A²=U0, 2*S2*A*B+S3*A³=U1,
P2*A²=(163/41)*U0, 2*P2*A*B+P3*A³=(326/41)*U1.
Since A and S2 are nonzero, eliminate U0,U1:
41 P2=163 S2 and
(41 P3-326 S3)/(163 S2)=2 B/A²=b/a²+2/(d*a).
This is exactly the scalar required by Paper9SignedCMPeriod.actualCMWeightedPeriod
and actualLiteralPrefixPeriod. No mixed derivative, inverse j or dense
bivariate coefficient table. Lean diskPeriodAlgebra and diskJetCorrection
are source-written scalar consumers, not proofs that the four equations
are already inhabited. Retain old tauJetToSigned as independent control.

## Executed exact arithmetic

Local SymPy: 11/11 exact symbolic identities (forward/reverse disk
linearization reduced modulo t²+t+41; reciprocal/trace; inverse coordinate;
matrix inverse; disk j jet; Q symmetry/diagonal; period elimination; correction).
Original committed signed coefficient packet blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4
read from #1546; exact JS BigInt independent binomial shift of 83 diagonal and
43 slice coefficients: P0=P1=S0=S1=0, S2 nonzero, 41P2=163S2,
cross-multiplied ratio = -77859659565707/19943834790540897829879824384000,
and original integer dominance all PASS. Not Lean execution.

A4 independent local Python exact-integer/Fraction replay of original
scripts/check_cm163_dyadic_j_integer_certificate.py algorithm at 128/160/256
bits: all PASS. Original 128-bit offsets reproduced exactly:
lower -121397398953732472506062368501224644,
upper 12147930101178244703017603450764613085, scale 2^128.
This was a separate implementation of read-back source, not byte-identical
source execution. No new numerical approximation or CM integrality premise.
The remaining formal A4 chain is original Machin/sqrt -> positive exp
prefix 180 terms + ratio-half tail -> signed q=-exp(-pi sqrt163) ->
literal 3-term E4/E6 + ratio-half majorants -> strictly negative
discriminant -> outward-rounded quotient -> rootOfChecks. Existing
Bishop exponential and Eisenstein majorant owners are to be consumed.
A rational interval checker alone is not analytic reflection.

## Maximum cut
A3c: execute original finite residual checks, including literal shift
zeros/ratio/dominance, kernel reflection.
A4: source-bound exp/Fourier interval attachment; numerical replay passed.
A5a/b: previously source-written universal slice and cusp symmetry;
kernel pending. A5c/d: reciprocal chart-0 binding, scalar divided-difference
first differential, four scalar coefficient equations. A7: existing
period consumer, now with direct disk algebra; native same-real F1/F5
and all kernel verification remain distinct. Do not claim endpoint solved.
Original attribution: classical fractional-linear fixed-point geometry,
Klein, Machin, Chudnovsky, original DASHI and pinned Mathlib owners;
new work is the selected reciprocal factor/period weld.
