# Paper 9 — CM163 literal source replay and direct signed Taylor elimination

Parent bb37835a8d73350ca78acb539939ece1adbea736. Source-writing and mathematical derivation only. No arithmetic checker, compiler, CI, kernel or benchmark executed in this cut. Historical receipts retained without promotion.

## A4. Real-slice root isolation, original analytic producer

Actual owners read: scripts/check_cm163_dyadic_j_integer_certificate.py blob 8581a684cfb6ba6bfbfa45adbf6bfe01e9617258, JInvariantCM163DyadicHalfIntegerExact.agda blob 380e0cea0b2921317ca84d16f8170106f560df8c, JInvariantBishopNativeProofRelevantKleinExact.agda blob 6fe718a4754fb06c8b34cbae279b13fda6f5f66e. Existing normalized real negative q=-exp(-pi sqrt163) supplies real E4/E6, and literal negative Delta yields the existing proof-relevant reciprocal. No new complex/real carrier. Realness of j follows from real coefficient limits and real reciprocal, provided these are bound to the original analytic source. The existing dyadic interval source uses exact rational Machin alternating brackets (90,30), integer floor sqrt163, 180 positive exponential terms and outward-rounded interval E4/E6 with first three coefficients and explicit tail. Native half-unit module checks only the final two offset inequalities; it does NOT prove the producer's analytic enclosure. Do not promote it.

From earlier actual Hecke correspondence derivation and source reconstruction, P(j(tau))=0, P(X)=Phi41(X,X). Let K=-640320^3, x=j(tau)-K. Existing diagonal source historically checked P(K+x)=x^2 S(x), deg S=80; strict coefficient dominance 2^80|a0|>sum_i 2^(80-i)|ai| for ascending S coefficients. Since x is real and |x|<1/2 from the dyadic source, |S(x)-a0|<=sum_i |ai|/2^i<|a0|. Thus S(x) is apart from zero and x^2=0 implies x=0 (native donor BishopSquareZeroReflectsSetoidZeroExact). No general complex norm/square-root calculus required for this selected root. The complex disk dominance remains true, but unnecessary for this real selected proof. Native remaining: real slice embedding of the actual normalized j, interval arithmetic soundness for the literal dyadic source, integer coefficient reflection and polynomial evaluation/factorization on original Bishop real or sound classical reflection. General CM integrality is off critical path.

## A5. Direct original tau Taylor: no local inverse of j

Let a=j'(tau), b=j''(tau), alpha=h'(tau), gamma=h''(tau), h(t)=-41/(t+1). By Ramanujan Dj=-j E6/E4 and tiny-q positivity, a!=0 at the selected CM point. Use epsilon=t-tau, not an inverse j coordinate. Expand the actual branches
 x=j(t)-K=a epsilon+(b/2) epsilon^2+O(epsilon^3)
 y=j(h(t))-K=a alpha epsilon+(b alpha^2+a gamma)/2 epsilon^2+O(epsilon^3).
The original symmetric germ has quadratic coefficients c20,c11,c20 and cubic c30,c21,c21,c30, with c20=S2, c11=P2-2 S2, c30=S3, c21=P3/2-S3 where P,S now denote original diagonal and fixed slice Taylor coefficients. Constant/linear coefficients zero via existing exact certificate and symmetry. In degree 2, cancel a^2 to obtain c20(1+alpha^2)+c11 alpha=0. Since f(alpha)=41 alpha^2+81 alpha+41=0 and alpha!=0, 41c11=81c20 (equiv 41P2=163S2). In degree 3, subtract the vanishing quadratic coefficient times a*b. With g=(alpha^2-alpha)b+a gamma, the remaining exact equation is
 (c11+2 c20 alpha) g + 2 a^2 [c30(1+alpha^3)+c21 alpha(1+alpha)] = 0.
This follows from the expansions directly, cancelling a/2, not from an inverse germ.

Integer polynomial identities, source-written in JInvariantCM163SignedTangentPolynomialExact:
 (82x+81)^2+163=164 f(x)
 41(1+x^3)+122x(x+1)=(x+1) f(x)
 (82x+81)(x-1)+163(x+1)=2 f(x).
Also f(0)=41, f(1)=163, f(-1)=1, so no zero/one/minus-one tangent. Signed coordinate 82alpha+81 = +/- i sqrt163, distinct conjugate orientations; actual h'(tau) fixes the branch, not an arbitrary sign. Substitute f(alpha)=0 and 41 c11=81 c20 into degree 3, multiply by alpha-1 and cancel the nonzero alpha+1:
 163 c20 g = a^2 alpha(alpha-1) * 2(41c21-122c30).
Hence the direct denominator-cleared source theorem is
 163 S2 [(alpha^2-alpha)b+a gamma]
   = a^2 (alpha^2-alpha) (41 P3-326 S3).
This is the exact weld on actual j derivatives, not a generic Taylor interface. Divide only by explicitly apart a^2, alpha(alpha-1), 163 S2:
 kappa=(41P3-326 S3)/(163 S2)
      =P3/P2-2 S3/S2
      =b/a^2 + gamma/((alpha^2-alpha)a).
BIDI reopening: g=a^2(alpha^2-alpha)kappa, and beta=g/(2a^2) in the old x-coordinate if desired; retain alpha, a, gamma to reopen b and the original signed branch. The scalar kappa alone is not the branch. From tau^2+tau+41=0, gamma/(alpha^2-alpha)=2/(2tau+1). Thus
 kappa=b/a^2+2/((2tau+1)a).
Using D=(2pi i)^-1 d/dtau and Dj=-j E6/E4, D log(Dj)=E2/6-2 E6/(3E4)-E4^2/(2E6), interpreted as quotient D(Dj)/(Dj), no global logarithm. At 2tau+1=2i Im tau, this gives s2=4+3K/(K-1728)-6K kappa. Existing historical exact result kappa=-77859659565707/19943834790540897829879824384000, s2=77265280/90856689. These values are not inputs to reconstruction. Native remaining: interpret integer polynomial equalities in the actual complex field, bind actual first and second derivatives and Taylor remainders, cancel nonzero factors, reflect exact coefficients. This removes local inverse j and quadratic field inversion from the analytic critical path, but does not prove the actual Taylor source or Ramanujan identities natively.

## Finite source replay

New scripts/check_cm163_source_bound_jet.py (UNEXECUTED) reuses the original pinned source owners, checks their Git blob hashes, accepts the signed-hex descending coefficient pair from existing check_cm163_backend_parity.py or constructs it with the original scalar generators. It checks both polynomial Laurent identities by direct forward substitution q^d poly(j(q)), independently of the producer's descending polynomial extraction. It uses original j_unit, unit log-derivative/norm recurrences and a coefficient-oriented convolution; NOT independent j-series production or independent analytic proof. Integer Horner shifting supplies actual factorization, coefficient dominance and signed Taylor data. The original dyadic 128-bit producer is called and both exact offsets compared with the existing Agda constants. Derive kappa through integer two-slice numerator/denominator, not field inversion, check its equivalent expression and derive correction/terminal ratio. Optional JSON receipt contains full shifted coefficients, signed dominance and scalar witnesses; not a formal import. Historical parity/benchmarks remain separate. No fresh result claimed. Native proof of the finite coefficient replay and source binding still necessary; a hash is provenance, not semantics.

## Critical path after this cut

A3/A4 original j normalized modular semantics plus actual Laurent/dyadic coefficient reflection; A5 direct original tau Taylor and chain rule (no inverse); A2 Ramanujan packaging via pinned rigidity; A6 original q triangular coefficient/convergent composition; A7 positive terminal normalization and F1 literal factorial sum; A1 original Machin period, F5 actual universal rational cross. F3 full intended literalWidthBound source exists but uncompiled; F2/F4 and transitive source remain unverified. F6-F9 exact kernel, original native computational parity, decimal apartness and performance unchanged. No additional downstream Bishop adapter. Classical CM, Hecke, Ramanujan, Chudnovsky, Machin and Bishop/Bridges, Murray/Csimma retain attribution; existing DASHI two-slice and dyadic owners retained. New work here is direct tau-coordinate elimination, real-slice proof reduction and forward coefficient replay.
