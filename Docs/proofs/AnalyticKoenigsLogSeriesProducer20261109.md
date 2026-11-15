# Original Koenigs P1: one local logarithmic power series pays both bounds

**2026-11-09 highest-alpha analytic producer.** This is an explicit classical-complex proof, with exact rational majorants, intended for translation to the independently selected Bishop-complex API. It does not by itself establish a kernel-checked Bishop principal Log or global Kneser tetration.

## Original goal

For the actual exponential's upper nonreal fixed point \(p\), construct a nonconstant local Schröder coordinate for \(\exp\), extend to a coherent Abel chart, and ultimately identify the globally normalized Kneser tetration and its modular-\(j\) observable. The theta/E8 shell and triadic 240/243 comparisons are **parallel auxiliary checks**, not a replacement for this goal.

## Hypotheses that must be paid by the actual source

- \(p\) is the selected upper-branch fixed point of the standard complex exponential, with \(\operatorname{Log}(p)=p\) for the principal branch.
- \(137/100<|p|<69/50\), and \(D(p,1/10)\) avoids the principal-log branch cut and zero.
- The original Bishop complex admits the uniformly absolutely convergent local series \(\log(1+w)=\sum_{k\ge1}(-1)^{k+1}w^k/k\), for \(|w|<1\), and the branch identity \(\operatorname{Log}(p+t)-\operatorname{Log}(p)=\log(1+t/p)\) on this disk.

The first and third hypotheses are **not** furnished by rational arithmetic alone. The existing rational-centre script establishes inequalities using standard log/atan series identities, but those identities still need the original Bishop/Agda interpretation.

## Theorem: the contraction bound from the same power series

For \(|t|\le1/10\), put \(w=t/p\), \(a=137/100\) and \(r=1/10\). Then \(|w|\le r/a=10/137<1\). Absolute convergence and \(\frac1k\le1\) imply
\[
|\operatorname{Log}(p+t)-p|
\le\sum_{k=1}^\infty |w|^k
=\frac{|w|}{1-|w|}
=\frac{|t|}{|p|-|t|}
\le\frac{|t|}{a-r}
=\frac{100}{127}|t|
<\frac45|t|.
\]
All inequalities are uniform in the disk. Hence \(g=\operatorname{Log}\) contracts the closed radius-\(1/10\) disk about \(p\) into itself. This does **not** require an integral/mean-value derivative bound.

## Theorem: the quadratic remainder from the same power series

Separate the \(k=1\) term and use \(1/k\le1/2\) for \(k\ge2\):
\[
|\operatorname{Log}(p+t)-p-t/p|
\le \sum_{k=2}^\infty\frac{|w|^k}{k}
\le\frac{|w|^2}{2(1-|w|)}
=\frac{|t|^2}{2|p|(|p|-|t|)}
\le\frac{5000}{17399}|t|^2
<\frac{311}{1000}|t|^2.
\]
The exact rational comparisons are \(500<508\) for \(100/127<4/5\), and \(5\,000\,000<5\,411\,089=311\cdot17399\) for the remainder constant. This is strictly stronger than the earlier \(M=311/1000\) estimate.

## Koenigs increments and uniform convergence

Define \(g^0(z)=z\), \(g^{n+1}(z)=g(g^n(z))\), and \(h_n(z)=p^n(g^n(z)-p)\). Since \(|g^n(z)-p|\le q^n|z-p|\) with \(q=4/5\), and \(g'(p)=1/p\) is the series linear term,
\[
h_{n+1}-h_n
=p^{n+1}\Big(g(g^n(z))-p-\frac{g^n(z)-p}{p}\Big).
\]
Consequently
\[
|h_{n+1}-h_n|
\le \frac{69}{50}\frac{5000}{17399}
     \left(\frac{552}{625}\right)^n |z-p|^2.
\]
Here \(\beta=(69/50)(4/5)^2=552/625<1\). The uniform Cauchy modulus is
\[
|h_m(z)-h_N(z)|
\le \frac{69}{50}\frac{5000}{17399}
     \frac{\beta^N}{1-\beta}|z-p|^2
=\frac{4312500}{1270127}\beta^N|z-p|^2.
\]
The reduced constant follows from exact rational arithmetic: \((69/50)(5000/17399)/(1-552/625)=4312500/1270127\).

Therefore \(h_n\) converges uniformly on the closed disk and defines \(\chi\), under the standard completeness and uniform-holomorphic-limit theorem. From \(h_n(gz)=h_{n+1}(z)/p\), the limit satisfies \(\chi(gz)=\chi(z)/p\). Since the coefficient of \(t\) in each \(h_n(p+t)\) is 1, the limit has \(\chi'(p)=1\) by uniform holomorphic convergence. A local inverse function theorem supplies a smaller injectivity disk. For \(z\) and \(\exp(z)\) in that disk, \(\chi(\exp z)=p\chi(z)\). **This is local Schröder linearization, not global Kneser normalization.**

## Source lemma contracts, in order

1. \`originalBishopLogOnePlusPowerSeriesOnDisk\`: the original same-object power series, with a uniform tail and branch identity \(\operatorname{Log}(p+t)=p+\log(1+t/p)\).
2. \`originalBishopLogOnePlusSeriesGeometricBound\`: norm bound by \(|t|/(|p|-|t|)\), directly from positive majorants.
3. \`originalBishopLogOnePlusSeriesQuadraticBound\`: norm bound by \(|t|^2/[2|p|(|p|-|t|)]\).
4. \`originalBishopLogInverseDiskIteration\`: actual original \(\operatorname{Log}\) self-map on \(D(p,1/10)\) with common factor \(q=4/5\).
5. \`originalBishopKoenigsIncrementMagnitude\`: use \(M=5000/17399\), \(\beta=552/625\) and actual iterates to discharge \`OriginalBishopGeometricComponentBounds\` in \`AbelBishopKoenigsGeometricAbsoluteExact\`.
6. \`originalBishopKoenigsUniformCauchy\`: use the *already-present* absolute summability, finite telescoping, and original trajectory-limit consumers. Do not duplicate this machinery.
7. \`originalSchroederHolomorphicLocalLinearization\`: same-source holomorphic limit, nonzero derivative, local inverse and conjugacy.

**Later unresolved gates:** selected punctured-sector integer winding; conjugate fixed-point chart gluing; Kneser fundamental-region continuation, reality/normalization and uniqueness; Bishop Machin trigonometric period and true \(q(\tau+1)=q(\tau)\); original \(E_4/E_6/\Delta/j\) same-object and analytic observer; certified Kouznetsov contours.

## Acceptance constraints

- This file proves the inequalities at the level of ordinary complex analysis conditional on the original principal-log series identity and fixed-point construction.
- No fresh Agda 2.9 \`--safe\` receipt has been obtained.
- No assumptions are to be silently substituted with a record of requested fields and called an original source instance.
- All contributions must retain original author attribution for the classical Kneser, Koenigs and Kouznetsov results.