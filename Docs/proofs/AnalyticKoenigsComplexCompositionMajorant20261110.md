# P1 highest-alpha proof: positive formal majorant for the composed exp–log series

**Date:** 2026-11-10. **Scope:** exact all-degree algebra and constructive absolute-summability bounds for the nested composition. **Not** yet an Agda-kernel-checked theorem or an identification of Bishop Cartesian complex exponential with its complex power series.

## Target and source objects

Our original objective remains the selected upper exponential fixed point, locally nonconstant Koenigs/Abel germ, globally normalized Kneser tetration and same-source Bishop modular \(j\). The E8 240/243 comparison does not pay these analytic obligations.

The preceding exact Bishop-complex modules define the literal
\[
L(X)=\sum_{k\ge1}\ell_kX^k,\qquad \ell_k=(-1)^{k+1}/k.
\]
Write the *formal* exponential \(E(X)=\exp(L(X))=\sum e_nX^n\) in \(\mathbb Q[[X]]\). Independently, define its coefficientwise positive majorant
\[
H(X)=\sum_{k\ge1}h_kX^k,\quad h_k=1/k,\qquad
B(X)=\exp(H(X))=\sum b_nX^n.
\]

## Theorem 1 — exact coefficients in every degree

The formal exponential differentiation and Cauchy-product identity give, with \(e_0=b_0=1\),
\[
n e_n=\sum_{k=1}^n(-1)^{k+1}e_{n-k},\qquad
n b_n=\sum_{k=1}^n b_{n-k}\quad(n\ge1).
\]
For \(n=1\), \(e_1=1\). For \(n\ge2\), induction assuming \(e_j=0\) for \(2\le j<n\) leaves exactly \(k=n-1\) and \(k=n\), whose contributions \((-1)^n\) and \((-1)^{n+1}\) cancel. Thus \(e_n=0\) for every \(n\ge2\).

For the positive coefficients, if \(b_j=1\) for \(j<n\), then \(n b_n=\sum_{k=1}^n1=n\), hence \(b_n=1\) for **every** \(n\).

Therefore, simultaneously for all \(n\),
\[
\boxed{e_0=e_1=1,\quad e_n=0\ (n\ge2),\quad b_n=1\ (n\ge0).}
\]

## Theorem 2 — actual composition coefficient majorization

Each \(e_n\) is a finite sum, because \(L(0)=0\):
\[
e_n=\sum_{m=0}^n\frac1{m!}
 \sum_{\substack{k_1,\dots,k_m\ge1\\\sum k_i=n}}
 \prod_{i=1}^m\frac{(-1)^{k_i+1}}{k_i}.
\]
The corresponding \(b_n\) replaces the signs by \(+1\). The rational triangle inequality gives \(|e_n|\le b_n=1\) term by term. This proof is **independent** of the signed cancellation calculation; it provides an explicit nonnegative comparison for all finite Cauchy compositions.

For any ordinary complex \(w\) satisfying \(|w|\le r<1\), all absolute values of the terms arising from expanding the nested series are dominated in total by
\[
\sum_{n\ge0} b_n r^n=\sum_{n\ge0}r^n=\frac1{1-r}.
\]
For every cutoff \(N\), the tail of all contributions with total degree \(n>N\) obeys
\[
\boxed{\sum_{n>N} b_n r^n=\frac{r^{N+1}}{1-r}.}
\]
This is a uniform, explicit, constructive geometric majorant on every compact subdisk, without invoking a real-valued logarithm to bound the nested exponential.

**Consequence in standard complete complex analysis.** Absolute convergence of the double/finite-composition expansion permits summation by total degree. The coefficient equality above then implies \(\exp(L(w))=1+w\), uniformly on \(|w|\le r<1\). This proves the target analytic identity classically without requiring a principal-log branch as an input.

**Agda acceptance warning:** to apply the same proof to the repository's original Bishop complex, one must still show that (i) the native \`BishopSetoidComplexExact.expC\`, defined by the *real* exp/sin/cos series, agrees with the complex factorial exponential series, and (ii) the existing Bishop finite Cauchy rearrangement/completion theorems can sum the composition under the geometric majorant. Neither is supplied as a new authority here. The proof above identifies the precise consumer chain.

## Next source-native lemma boundaries

1. \`originalBishopComplexFactorialExpSeriesConvergent\`: construct \(\sum_{m\ge0}z^m/m!\) on the selected Bishop complex for all \(z\).
2. \`originalBishopCartesianExpEqualsFactorialSeries\`: same-carrier identification with the existing source-defined \`expC T\` from Bishop real exp/sin/cos. This must use actual sine/cosine term identification and finite parity/Cauchy-product lemmas.
3. \`originalBishopFormalExpLogCompositionCoefficients\`: all-degree finite rational Cauchy-composition theorem, ideally shared with the existing Bishop finite Cauchy wing/triangle machinery.
4. \`originalBishopExpLogCompositionPositiveMajorant\`: source-native \(|e_n|\le b_n=1\) and a uniformly vanishing geometric tail, with actual Bishop order and series convergence witnesses.
5. \`originalBishopLogOnePlusExpInverseOnUnitDisk\`: resulting \(\exp_C(L(w))\approx_C1_C+w\) on the original certified disk.
6. \`originalBishopLocalInverseAtUpperFixedPoint\`: actual \(p\), \(p^{-1}\), \(\exp(p)=p\), and a disk/radius witness, then \(g(z)=p+L((z-p)/p)\), including local addition.
7. Original holomorphic Koenigs limit, Abel branch winding/cocycle, global Kneser normalization; and in parallel, true Bishop \(q\)-period and same-object \(\Delta/j\).



## Theorem 3 — finite-polynomial approximation certificate (stronger implementation cut)

For each \(N\ge1\) define the *finite* source polynomial
\[
L_N(w)=\sum_{k=1}^{N}\frac{(-1)^{k+1}}k w^k.
\]
Let \(F_N(w)=\exp(L_N(w))\) denote the ordinary complex exponential of this polynomial. In its Taylor expansion \(F_N(w)=\sum_{m\ge0}c_{N,m}w^m\), the coefficients through degree \(N\) are exactly the previously proved full-composition coefficients, since replacing \(L\) by \(L_N\) changes no input degree up to \(N\). Thus \(c_{N,0}=c_{N,1}=1\), and \(c_{N,m}=0\) for \(2\le m\le N\).

The **positive composition majorant** for \(F_N\) has coefficients bounded by \(b_m=1\), because every positive Cauchy composition using terms of degree \(\le N\) is a sub-sum of the full positive composition. Hence \(|c_{N,m}|\le1\) for every \(m\), including beyond the cutoff. Therefore, for any complex \(|w|\le r<1\),
\[
\boxed{\bigl|\exp(L_N(w))-(1+w)\bigr|
       \le\sum_{m>N}r^m
       =\frac{r^{N+1}}{1-r}.}
\]
This is a **uniform, explicit** error estimate obtained from exact finite rational coefficient cancellation and a positive geometric majorant; it does not require a Cauchy integral estimate or an analytic principal logarithm.

Separately, the log polynomial itself has the uniform tail estimate
\[
|L(w)-L_N(w)|
\le\sum_{k>N}\frac{r^k}{k}
\le\frac{r^{N+1}}{(N+1)(1-r)}.
\]
As \(N\to\infty\), \(L_N(w)\to L(w)\) uniformly and \(\exp(L_N(w))\to\exp(L(w))\) by continuity of the ordinary complex exponential, so the boxed estimate implies \(\exp(L(w))=1+w\) on \(|w|<1\).

**Preferred Bishop Agda proof cut:** source-construct \`L_N\` using finite Bishop sums and prove coefficient cancellation and the positive absolute majorant for its factorial exponential series. Use the existing Bishop real/complex convergence and continuity lemmas to pass to the canonical limit \`originalBishopLogOnePlusCanonicalLimitOnUnitDisk\`. This needs the same-carrier identification of \`BishopSetoidComplexExact.expC\` with its complex factorial series and uniform continuity/limit transport, but does **not** require prior principal-log existence. The finite estimate is valid for every \(N\), not merely the checked examples.

## Independent regression

Run \`python3 scripts/analytic_j_tetration_exp_log_composition_majorant.py\`. It constructs signed and positive **finite Cauchy compositions**, separately from the previous derivative-recurrence regression, in exact \`fractions.Fraction\` arithmetic. The checks pass at total degrees \(1,2,4,8,16,24\): all signed coefficients beyond degree 1 vanish; all positive comparison coefficients equal 1; every signed coefficient magnitude is bounded by its positive counterpart. Exact rational geometric tail identities are checked for \(r=1/10,1/2,3/4,9/10\). The script is a test, not a proof of the all-degree recurrence or a Bishop-kernel receipt.

**Status:** full all-degree **mathematical** coefficient/majorant proof completed here; original Bishop analytic transport and pinned Agda 2.9 \`--safe\` verification OPEN. Do not mark local Koenigs, Abel, global Kneser, Bishop \(j\) or Kouznetsov complete.
