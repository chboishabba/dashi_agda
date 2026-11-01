# Riemann reflection-orbit defect — 2026 frontier

## Primary source

Levent Alpöge and Ralph Furman, **“More than two thirds of the zeta zeros are simple and on the critical line”**, arXiv:2608.13637 (2026). DOI: `10.48550/arXiv.2608.13637`.

Machine-checked companion consulted for the exact zero-side block decomposition and test-family formulas: Anthropic, `zeta-23-lean` (2026, Apache-2.0), especially `Zeta23/Defs.lean`, `Zeta23/Poisson.lean`, `Zeta23/Hypotheses/GzGp.lean`, `Zeta23/ZeroSide.lean`, and `Zeta23/ZeroSide/RankTraceMult.lean`.

This tranche is source-calibrated to the 2026 rank/trace + Sylvester-inertia argument. It does not claim RH.

## 1. Reflection quotient

Write

\[
\rho=\frac12+\alpha+i\gamma,
\qquad
1-\bar\rho=\frac12-\alpha+i\gamma.
\]

Thus the transverse coordinate carries the involution

\[
\alpha\leftrightarrow-\alpha.
\]

`RiemannReflectionOrbitDefectExact.agda` constructs a finite theorem-bearing model with one critical fixed centre and left/right inverse-oriented states. Its quotient forgets orientation while retaining magnitude and squared defect. It proves reflection involutivity, uniqueness of the fixed centre, reflection invariance of the defect, zero defect only at the centre, and exact finite left/right pair-count identities.

## 2. What bare inertia sees — and what it loses

For one representative of an off-line pair, the verified source writes the evaluation vector

\[
u=x+iy.
\]

The pair contributes

\[
m\bigl(uu^T+\bar u\,\bar u^T\bigr)
 =2m\bigl(xx^T-yy^T\bigr).
\]

Hence each off-line pair is a pullback of a hyperbolic source form with one positive and one negative channel. The companion proof obtains

```text
n_+(Q) <= p
```

for `p` unordered off-line pairs.

`RiemannWeilOffLineHyperbolicBlockExact.agda` formalizes this signature ledger and proves a no-factor theorem: the fixed/pair signature does not determine squared displacement. Two inverse-pair states may share the same signature code while carrying defects `1` and `9`. Therefore the present inertia count controls how many positive directions unresolved pairs can cost, but not how far those pairs lie from the critical line.

## 3. First source-facing displacement-sensitive producer: complex Poisson energy

The companion definitions make the missing variable unusually explicit:

\[
\gamma_\rho
 =\frac{\rho-1/2}{i}
 =\gamma-i\alpha,
\qquad
v_\rho(k)=\widehat\phi(\gamma_\rho-\tau_k).
\]

Its Poisson module proves, for real arguments,

\[
\sum_{k\in\mathbb Z}
\widehat\phi(\tau-\tau_k)
\widehat\phi(\tau'-\tau_k)
=L\Phi(\tau-\tau'),
\]

and explicitly notes that the complex continuation mentioned in the paper is not needed by the published proof.

If this identity is continued to the required complex arguments, two very different diagonal observables appear.

### 3.1 Holomorphic/bilinear square: baseline-blind to displacement

Taking the same complex argument twice gives schematically

\[
\sum_k v_\rho(k)^2=L\Phi(0)=aL^2.
\]

This is the analytic/bilinear quantity naturally aligned with the usual Weil matrix. It is constant along the transverse displacement in the ideal full-grid identity.

### 3.2 Hermitian square: quantitatively displacement-sensitive

Pairing the argument with its conjugate instead gives

\[
\sum_k|v_\rho(k)|^2
=L\Phi(\gamma_\rho-\bar\gamma_\rho)
=L\Phi(-2i\alpha).
\]

Because `phi` is real and even,

\[
\Phi(-2i\alpha)
 =\int \phi(u)^2 e^{2\alpha u}\,du
 =\int \phi(u)^2\cosh(2\alpha u)\,du.
\]

Therefore

\[
\sum_k|v_\rho(k)|^2-aL^2
 =L\int \phi(u)^2\bigl(\cosh(2\alpha u)-1\bigr)\,du
\ge
2L\alpha^2\int u^2\phi(u)^2\,du,
\]

using `cosh x - 1 >= x^2/2`.

This is exactly the shape sought in the previous frontier:

\[
\boxed{
D(\rho)\ge c_\phi L\,|\beta-1/2|^2,
\qquad
D(\rho)=D(1-\bar\rho).
}
\]

The remaining work is to prove the complex continuation and transport enough of this Hermitian information through the finite compression and arithmetic side.

## 4. Exact local block consequence

`RiemannComplexPoissonPairEnergyExact.agda` closes the local algebra without pretending the analytic promotion is already proved.

Write

\[
A=\|x\|^2,
\qquad B=\|y\|^2,
\qquad C=\sum_kv_k^2.
\]

If the complex-square identity fixes `C` as a real baseline, then `x·y=0` and

\[
A-B=C,
\qquad A=C+B.
\]

For the paired block

\[
Q_\rho=2m(xx^T-yy^T),
\]

orthogonality gives

\[
\|Q_\rho\|_F^2
 =4m^2(A^2+B^2).
\]

The critical-line baseline is `B=0`, hence

\[
\|Q_{\rho,\mathrm{crit}}\|_F^2=4m^2C^2,
\]

and the exact excess is

\[
\boxed{
\|Q_\rho\|_F^2-4m^2C^2
 =8m^2BA.
}
\]

The Agda module proves this as a polynomial identity and includes separating checks: with the same multiplicity and same holomorphic baseline, two pair ledgers have Hermitian energies `3` versus `7`, Frobenius squares `20` versus `100`, and excesses `16` versus `96`.

It also proves a second no-factor theorem:

```text
holomorphic baseline -> Hermitian energy
```

cannot exist as a universal decoder. The bilinear/holomorphic observer has genuinely quotiented out information that the Hermitian observer retains.

So the new bottleneck is sharper than “find a defect”:

\[
\boxed{
\text{transport the Hermitian residual to an arithmetic-controlled observable.}
}
\]

## 5. Why the existing rank–trace inequality is nearby but not yet enough

The companion `ZeroSide/RankTraceMult.lean` proves the multiplicity-aware inequality

\[
\|P+Q\|_F^2
\ge
c\,\mathrm{tr}P
+\sum_jg_c(m_jx_j)
+2c\,\mathrm{tr}Q
-c^2b,
\]

with

\[
g_c(x)=x^2-cx-((x-c)_+)^2.
\]

This is promising because it already consumes rank-one norm data and Frobenius information. But in the published decomposition the off-line pairs sit in the indefinite `Q`, and only their positive-index budget survives into the final estimate. The displacement-sensitive Hermitian norm is not presently exposed as a separate controlled term.

A successful refinement must therefore do at least one of:

1. refine the decomposition so an off-line Hermitian residual survives the scalar/rank–trace step;
2. derive an independent prime-side bound for a sesquilinear/Hermitian companion form;
3. prove an almost-orthogonality inequality that converts the sum of local pair-energy excesses into a controlled part of the global Frobenius norm.

The existing pair-ceiling and weighted-end machinery controls bandwidth-one pair-correlation laws and `psi`-weighted tail/endpoint errors, but it does not by itself identify the transverse Hermitian defect above. Its value for this lane is likely in the finite-grid/interference estimates, not as an automatic RH promotion.

## 6. Ramanujan/Hecke cross-pollination at the correct level

The repository's `RamanujanTauHecke23Exact.agda` provides exact local compatibility examples such as

\[
\tau(9)=\tau(3)^2-3^{11},
\qquad
\tau(27)=\tau(3)^3-2\,3^{11}\tau(3).
\]

The relevant lesson is architectural: local spectral data can be forced into a globally rigid compatible family. It does **not** supply a zeta-zero location theorem by analogy.

For this zeta lane the corresponding bridge must be an actual intertwiner:

\[
\text{Hermitian zero defect}
\longleftrightarrow
\text{explicit-formula / prime observable},
\]

followed by an arithmetic rigidity/coercivity estimate. DASHI already has the terminal composition in `RiemannArithmeticCoercivity.agda` and `RiemannMillenniumAssembly.agda`: once an exact positive arithmetic decomposition is available, explicit-formula transport plus the Weil criterion yields RH. The new work should feed that existing terminal route rather than create a parallel prize claim.

## 7. Current exact frontier

The highest-alpha proof programme is now:

\[
\boxed{
\begin{array}{c}
\text{complex Gabor/Poisson continuation}\\
\Downarrow\\
D_{\mathrm{full}}(\rho)
 =L\int\phi^2(\cosh(2\alpha u)-1)\\
\ge 2L\alpha^2\int u^2\phi^2\\
\Downarrow\\
\text{finite-grid retention + pair/interference control}\\
\Downarrow\\
\text{Hermitian-to-arithmetic transport}\\
\Downarrow\\
\text{positive arithmetic decomposition / vanishing defect}\\
\Downarrow\\
\alpha=0\ \text{for every zero.}
\end{array}}
}
\]

The first genuinely displacement-sensitive candidate has therefore been identified. The open mathematical burden is no longer the orbit algebra or bare inertia; it is the three analytic arrows after the full-grid identity.

Current fail-closed status remains:

```text
complex Poisson continuation = not yet proved here
finite-grid retention = not yet proved here
cross-pair interference = not yet controlled here
Hermitian/arithmetic transport = not yet constructed here
weighted transverse moment theorem = false
RH proved here = false
```
