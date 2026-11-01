# Riemann Weil-pair Frobenius kernel — nonlinear transverse producer

## Calibration

Primary source: Levent Alpöge and Ralph Furman, **“More than two thirds of the zeta zeros are simple and on the critical line”**, arXiv:2608.13637 (2026), DOI `10.48550/arXiv.2608.13637`.

Machine-checked source inspected: Anthropic, `zeta-23-lean` (2026), especially `Zeta23/Defs.lean`, `Zeta23/Poisson.lean`, `Zeta23/Taper/Strip.lean`, `Zeta23/Tail.lean`, `Zeta23/ZeroSide.lean`, `Zeta23/ZeroSide/RankTraceMult.lean`, and the `PairCeiling` / `PrimeSideA/EndsWeighted` lanes.

## 1. The Hermitian defect is already hidden in the Frobenius square

For off-line reflection-pair evaluation vectors

\[
u=a+ib,\qquad v=c+id,
\]

define the two natural kernels

\[
S(u,v)=u^Tv,
\qquad
H(u,v)=u^T\bar v.
\]

Write

\[
p=a\cdot c,\quad q=a\cdot d,\quad r=b\cdot c,\quad s=b\cdot d.
\]

Then

\[
S=(p-s)+i(q+r),
\qquad
H=(p+s)+i(r-q).
\]

The real paired blocks used by the 2026 zero-side argument are

\[
Q_u=2m(aa^T-bb^T),
\qquad
Q_v=2n(cc^T-dd^T).
\]

A direct expansion gives

\[
\langle Q_u,Q_v\rangle_F
=4mn(p^2-q^2-r^2+s^2).
\]

But also

\[
\Re(S^2)+\Re(H^2)
=2(p^2-q^2-r^2+s^2).
\]

Therefore

\[
\boxed{
\langle Q_u,Q_v\rangle_F
=2mn\,\Re\!\left(S(u,v)^2+H(u,v)^2\right).
}
\]

`DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda` proves the polynomial core of this identity exactly over the integers.

This materially improves the previous producer picture. The linear Weil trace sees the holomorphic/bilinear channel, but the **nonlinear Frobenius square already contains the Hermitian channel**. We therefore do not automatically need a new linear explicit formula just to make the displacement-sensitive kernel appear.

## 2. Diagonal: the desired transverse residual

For `u=v` and the ideal complex-Poisson baseline, write

\[
A=\|a\|^2,\qquad B=\|b\|^2.
\]

The equal-argument holomorphic identity gives

\[
C=u^Tu=A-B,
\]

while the Hermitian diagonal gives

\[
H=u^T\bar u=A+B=\|u\|^2.
\]

Hence

\[
C^2+H^2=2(A^2+B^2).
\]

The complex-Poisson candidate further predicts

\[
H=L\Phi(-2i\alpha)
=L\int \phi(t)^2\cosh(2\alpha t)\,dt,
\]

where `alpha = beta - 1/2`. Consequently the diagonal Hermitian excess is reflection invariant and coercive:

\[
H-aL^2
=L\int\phi(t)^2(\cosh(2\alpha t)-1)\,dt
\ge
2L\alpha^2\int t^2\phi(t)^2\,dt.
\]

So the diagonal part has exactly the desired geometry:

\[
\boxed{
\alpha=0\iff\text{critical line},
\qquad
|\alpha|>0\Longrightarrow\text{positive Hermitian excess}.
}
\]

## 3. Off diagonal: the real obstruction is interference

The global Frobenius norm is

\[
\left\|\sum_r Q_r\right\|_F^2
=\sum_r\|Q_r\|_F^2
 +2\sum_{r<s}\langle Q_r,Q_s\rangle_F.
\]

The local diagonal excess is positive, but the cross terms are signed. `RiemannWeilPairKernelFrobeniusExact.agda` includes an exact negative-interference witness, so one may not simply discard the off-diagonal sum.

Thus the next theorem is no longer vaguely “find an arithmetic observable.” It is an **almost-orthogonality theorem** of the form

\[
\boxed{
\left|\sum_{r\ne s}m_rm_s
\Re(S_{rs}^2+H_{rs}^2)\right|
\le
\eta(T)
\sum_r m_r^2\bigl(H_{rr}^2-C^2\bigr)
+E(T),
}
\]

with `eta(T) < 1` in the useful range and `E(T)` controlled by the same prime/tail machinery.

If such an estimate holds, the global Frobenius quantity retains a fixed fraction of the positive transverse energy.

## 4. Why the existing analytic infrastructure is relevant

The complex arguments are not outside the source framework. `Zeta23/Taper/Strip.lean` already proves

\[
|\widehat\phi(r-iy)|
\lesssim
\frac{e^{L/4}C_1}{|r-iy|^2},
\qquad |y|\le1/2,
\]

and `Zeta23/Tail.lean` uses exactly this bound for actual off-line zero vectors. Therefore complex-vector decay is already part of the verified proof.

The missing complex Poisson identity can plausibly be obtained from the existing real two-variable identity by normal convergence plus the identity theorem: first continue one variable while fixing the other real, then continue the second. This is not yet formalized in DASHI and is not claimed as closed here.

Once complex Poisson is available, the pair kernels should have the ideal full-grid forms

\[
S_{rs}=L\Phi(z_r-z_s),
\qquad
H_{rs}=L\Phi(z_r-\bar z_s),
\]

with `z_r = gamma_r - i alpha_r`.

The source already has three likely ingredients for interference control:

- complex strip decay of `phiHat`;
- `psi`/autocorrelation decay and finite-grid tail estimates;
- bandwidth-one pair-correlation ceiling/stability machinery.

The open issue is to combine them in a form that controls the **signed squared pair kernels**, not merely zero counts.

## 5. Relation to the existing DASHI prize-facing route

DASHI already has the terminal implication machinery:

```text
positive arithmetic square decomposition
  -> Weil-square positivity
  -> off-line separator contradiction
  -> RH.
```

The present lane should therefore aim to produce a quantitative refinement feeding `RiemannArithmeticCoercivity`, `RiemannWeilSquareCriterion`, or `DashiWeightedValuationSquareCoercivity`, rather than duplicate the terminal theorem.

The desirable intermediate theorem is now:

\[
\boxed{
\|G\|_F^2-\text{critical baseline}
\ge
c\sum_{\rho}m_\rho^2
\left(\Re\rho-\frac12\right)^2w_T(\gamma_\rho)
-E(T),
}
\]

with the left side already controlled through the 2026 explicit-formula/prime-side matrix and `E(T)` negligible or absorbable.

That would upgrade the current `fixed vs nonfixed` inertia count to a genuine transverse energy theorem.

## 6. Ramanujan/Hecke role

The exact Ramanujan lane (`RamanujanTauHecke23Exact.agda`) remains useful as a rigidity template:

\[
\tau(p^2)=\tau(p)^2-p^{11},
\]

with the concrete `p=3` tower also giving the `p^3` recurrence. The lesson is that local spectral data need not be independent; arithmetic compatibility can sharply constrain the allowed global carrier.

No theorem here identifies the zeta pair kernel with a Ramanujan Hecke eigenvalue. A legitimate cross-pollination would require an actual intertwiner between a prime-local recurrence/operator and the Frobenius/Hermitian zero-side energy. Until such an intertwiner is constructed, the Hecke material is architectural guidance only.

## Current fail-closed frontier

```text
pairwise S/H Frobenius identity = exact
negative interference witness = exact
Hermitian diagonal defect = exact conditional algebra
complex Poisson continuation = open here
finite-grid Hermitian retention = open here
pair-kernel almost orthogonality = open here
prime-side transverse coercivity = open here
weighted transverse moment theorem = false
RH proved here = false
```
