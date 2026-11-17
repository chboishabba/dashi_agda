# RH R2 — explicit unconditional shell count A=160, parameterized C, exact remaining lemmas (2026-11-17)

**Classification:** classical unconditional external zero-count theorem plus elementary analytic deductions; local SymPy checks of algebra. **R2 OPEN. No new Agda/Lean kernel theorem.** The explicit value A below is universal but deliberately generous.

## 1. Verified zero-count source and constant

Use Chiara Bellotti and Peng-Jie Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Math. Comp., published electronically 2025-11-14, DOI 10.1090/mcom/4133, with
`|N(U) - U/(2pi)*log(U/(2pi*e))| <= 0.10076 log U + 0.24460 loglog U + 8.08344` for `U>=e`. Count includes multiplicity; no RH required.

For `U>=e`, using `loglog U<=log U`, `U log U>=e`, and `U/(2pi)log(U/(2pi*e)) <= U log U`, one obtains
`N(U) <= (1+0.34536+8.08344/e)*U log U <5U log U`.
For `0<=U<e`, monotonicity gives `N(U)<=N(e)<5e<20`.
Thus for all `U>=0`,
`N(U)<=20(1+U)log(e+U)`.

For `t>=0`, integer `k>=1` and `X=1+t+k>=2`, symmetry of the actual nontrivial zeta zeros about the real axis gives the **multiplicity-weighted** shell count
`Z(t,k)=#{rho: k<=|Im(rho)-t|<k+1} <=2N(t+k+1)`.
Using `1+t+k+1=X+1<=2X` and `log(e+X+1)<=2log(e+X)` gives
**`Z(t,k)<=160*(1+t+k)*log(e+t+k)`**.
At the inclusive shell boundary use `N(t+k+1)` as an upper bound, so endpoints cannot invalidate the inequality. This count is **not** a proportion of off-line zeros and does not assume RH.

Note: the previously supplied Hasanalizade–Shen–Wong JNT DOI was incorrectly given as `...06.028`; the verified DOI is **10.1016/j.jnt.2021.06.032**. The cited Carneiro–Chandee–Milinovich 'Mollifiers and the zeros...' title/identifier was not verified and is not used as a source of this bound.

## 2. Parameterized fourth-derivative kernel constant, NOT yet instantiated

For `P∈C_c^4(R)` supported on `[-L,L]` and
`F(alpha,q)=integral P(u)e^(alpha*u)e^(i*q*u)du` with `|alpha|<=a`, four integrations by parts give
`|F(alpha,q)|<= e^(aL)/|q|^4 * sum_(j=0)^4 binom(4,j)*a^(4-j)*||P^(j)||_1`.
In particular with `r=t/16`, `alpha=(beta-1/2)/r`, the zeta critical strip gives `|alpha|<=1/(2r)=8/t`, and for `|gamma-t|>=k>=1`, using `((k+1)/k)^4<=16`, the multiplicity-normalized physical term has envelope
`C(t,P)/(1+k)^4`, where
`C(t,P)=16*r^2*exp(L/(2r))*[M4+4a M3+6a² M2+4a³ M1+a⁴ M0]`,
`a=1/(2r)`, `M_j=||P^(j)||_1`.

**Important:** the original `W.signedNormalizedPairKernel` is defined as a signed linear combination of `genericProjectivePairKernel` terms for two distinct profiles. Before inserting this `C(t,P)`, one MUST prove the appropriate exact integral representation with its signed pole factors, distinguish possible `cosh(alpha u)`/base subtractions, and bound each term. The formula is a **conditional donor**, not an evaluation of the selected witness.

The original Lean identity is
`signedLiteralPairSourceTerm sigma = mult(sigma)/r² * W.signedNormalizedPairKernel ((beta-1/2)/r) ((gamma-t)/r)`.
Original finite far source is `W.literalFarExactAt eta n` with `eta=1/(pi+1)` and `centeredZeroFinset t n` iff `t-n<gamma<=t+n`. The original `literalGoodQuarticGainAt` uses `S*(alpha²q²-q⁴/6)`, **not** the newer complete quartic with an additional `-alpha⁴/6`.

## 3. Local executable check

`scripts/check_rh_r2_explicit_zero_shell_fourier_20261117.py` checks:
- the 2025 published coefficients imply the generous factor 5 via exact rational/SymPy inequalities;
- the two-sided unit-shell count admits A=160;
- binomial fourth derivative envelope and physical rescaling;
- the exact fixed-t tail integral and monotonicity.

It does **not** numerically integrate the selected W or formally prove the cited N(U) theorem. These remain separate acceptance gates.

## 4. Exact remaining lemmas / producers

1. **`selectedQuarticFourWActualProfileIntegralExact` (OPEN):** extract the constructed `QuarticFourSignedPolePair t` and show the exact selected `signedNormalizedPairKernel` equals the claimed Fourier integral or a finite combination, including pole coefficients, horizontal factor and source normalization, for every `alpha,q`.
2. **`selectedQuarticFourWDerivativeNormsExplicit` (OPEN):** determine actual W parameters and compact support `L`, calculate/certify `||P_j^(m)||_1` for `m=0,...,4`, bound `cosh`/horizontal terms, and construct an explicit valid `C(t,W)` on `0<=beta<=1`. A symbolic expression with unknown norms does not close this lemma.
3. **`originalActualZetaUnitShellCountA160` (CLASSICAL COROLLARY; NATIVE OPEN):** instantiate Bellotti–Wong 2025 zero count in Lean for the original `Zeros` type, multiplicity, real-axis reflection and interval endpoints; deliver the numeric universal constant `A=160`.
4. **`originalLiteralFarExactCertifiedFinite` (OPEN):** certified interval value of `W.literalFarExactAt eta n` for the source selected W and actual zero ordinates, preserving sign; verify `OffOrdExactAt=ConeExactAt+GoodExactAt+FarExactAt`.
5. **`originalSelectedTargetThresholdCertified` (OPEN):** calculate actual `T_W(rho)=4D_comb(rho)+∫Psi_t dmu` from the literal selected witness, not generic surrogate.
6. **`originalSelectedFiniteSignedSurplusStrict` (OPEN):** construct a rational `epsilon>0` and finite cutoff with a **certified** positive surplus in the *correct polarity*, including local remainder and target threshold; explicitly handle same-height exclusion and multiplicities.
7. **`originalSelectedUniformCofinalTail` (OPEN):** combine an instantiated `A,C(t,W)` with a rigorously uniform cutoff and the literal signed far term; the supplied majorant only converges with n for fixed t.
8. **`originalR2EventualSignedCompensationGap` (OPEN):** prove `exists eps>0, N, forall n>=N: LocalDebt_n-SignedCompensation_n<=T_W(rho)-eps` for the originally quantified t,rho,W. For fixed t and W, a certified total surplus and a tail smaller than half that surplus suffice; a margin depending on t or rho does **not** imply the universal target.
9. **`originalR2NativeKernelWeld` (OPEN):** typecheck and import the actual proof at exact Lean/Agda heads, then update gate ledger only after the original acceptance predicate is discharged.

**Accounting:** Classical external A bound established, but the native carrier and all selected-W signed-gap producers OPEN. Portfolio remains **13/28 settled, 15/28 open**; **0/6 original Clay endpoints**.
