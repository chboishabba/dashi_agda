## 22 November 2026 — selected-W FULL horizontal-weighted q^-4 formula (symbolically discharged, constants/uniformity OPEN)

Following the source correction, the original Lean theorem
`QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral`
and the original actual selected-W compact-`C⁴` theorem
give a concrete **human-level symbolic full-horizontal kernel
tail** at any fixed selected `W` and `t`, not just the
unweighted base channel.

Let `P_W=quarticFourSignedPoleCombinedProfile
W.R W.muHalf W.muTwo t`, supported in
`[-L,L]` (take `L=π+W.R` from the
source four-center bump support), and define
`M_j(W)=∫ |∂_x^j P_W(x)| dx` for `0≤j≤4`.
For `q≠0`, `|α|≤a`, put
`P_{W,α}(x)=P_W(x)cosh(αx)`. Product
differentiation gives the **exact formula**
```text
(P_W cosh(αx))'''' =
    P_W'''' cosh(αx)
  + 4α P_W''' sinh(αx)
  + 6α² P_W'' cosh(αx)
  + 4α³ P_W' sinh(αx)
  + α⁴ P_W cosh(αx).
```
On `|x|≤L`,
`|cosh(αx)|,|sinh(αx)|≤exp(aL)`.
The already source-proved compact Fourier
fourfold integration-by-parts lemma therefore
yields the precise conditional-norm inequality
```text
|W.signedNormalizedPairKernel(α,q)|
 ≤ exp(aL)/|q|^4
    ·[M4 + 4a M3 + 6a² M2 + 4a³ M1 + a⁴ M0].
```
For an actual off-ordinate zero `σ` in the
critical strip, the source identifies
`r=t/16`, `α=(Re σ−1/2)/r`,
`q=(Im σ−t)/r`. Hence for `t>0`,
`|α|<8/t`, and
```text
|W.signedLiteralPairSourceTerm σ|
 ≤ mult(σ) (t/16)^2 exp(8L/t)
   · [M4+4(8/t)M3+6(8/t)^2M2
        +4(8/t)^3M1+(8/t)^4M0]
   / |Im σ−t|^4.
```
The `mult(σ)` is the actual original zeta
zero multiplicity, NOT dropped for a
scalar surrogate. The estimate applies to
**both horizontal sides** because the
kernel is cosh-even in `α`; it is
an ABSOLUTE tail envelope and proves
NO desired signed surplus by itself.

**Local executable mathematical check:** the EXISTING
`scripts/check_rh_r2_explicit_zero_shell_fourier_20261117.py`
was extended in place (commit `e3c25a13`) to audit
the exact source identity status, the five-term
weighted fourth Leibniz derivative,
horizontal reflection, `α=0` base recovery
and true strip `8/t` radius. Independently
executed local SymPy 1.14.0: **7/7**
new exact derivative/normalization assertions
PASS. The full revised file has been
committed and source-readback verified but
not executed end-to-end in this runtime;
do not state a complete script receipt
or native Lean kernel result.

**Precisely UNPAID:** obtain numerical/source-quantified
uniform bounds for the **actual**
`W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo`
and `M_j(W)`; prove those are strong enough,
with actual two-sided ζ-zero counts and
tail/cutoff quantifiers, to pay the
correct-polarity cofinal
`W.UniformSignedCompensationGap rho`.
An arbitrary fixed-t positive finite-core
estimate, absolute convergence, symbolic
`q^-4` formula or same-ordinate local
positive signal does not imply the
universal strict RH inequality. This
update is a proof-of-algebraic-estimate
at paper level, **not** a new kernel-accepted
original analytic GRH/RH result.

---

## 22 November 2026 — SOURCE RECLASSIFICATION: selected-W integral already proved

This dated source audit **supersedes the first 17 Nov open
lemma** `selectedQuarticFourWActualProfileIntegralExact`,
as phrased there: **the literal same-selected-W
weighted Fourier/cosh representation is ALREADY
theorem-bearing in original Lean main**, not an
unconstructed theorem. Do not write a new replacement
theorem or copy the same proof into this branch.

Inspected exact source paths and Git blobs:

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
  blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`,
  **lines 1142–1203**:
  `QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral`
  proves directly, for the ACTUAL selected
  `QuarticFourSignedPolePair t`,
  ```text
  W.signedNormalizedPairKernel α q =
     ∫ x, quarticFourSignedPoleCombinedProfile
                W.R W.muHalf W.muTwo t x
             * cosh(α*x) * cos(q*x)
  ```
  including both original signed pole coefficients
  and the two actual source windows; the proof
  establishes integrability and expands the true
  source definitions, not an abstract W.
- In the **same** source, lines 415–440:
  `W.signedLiteralPairSourceTerm_eq_normalizedPairKernel`
  identifies the genuine original non-same-ordinate
  zero summand with
  `mult(σ)/(t/16)² * K_W(heightOf σ/(t/16),
      (Im σ−t)/(t/16))`. The necessary analytic
  `Re(s)−1/2` reflection is already visible
  through the cosh-even dependence.
  `W.signedNormalizedPairKernel_eq_jointJet`
  and `_eq_quarticJet` also source-write
  the exact base/horizontal/remainder split.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean`
  blob `16110e433efd16379c6b93bdc13420036b1d6411`
  defines the **literal** combined profile and
  exact zero- and second-moment identities.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean`
  blob `6b30db459d28a2b5707cec004b570ff7061e1a8a`
  proves source-selected
  `quarticFourSignedPoleCombinedProfile_contDiff_four`,
  `compactCosineTransform_abs_le_invPowFour`
  and the **literal base ordinate channel**
  `W.signedOrdinateTest_abs_le_gap_four`,
  ```text
  |W.signedOrdinateTest x|
    ≤ (t/16)² * ∫ |P_W''''(u)| du / (x−t)⁴
  ```
  for x≠t and t>0. The original proof
  already uses the actual combined W profile,
  not an arbitrary test substitute.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean`
  blob `2fb66d2e7c4345673e1dda82e67823bf2d7e0481`
  proves the actual cone/good/far
  **algebraic** split and convergence compiler,
  but `W.UniformSignedCompensationGap rho`
  at lines 941–953 remains an **ASSUMED
  strict eventually quantified inequality**.
  Its theorem
  `completedSignedResidual_lt_target_of_uniform_compensation_gap`
  at lines 960+ consumes, rather than constructs,
  that analytic payment.

**Revised R2 priority:**
1. **PAID SOURCE-WRITTEN:** exact selected
   W ↔ weighted cosh-cos integral,
   source multiplicity/scaling and both
   horizontal sides, exact `C^4`/compact
   selected W, fourth-power base-channel
   `signedOrdinateTest` decay.
2. **OPEN QUANTITATIVE:** explicit *selected*
   `W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo`,
   actual derivative-norm and
   horizontal-weighted `P_W(x)cosh(αx)`
   bounds and their uniformity in t,
   original ζ zero multiplicities and
   cutoff. Do not incorrectly promote
   the `α=0` **base** tail theorem
   to the full `α≠0` horizontal source.
3. **OPEN ORIGINAL SIGN:** a **strict
   correct-polarity cofinal margin**
   `W.UniformSignedCompensationGap rho`
   or its source-valid sharpened version,
   with actual original ζ-zero configurations,
   completed residual and the exact
   quantifier order (not test-specific floats).
4. **OPEN TRUST:** no new exact-head Lean
   kernel receipt was run by this
   Git source-readback audit.

**Acceptance distinction:** source declarations, bodies
and dependency edges were read directly from the current
`dashi_lean4/main` tree, but no Lean/Agda typechecking
was executed in this runtime. This corrects a
stale research-status classification rather
than newly proving an R2 estimate.

---

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
