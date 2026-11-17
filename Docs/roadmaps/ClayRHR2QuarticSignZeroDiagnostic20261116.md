# RH R2 — completed quartic exact sign and numerical zero controls (2026-11-16)

**Classification:** exact SymPy polynomial identities + numerical mpmath controls; **R2 OPEN**, no actual selected-W finite compensation evaluation, no certified cofinal tail, no Lean/Agda kernel receipt.

## Original owners

Read exact branch sources:
- `DASHI/Analysis/RiemannQuarticSignedPoleCompensationExact.agda`: completed quartic `K_W(alpha,q)=S(W)*(alpha²q²-(alpha⁴+q⁴)/6)+R6`, bound `|R6|<=M6*(7/4320*(|q|⁶+|alpha|⁶)+5/192*alpha²*|q|⁴+1/48*|alpha|⁴*|q|²)`, sharpened `ConeGain+GoodGain-FarExact` and eventual signed-gap still `openAnalyticObstruction`.
- `DASHI/Analysis/RiemannQuarticSignedPoleConeDebtExact.agda`: older partition `q²<=6alpha²` for `ConeDebt` (positive-part upper debt), **not a claim of full completed-quartic positivity**; `FarExact` must remain literal and signed.
- `DASHI/Analysis/RiemannQuarticSignedPoleJointHorizontalJetExact.agda`: earlier incomplete jet `alpha²q²-q⁴/6`; cannot substitute for complete quartic.
- `Docs/roadmaps/BishopEtaRHA2G3MaximumCutRound20261114.md`: actual selected `QuarticFourSignedPolePair t`, `W.targetStrength`, `W.fourthLipschitz`; warns that `FarExact` is `FarBaseExact+FarHorizontalExact` and not a generic pole sum. Selected witness and exact Lean formula must be read from the Lean owner before an actual R2 run.

## Exact new mathematical cut

For `alpha!=0`, set `r=q²/alpha²>=0`. Then
`6 P/alpha⁴=6r-1-r²=8-(r-3)²`. Therefore `P>0` iff `3-2sqrt(2)<r<3+2sqrt(2)`. At `alpha=0`, `P=-q⁴/6<=0`. The old cone `r<=6` includes `r=0`, where `P(1,0)=-1/6`, and a positive band near `r=1` where `P(1,1)=2/3`. The completed quartic is negative in both extreme ratio tails, positive only in the middle band. This is a **new diagnostic partition**, not a refutation of the existing conservative cone debt theorem.

For positive selected strength S and nonnegative sixth-bound constant M, with `B(alpha,q)` the source sixth-order polynomial, `S*P>M*B` rigorously certifies `K_W>0`; `S*P< -M*B` certifies `K_W<0` **only inside the original local domain**. In particular, the quartic-only sign near the boundaries is not enough.

The local Taylor normalization is `alpha=(beta-1/2)/(t/16)`, `q=(gamma-t)/(t/16)`. Computing only known critical-line zeros gives `alpha=0` numerically; this does **not** test the off-line signed compensation or establish that all zeros lie on the line.

## Executed checks

The standalone equivalent Python script was executed in the working container: **PASS** symbolic factorization, exact sign endpoints, sample signs, all four sixth-order coefficients, fourth/sixth homogeneity; 32 mpmath `zetazero(k)` ordinates at 45-digit precision with small `abs(zeta(z))` residuals. These are **numerical zeros, not rigorous zero-isolation certificates**, and the script does not compute the selected W or FarExact. The checked script is committed as `scripts/check_rh_r2_quartic_zero_diagnostic_20261116.py`.

## Precise unfinished work

1. Fetch actual Lean selected `QuarticFourSignedPolePair t` and original `W` definition/parameters, exact pair kernel, zero multiplicity, local radius and symmetric cofinal ordering; cross-check normalization.
2. Implement literal `FarBaseExact+FarHorizontalExact` and exact cone/good signed decomposition with independently reproduced source values; reject substitutes.
3. Use certified zero intervals (rather than only mpmath approximations), exact/interval evaluation of selected W, and interval bounds for each finite pair sum.
4. Obtain a **uniform bound on the omitted cofinal tail** and a strict eventual epsilon margin, or rigorously falsify the claimed uniform margin for an admissible actual-zero configuration.
5. Keep `R2` OPEN until the actual selected signed inequality is proved or rigorously refuted; no implication to RH or any Clay endpoint.

**Portfolio unchanged: 13/28 settled, 15/28 OPEN, 0/6 original Clay endpoints proved.**
