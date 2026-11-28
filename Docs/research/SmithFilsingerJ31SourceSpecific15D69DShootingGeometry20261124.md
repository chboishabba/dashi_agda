# J31 — original-source seven-chart shooting: 15D event-time system versus true sparse 69D multiple shooting

**24 November 2026 | [Filsinger PR #1537](https://github.com/chboishabba/dashi_agda/pull/1537) | original Smith/Filsinger attribution | mathematical synthetic prescribed-wave receiver only.**

## Actual contribution and scope

The J30B [exact six-event Schur theorem](SmithFilsingerJ30BSixGuardAugmentedShootingSchur20261123.md) was a **general exact algebraic** reduction, not a calculation of the original six-guard Jacobian. J31 now constructs **source-specific numerical** seven-segment shooting using the original nine-state J25 finite-loss synthetic equations, both coupled coils, actual diode current law, actual switched spark, nonlinear HF capacitor and both signed external wave quadratures. It uses no substitution of a different receiving circuit.

The committed [replayable J31 source](../../scripts/check_smith_filsinger_j31_source_15d_69d_shooting_20261124.py) computes \(\mathbb R^{15}\) residuals and analytic \(15\times15\) derivative blocks for **all seven original physical mode segments** in chronological order, as well as an independently assembled **genuine sparse 69-variable multiple-shooting lift**. The committed [execution receipt](../../Artifacts/smith-filsinger/j31_source_15d_69d_shooting_geometry_audit_20261124.json) retains model scope, exact-vs-numerical flags, and quantitative checks. It reuses the original [independent six-event source numerical solver](../../scripts/independent_full_period_numerical_audit.py) and [independent hybrid tangent](../../scripts/independent_full_period_monodromy_audit.py) as distinct cross-checks, whose Git blobs are recorded in the receipt.

**Mathematical endpoint remains OPEN**. Neither source-specific numerical \(DF(z_0)\) nor the finite-difference checks bound \(DF\) over an interval box; the next Krawczyk acceptance must be strict and outward-validated. The separate original physical metering/source and the original J24 last numerical event-state box remain unpaid.

## Six physical event times and signed guards

The original mode sequence, with entries \((U\text{ diode},V\text{ diode},\text{spark})\), is

\[
(0,0,1)\to(0,1,1)\to(0,1,0)\to(0,1,1)
\to(1,1,1)\to(1,0,1)\to(0,0,1).
\]

The guards are \(g_V=v-b-V_d\), \(g_{\rm spark,off}=b-V_{\rm off}\), \(g_{\rm spark,on}=b-V_{\rm on}\), \(g_U=u-b-V_d\), \(g_V\), \(g_U\), in that exact order; the numerical pre-event derivative signs are \(+,-,+,+,-,-\). The original four diode crossings have a continuous state vector field and identity saltation at the zero-current guard; both spark transitions have a nontrivial rank-one saltation. The clock stays at \(\tau=20\pi/11\). The original J29 exact-rational receipt, **not the numerical output here**, remains the producer for the **6/6 nominal exact root count**.

## Exact algebra: why true independent seven-chart shooting needs 69 variables

For a 15D *scheduled-switch* formulation take \(z=(x_0,t_1,\ldots,t_6)\), nine initial states plus six crossing times. Compose seven source-owned smooth maps \(\Phi_j(t_{j+1},t_j,\cdot)\) to form the original terminal return and six guards:

\[
F_{15}(z)=
\begin{pmatrix}
 \Phi_6\circ\cdots\circ\Phi_0(x_0)-x_0\\
 g_1(X(t_1))\\ \vdots\\g_6(X(t_6))
\end{pmatrix}.
\]

This 15D formulation **still composes the interface states**, so treating its seven charts as independent variables without adding their matching equations would drop necessary constraints. To genuinely centre the seven smooth charts independently, introduce six nine-state interface vectors \(y_1,\ldots,y_6\), for **54 additional unknowns**. The correct true multiple-shooting unknown is

\[
Z=(x_0,y_1,\ldots,y_6,t_1,\ldots,t_6)\in\mathbb R^{69}.
\]

With \(y_0=x_0\), the 69 original-source equations are:

\[
\begin{aligned}
H_i(Z)&=y_i-\Phi_{i-1}(t_i,t_{i-1},y_{i-1})=0,\quad i=1,\ldots,6
& (54\text{ matching coordinates});\\
R(Z)&=\Phi_6(\tau,t_6,y_6)-x_0=0 &(9\text{ return coordinates});\\
G_i(Z)&=g_i(y_i)=0,\quad i=1,\ldots,6 &(6\text{ guard coordinates}).
\end{aligned}
\]

The Jacobian of the 54 matching equations is block lower bidiagonal in the interface-state variables, with an identity block on each \(y_i\) diagonal. Those six interface vectors can therefore be eliminated *uniquely by forward substitution*, recovering \(F_{15}\) and its analytic 15D Jacobian. **This is an exact algebraic equivalence** of zeros whenever all seven segment maps exist; it is not a numerical approximation and does not require periodic existence as a premise. Its determinant/invertibility relationship is a signed row/column permutation times the 15D determinant, and the further J30B time-guard Schur reduction identifies the six signed crossing slopes times \(\det(M_\tau-I_9)\).

The rigorous-proof advantage of **69D** is not a stronger existence theorem for free. It is the ability to validate the seven individual short maps on *their own outward state/time boxes*, using sparse matching blocks, avoiding the explosion from a single global 9D interval enclosure. A numerical or interval proof must retain all 54 matching equations; a missing match invalidates the physical conclusion.

## Source-specific computed results (NUMERICAL only)

The locally executed more extensive J31 source-specific diagnostic, with 15 coordinate-direction finite differences and an independently assembled 69D matching Jacobian, recorded:

| Source-equation numerical check | Observation |
|---|---:|
| Full \(F_{15}(z_0)\) infinity residual | \(3.4949293459\times10^{-11}\) |
| Full \(F_{15}\) residual after coupled Newton correction | \(1.6875389974\times10^{-14}\) |
| Analytic 15D guard-time Schur reduced hybrid derivative vs independently assembled six saltations | \(7.1795867862\times10^{-16}\) |
| Recovered \(9\times9\) hybrid derivative vs separate original numerical tangent | \(1.2864765698\times10^{-10}\) |
| Rounding the source-specific \(15\times15\) inverse to rational denominator \(10^{12}\): sampled centre \(\|I-CJ(z_0)\|_\infty\) | \(3.8712758197\times10^{-12}\) |
| Max analytic 15D Jacobian column vs centred finite difference over all 15 coordinates | \(3.5527335114\times10^{-9}\) |
| 69D independent chart matching residual | zero within same numerical execution |
| **Eliminating the 54 interface corrections from the 69D Newton system vs direct 15D Newton correction** | **\(2.9309906052\times10^{-24}\)** |
| 69D sparse matrix | **748 nonzeros out of 4,761 entries** |
| 69D numerical 2-norm condition number | \(\approx8497.86\) |

The compact repository replay source evaluates the same source-defined 15D/69D geometry and emits a full source Jacobian and rationalized preconditioner in a machine JSON receipt when invoked locally. The detailed figures above were recorded from the locally executed J31 formulation; **the compact committed source is not asserted to be byte-identical to that longer local experimental driver**, and no CI or Agda execution is claimed. The earlier independent monodromy and finite-difference sources are separately committed and source-pinned.

**These are diagnostics, not validated inequalities.** The very small 69D-vs-15D Newton mismatch is a numerical regression of the exact matching-elimination theorem, and does not prove all-ball inclusion or a rigorous centre defect. The 69D unscaled matrix is substantially more ill-conditioned than the nine-state return matrix, so an **appropriately scaled** rational preconditioner is necessary for a useful interval test.

## One remaining J31 maximum cut

**Mathematical objective:** exact nonlinear \(\tau\)-periodic solution for the *nominal, prescribed-wave, original nine-state model*, including all six original guard transitions, source clock, two spark saltations, four diode law changes and no hidden resets.

1. **Seven individually validated original-source interval charts.** On one nonzero \(69\)-variable rational box \(B_{69}\), produce outward Taylor/Lohner state maps \([\Phi_i]\), local full-time guard sign conditions and \([D\Phi_i]\); keep time and state correlations and the irrational endpoint \(\tau\) from J30's exact rational Machin bracket. Declare and verify **all 54 state matching equations**, not merely seven independent approximate integrations.
2. **One sparse source-dependent \(69\times69\) interval derivative and exact rational preconditioner**, or perform an *interval-safe* Schur reduction into \(15\times15\) with explicitly proved enclosure of every eliminated term. The numerical rounded inverse is an **approximate starting design only**. Do not treat \(q_0\) from a sampled matrix as an interval contraction bound.
3. **One strict inward inclusion and uniqueness proof**, using an actual source-owned \([F(B)]\) and \([DF(B)]\), e.g.
\[
K(B)=z_0-CF(z_0)+(I-C[DF(B)])(B-z_0)\subset\operatorname{int}B.
\]
Every accepted normal mode must remain sign-consistent throughout the seven chart interiors; every event guard must cross with strict signed slope, correct chronology and no extra switches.
4. Once that entire single accepted Krawczyk packet passes, promote exactly the nominal existence/uniqueness theorem and then its **11-fold original \(T=20\pi\) transport**. The original J24 sixth *preselected numerical-centre state box* is a separate diagnostic, not a logical prerequisite if the new 69D guard-admission contract is itself fully certified. A uniform five-parameter family remains another theorem.

**Fail closed** if any interval chart, guard, source phase, matching residual, Jacobian enclosure, Krawczyk margin or exact original circuit identity is missing. No small isolated event-lemma promotions, no GitHub Actions, no unmeasured source/receiver coupling or hardware efficiency promotion. Preserve original Smith/Filsinger and donor attribution.
