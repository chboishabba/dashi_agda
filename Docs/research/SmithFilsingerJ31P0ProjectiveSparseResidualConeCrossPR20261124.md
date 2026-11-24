# Filsinger J31 P0 — projective sparse Schur/interval-cone weld from P≠NP, π and Langlands (24 November 2026)

**Original proof owner** [#1537](https://github.com/chboishabba/dashi_agda/pull/1537); actual mathematical source: Smith/Filsinger-attributed prescribed-wave finite-loss J25–J31 synthetic nine-state ODE. **This is not** an experimental receiver, source power measurement or exact periodic-orbit proof. The donor PRs are **mathematical techniques**, not source premises about the electrical apparatus.

## Exact donor inspection and owner boundaries

| Source donor | Latest inspected source | Exact transfer to J31 | Scope/exclusion |
|---|---|---|---|
| Clay P vs NP [Agda #1548](https://github.com/chboishabba/dashi_agda/pull/1548), [Lean #119](https://github.com/chboishabba/dashi_lean4/pull/119) | N1–N3 costed same-semantic carrier; G56–G59 signed low-mode vs original relation and indexed residual; G60–G64 degree/valuation interface | Preserve actual 54 matching costs + guard-time steps; choose sufficient *consumer* (69 row-slack inequalities) rather than globally minimal state representation. Signed zero residual ≠ deleted state. | P≠NP, circuit lower bounds, high-order Fourier rank do NOT imply hybrid-orbit existence or complexity bounds for this ODE. |
| Paper 9 π [Agda #1546](https://github.com/chboishabba/dashi_agda/pull/1546), historical [#1529](https://github.com/chboishabba/dashi_agda/pull/1529) | G4 directly output-aligned integer radical, G5 source-ordered noncommutative product and peak-resource schedule, G6 root-free integer signed-square verifier; candidate G4–G6 described as UNTESTED | Check the **strict Krawczyk row slack** directly with rational integers, not a separately inflated global matrix-norm estimate; retain matrix composition/chronology and independent source/consumer receipts. | π Chudnovsky series/tail and run-time figures are unrelated to and cannot prove J31 source ODE. Root-free square trick only applies to the original nonnegative π inequalities; here use exact rational interval products, not squaring signed guards. |
| Ramified Langlands/GCT [Agda #1549](https://github.com/chboishabba/dashi_agda/pull/1549), [Lean #120](https://github.com/chboishabba/dashi_lean4/pull/120) | R85–R89 source-labelled zero mode, signed residual, t/k/chart and observer collision; R92–R98 inherited precision/carry and exact local coefficient constraints | Eliminate interface variables **algebraically** while retaining all original 54 signed matching residuals, six guard-zero equations, sign/transversality, time and chart provenance; track rounding/precision in original source coordinates. | Rank-one observer collisions, 2-adic precision or weighted Fourier masks cannot supply missing real differential-equation interval bounds. |

All four main donor PRs were checked at their **current head on 24 November**. Agda #1548 and #1549 are separately master-based; Lean #119 and #120 are separately main-based. No donor code or claims copied as a physical theorem, no divergent merges, no GitHub CI.

## Exact algebraic structural result: retained-matching 69D preconditioner

Take original J31 genuine sparse 69D multiple-shooting equations and reindex the **variables only** to \(u=(x_0,t_1,\dots,t_6)\in\mathbb R^{15}\), \(v=(y_1,\dots,y_6)\in\mathbb R^{54}\). Keep residual order as \(F=(h,r)\): \(h\in\mathbb R^{54}\) are **all** named segment matching errors; \(r\in\mathbb R^{15}\) is nine periodic-return components and six actual guard errors.

For a centre Jacobian \[A=\begin{bmatrix}H_u&H_v\\R_u&R_v\end{bmatrix},\] source construction gives \(H_v=I+L\), with \(L\) strict block-lower triangular over six event interfaces. In particular \(L^6=0\), so \(T=H_v^{-1}=\sum_{j=0}^{5}(-L)^j\) is **exact**, rather than an unexplained black-box dense inverse. Define \(L_r=R_vT\) and the 15D Schur block \(S=R_u-L_rH_u\), and pick a candidate **rational** 15×15 inverse \(B\), not assumed to be the true inverse.

Then the following **source-compatible structured 69D left preconditioner** is an *exact algebraic* construction:

\[
C=\begin{bmatrix}
-BL_r & B\\
T+TH_uBL_r &-TH_uB
\end{bmatrix},
\qquad
I_{69}-CA=
\begin{bmatrix}
I_{15}-BS&0\\
-TH_u(I_{15}-BS)&0
\end{bmatrix}.
\]

The 54 matching columns **vanish from the centre residual of this particular constructed preconditioner**, but **the matching equation residuals do not vanish**. The signed preconditioned full centre residual is
\[
(CF)_u=B(r-L_rh),\qquad
(CF)_v=Th-TH_uB(r-L_rh).
\]
Dropping \(h\) is invalid even when a reduced/terminal observation is zero: a large interface mismatch can make the true 69D strict-inclusion test fail. The labelled \(h\) is the dependent signed residual required by the Langlands and indexed-hyperfabric comparison; it is **not** an additional physical energy reservoir or an independently existing zero-mode state.

These formulas avoid constructing/inverting a dense 69D central matrix and reduce the difficult centre inverse to **15D**, while preserving all 69 original equations. They do not by themselves bound \(DF(B_{69})\) over a nonzero state-time neighbourhood or establish that the seven source ODE charts exist with the required guards.

## Output-aligned exact rational Krawczyk gate

For a positive rational 69-coordinate radius vector \(r_i>0\), a *genuinely source-validated* \(F(z_0)\) interval, a *genuinely source-validated* 69×69 \([DF(B_{69})]\), and a **fixed rational** \(C\) computed independently of interval variation, certify for each variable coordinate \(i\)
\[
\boxed{
s_i=r_i-\sup|(CF(z_0))_i|
 -\sum_{j=1}^{69} r_j\,\sup|(I-C[DF(B_{69})])_{ij}|>0.
}
\]
All interval endpoints are exact Python fractions; \(s_i>0\) is a sign test rather than a floating tolerance. Record all 69 signed slacks, the source-to-output residual terms and each chart's contribution, not solely a scalar max. A strict inward Krawczyk image is enough for existence under the usual validated \(C^1\)/invertibility assumptions, with uniqueness requiring the suitable interval-Newton or contraction argument and verified guard/mode itinerary. The certificate receiver is therefore **not** a replacement for its required original-source Taylor/Lohner producer.

**Crucial negative control:** a proof may pass on a numerical terminal observer with \(r=0\) while \(h\ne0\). The exact fixture forces a nonzero matching residual which the terminal rows cannot see; the 69D gate rejects it when made larger than the rational ball. Equal projected terminal zero is **not** full-interface equality. Preserve the zero mode (zero guard equations), signed residual (matching errors), physical time \(\tau\), event index, chart refinement \(k\), precision and source SHA as separate labels; never collapse time and chart or turn uncertain sign into a Boolean positive.

## Executed checks, committed source, and limitations

[Source and exact cone checker](../../scripts/check_smith_filsinger_j31_projective_sparse_preconditioner_20261124.py) runs in three modes: \`--exact-fixture\` (nontrivial **69D exact Fraction** Schur identity, all 69 rational row slacks, adversarial hidden-mismatch rejection); \`--numeric-source\` (actual original seven-mode J31 numerical chart Jacobian and 15D/69D structural preconditioner); and \`--verify-json FILE\` (exact rational conditional row slacks for an externally supplied \`J31_69D_INTERVAL_CONE_V1\` witness; **never** a source validation from metadata alone).

**Local exact fixture PASS:** 54 labelled matches, 15 quotient variables, all 69 strict row-slack checks, and terminal-observer mismatch negative control. **Local numerical source-shaped audit PASS:** actual 69D sparse original-source central Jacobian has 748 nonzero entries; Schur vs independent 15D Jacobian infinity difference \(\approx5.37\times10^{-15}\); centre preconditioner \(\|I-CJ\|_\infty\approx3.2022\times10^{-11}\); exact structural predicted-block residual versus observed numerical residual \(\approx5.46\times10^{-13}\). The tested numerical donor was a longer local J31 source-equation implementation, not a byte-reexecution of this newly committed compact source. No full original source interval ODE chart computation was executed in this tranche; no Agda/Lean kernel or CI. The exact fixture is **linear synthetic algebra**, not Filsinger physical proof.

**Remaining one maximum cut:** source-pin the seven original smooth ODE branch Taylor/Lohner charts and guard signs across a nonzero rational 69D box, including the first long source segment; construct outward-rational **centre \(F(z_0)\)** and actual full **\([DF(B)]\)**, with explicit source-forcing time enclosure \(\tau=20\pi/11\), no dropped 54 matches, signs \((+,-,+,+,-,-)\) for the six original guards and two actual spark saltations; then pass all 69 strict row inequalities and a uniqueness argument. If the first long segment overwraps, split it further with **paid** matching variables rather than silently using an unvalidated long source chart. No intermediate numerical root/pin/100%-energy claim promoted. Original J29/J30 nominal 6/6 roots, original J24 5/6 state boxes and exact nominal return remain the accepted frontier.

## Related sources

- [J31 original 15D/69D shooting geometry](SmithFilsingerJ31SourceSpecific15D69DShootingGeometry20261124.md)
- [J30 exact six-event nominal return](SmithFilsingerJ30AllSixGuardFullSourcePeriodReturnValidated20261123.md)
- [J30B 15D Schur algebra](SmithFilsingerJ30BSixGuardAugmentedShootingSchur20261123.md)
- [Filsinger authoritative roadmap](../roadmaps/FilsingerP0SixGuardExactStatusAndJ31ShootingCut20261124.md)
- [Original attribution policy](../SourceAttributionPolicy.md)
