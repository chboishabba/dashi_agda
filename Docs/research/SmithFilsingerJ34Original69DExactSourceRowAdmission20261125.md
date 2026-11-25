# J34 — original 69D source-labelled shooting assembly: first 15 exact rows admitted, remaining 54 fail closed

**25 November 2026 · controlling draft [DASHI #1537](https://github.com/chboishabba/dashi_agda/pull/1537)**

The original Smith/Filsinger-attributed J23–J33 **synthetic, externally prescribed-wave, finite-loss nine-state** source and original six physical diode/spark events remain authoritative. J34's contribution is a *source-labelled exact rational* 69D multiple-shooting row producer, six physical transversality checks on an explicitly nonzero 69D input box, independently source-checked numerical Schur diagnostic, and a fail-closed complete-row requirement. There is **NO claimed physical device measurement, environmental energy source, exact periodic orbit, or whole-ball 69D Krawczyk inclusion**.

## Committed executable, reproducibility and nine adversarial acceptance tests

- [Source-specific exact-rational 69D interval row producer](../../scripts/check_smith_filsinger_j34_69d_exact_rows_20261125.py): exact local execution and Git blob parity **7aa09a7d421da56b7d65d5d44e20c6542fdbcbb1**.
- [Original-source adversarial test](../../scripts/test_smith_filsinger_j34_exact_rows_20261125.py): local **9/9 PASS**, exact tested Git blob **81c1ae66e6f0a53d4a9ba8b01dc60890de7aa63e**.
- [Machine admission and missing-row receipt](../../Artifacts/smith-filsinger/j34_original_69d_15_source_rows_and_schur_audit_20261125.json): all six signed guard slope bands, actual source J33 proof checksum, cross-source numeric diagnostic, and six exact missing-row owners.
- Required J33 full original-source 256-slab Fraction output: **49,898 bytes**, pinned SHA256 **1736f652288fd77bfc165fc86eadb268fc94418c9024e19591a70bc08a4beb3b**. This **full J33 output** is not the previously committed *compact* J33 receipt. Regenerate it with the committed [J33 moving rational coframe source](../../scripts/check_smith_filsinger_j33_coframe_initial_full_20261125.py), which creates its own numerical *frame proposals* but proves every inverse, Picard, PB6 and physical-source inequality using exact rational arithmetic.
- Locally executed J34 full exact 15-row output is **23,298 bytes**, SHA256 **ae9bec481ef0e0a6f43841cf5c3127615707d658a191d011bb3c52d6d750f544**, and is reproducible from the committed exact row source plus that pinned full J33 result. The separate local original-ODE numerical 69D and 15D regression is diagnostic only, not a byte-identical committed secondary executor. No GitHub CI or proof kernel used.

Commands on a checked-out PR #1537 branch:

\`\`\`sh
python scripts/check_smith_filsinger_j33_coframe_initial_full_20261125.py --N 256 --frames j33_frames.json --out j33_full.json
python scripts/check_smith_filsinger_j34_69d_exact_rows_20261125.py --j33 j33_full.json --out j34_exact_rows.json
python scripts/test_smith_filsinger_j34_exact_rows_20261125.py --j33 j33_full.json --out j34_negative_tests.json
\`\`\`

**Validation boundaries**: Only the new J34 source and test files are byte-identical to the locally executed files at their cited Git blobs. The J31/J32 original source primitives loaded in local J34 were a source-equivalent copy of their mathematical functions; this is **not** a claim of running the entire latest upstream dependency byte-for-byte. The full J33 receipt digest and original source identities are checked at J34 ingress.

## Actual 69 original equations — no synthetic replacement

Let \(\Phi_k(x;t_k,t_{k+1})\) denote the physical smooth-mode flow for the original modes \(k=0,\ldots,6\), with original source forcing and nonlinear capacitor. The **independent original multiple-shooting unknowns** are

\[
z=(x_0,y_1,\ldots,y_6,t_1,\ldots,t_6)\in\mathbb R^{9+54+6}=\mathbb R^{69},
\qquad t_0=0,\quad t_7=\tau=20\pi/11.
\]

The residual has **54 distinct signed interface matches**, **nine original period-return components**, and **six physical source guard-zero equations**:

\[
h_k(z)=y_{k+1}-\Phi_k(y_k;t_k,t_{k+1})\in\mathbb R^9 \quad(k=0,\ldots,5),
\]
\[
r_\tau(z)=\Phi_6(y_6;t_6,\tau)-x_0\in\mathbb R^9,
\qquad g_k(z)=g_k(y_{k+1})=0 \quad(k=0,\ldots,5).
\]

Do not replace the original physical event guard by an independently timed numerical label. The exact Jacobian structure for every physical mode requires the **same-source and same-clock** derivatives:
\[
D_{y_k}h_k=-D_x\Phi_k,\quad D_{y_{k+1}}h_k=I_9,
\quad \partial_{t_k}h_k=+D_x\Phi_k\,f_k(t_k,y_k),\quad
\partial_{t_{k+1}}h_k=-f_k(t_{k+1},\Phi_k).
\]
For the return, \(D_{y_6}r_\tau=D_x\Phi_6,\;D_{x_0}r_\tau=-I_9,\;\partial_{t_6}r_\tau=-D_x\Phi_6 f_6\).
Every \(g_k\) is **exactly affine** in the original nine source coordinates, so its row \(Dg_k\) is a signed source-true integer normal in the original \(y_{k+1}\) block, with no time derivative. These signs and indices agree with the existing original [J31 69D/15D numerical source owner](../../scripts/check_smith_filsinger_j31_source_15d_69d_shooting_20261124.py) and [exact 54+15 Schur preconditioner](../../scripts/check_smith_filsinger_j31_projective_sparse_preconditioner_20261124.py), and they are **not** an alternative synthetic 69D theorem.

## Concrete common nonzero candidate domain

The current 69D centre uses the **original J23/J24** rational nine-state centres \(x_0,y_1,\ldots,y_6\), the six actual physical J29/J30 nominal source clocks, and the original fixed \(t_0=0\). Its box has independent **source-labelled spatial halfwidth \(10^{-6}\)** in all 63 state coordinates, event times \(t_1,\ldots,t_5\) with halfwidth \(5\times10^{-6}\), and the genuine wide original sixth event \(t_6\pm2\times10^{-4}\). It includes **all six originally certified rational J29/J30 root-time brackets**, and the first-leg \((x_0,t_1)\) projection lies inside the complete J33 source-proof input box. All six original affine guard intervals contain zero.

This is a mathematically explicit **candidate** common nonzero box, **NOT** a jointly source-admitted domain for the other six flow operators yet. The prior J33 source terminal enclosure retains independent time uncertainty; it is never identified with the exact original \(y_1\) event state merely by interval overlap.

### 15/69 original exact source rows now genuinely supplied

- **Rows 0–8**: original signed \(h_0=y_1-\Phi_0(x_0;0,t_1)\), with outward rational F interval, \(-[D_x\Phi_0]\) on original \(x_0\), \(I_9\) on original \(y_1\), \(-[\partial_{t_1}\Phi_0]\) on original actual \(t_1\); all remaining columns are *exact zero*. These are directly read from the pinned **J33 full** source-validated ninth-state output and 9×9 tangent, not from the numerical approximate fundamental matrix.
- **Rows 63–68**: all six original physical affine guard values \(g_k\) and their **full exact** 69-component Jacobian rows, evaluated on the same source-labelled \(y_{k+1}\) box. All six pre-switch source-field slopes are strictly of the originally required sign at their same physical event-clock boxes:

| Original guard | Strict outward source-slope range (decimal display only) |
|---|---|
| V ON | [0.45490586, 0.45491713] |
| spark OFF | [-0.09206334, -0.09200892] |
| spark ON | [0.14771431, 0.14776566] |
| U ON | [0.99273799, 0.99283149] |
| V OFF | [-0.44379573, -0.44361353] |
| U OFF | [-0.14941416, -0.14930499] |

The **machine code**, rather than the rounded table, uses exact fraction intervals. Strict slope signs are **local transversality** statements conditional on a source state being in that box, not solutions of the guard equations.

**Rows 9–62 remain literal UNKNOWN source F and DF intervals: 54 missing, not 54 zeros.** Their original owners, each requiring nine full source F, nine-by-nine \([D_x\Phi]\), both independently variable absolute-time derivative vectors, and source box inclusion, are:

| Rows | Source flow needed | Existing conditional smooth-mode source owner |
|---|---|---|
| 9–17 | event1→event2 | J31 64-slab PB8 |
| 18–26 | event2→event3 | J31 4-slab PB12 |
| 27–35 | event3→event4 | J32 128-slab Taylor/PB6 |
| 36–44 | event4→event5 | J31 32-slab PB8 |
| 45–53 | event5→event6 | J32 128-slab Taylor/PB6 |
| 54–62 | event6→exact \(\tau\) return | J32 128-slab PB6 and **source-hashed broad sixth-state input** |

Live repository audit confirms the **committed compact receipts do not contain all required source interval arrays**. They establish conditional segment progress but cannot be parsed as a joint original 69D \([DF(B)]\) without re-emitting those actual arrays and validating each input box against the **same** original \(B_{69}\). The broad, source-generated sixth-event input **is not** the unpaid narrow J24 sixth state-box proof.

## Source-specific numerical diagnostic, independent and non-authoritative

Using independent numerical integration of the **original nine-state equations and original seven modes** (SciPy DOP853) and a separate analytical source tangent:
- **630/630** original rational f/fJ scalar and Jacobian spot comparisons match within floating-roundoff excess \(\le3.56\times10^{-15}\).
- Full numerical **69×69** multiple-shooting Jacobian has **748 nonzero entries**.
- Eliminating the original exact-identity 54×54 unit-lower matching block yields the same-source scheduled 15D Schur Jacobian with \(\ell_\infty\) discrepancy **\(5.2832\times10^{-15}\)**.
- The 15D numerical \(\ell_\infty\) condition number is around **141.3**; actual source nominal centre 69D residual is around **\(3.4950\times10^{-11}\)**, with numerical full-period return centre defect \(1.921\times10^{-12}\).
- A deliberately reversed physical *start-clock* derivative sign makes the same-source 15D Schur comparison fail. This is the source-equivalent negative control of #1547's same-clock forensic discipline.

**None** of these NumPy/SciPy comparisons is a strict outward interval result. In particular, a numerically close Newton centre does not establish a periodic orbit, and 15D good conditioning does not imply the source 69D interval matrix is contraction-ready.

## The one next P0 big cut and strict promotion firewall

1. Make each of the six existing *original* conditional smooth-mode producer scripts emit a **source-hashed, whole-interval, full F/[DΦ]/two-clock derivative JSON**, with input-state/time box geometry preserved. Check the original J24 and alternative broad sixth-state ingress in both directions, never promoting numerical overlap to exact event identity.
2. Produce rows 9–62 of original \(F_{69}(z_0)\) and \([DF_{69}(B)]\) from those six *same-source* flow records. Verify the 54×54 exact lower-triangular Schur identity and all 69 equations **as one source joint ball**, not independent events copied as if matched.
3. Tighten the event3→4 and J33 interval tangents if the [classical interval Krawczyk method](https://na.math.kit.edu/alefeld/download/2000_Interval_analysis_theory_and_applications.pdf) requires it, and then use the existing exact rational 15D-Schur/69D preconditioner to establish **69 strictly inward row slacks and uniqueness**.

**Mathematical acceptance today**: 7/7 complete *conditional* original smooth source segment calculations remain prior verified evidence; **15/69** source F+DF rows are directly assembled on the candidate common box; **0/69 global Krawczyk rows** proved. Six physical zero guards, 54 original signed matches and nine returns have **not** been jointly solved. No Agda/Lean kernel, GitHub CI, physical Filsinger apparatus, environmental energy metrology or 100%-energy theorem.
