# J24 — six-guard hybrid source-period audit and exact rational Newton obligations

**23 November 2026 | PR #1537 | source-only J18–J23 nine-state synthetic receiver.** This work reuses the original Smith/Filsinger-provenance source graph; no new original hardware netlist, measured naturally incident Poynting flux, environmental-power or gravitational claim. Production exact periodic-orbit certificate is **NOT complete**.

## Repository branch reconciliation before the cut

GitHub repository default is **master**. PR #1537 was verified **open, not merged**; the J23 native checker was not found on master even though other programmes have merged. Existing J18–J23 native owner dependencies thus remain on branch `research/sheldrake-field-filsinger-levin-consolidation-20261121`. Work is attached to that existing PR; a master-native claim would be false.

The J23 *independent local* numerical archive was available, but the container could not reach raw GitHub directly. Exact committed-byte native J18–J23 execution remains a distinct OPEN gate. Exact rational J24 calculations below were executed **locally** in the attached independent scripts, not by GitHub CI.

## Stronger original switched geometry: 6 distinct guards in one wave period

J23's 2 spark events are NOT the entire differentiable segmentation. With omega=11/10 and tau=20*pi/11, the independent J18-equation integration of its corrected numerical orbit gave (all model-time units; approximate event centres):

| t | crossing type | direction-corrected slope, numerically |
|---:|---|---:|
| 3.389367008882 | V diode becomes forward active | +0.454910 |
| 3.491292721185 | spark ON → OFF at bank Voff=0.0018 | +0.0920361 |
| 3.515340479137 | spark OFF → ON at bank Von=0.0060 | +0.147740 |
| 4.275489023213 | U diode becomes forward active | +0.992780 |
| 4.323837947628 | V diode deactivates | +0.443724 |
| 4.928751406857 | U diode deactivates | +0.149377 |

Native diode guard functions are g_U=u-b-Vd, g_V=v-b-Vd, each with current j=max(g,0)/Rd and Vd=0.1. Spark threshold guard is b-Voff if ON, b-Von if OFF. The full one-period itinerary, including the initial and final spark-ON mode, is therefore: **U/V diode inactive → V active → spark OFF → spark ON → U activates → V deactivates → U deactivates → return**. At diode boundaries the vector field is continuous (j=0 from both sides) and its **saltation matrix is the identity**, but its *Jacobian* changes; validated variational flow must split at those roots. At spark boundaries the vector field itself jumps and requires full saltation.

## New exact rational local six-guard gate

The local checker `check_smith_filsinger_j24_rational_six_guard_newton_budget_20261123.py` uses exact Python Fraction interval operations (not binary-float inequality arithmetic), on **specified rational** nine-state centre boxes at the six independently computed event centres. Each state component has half-width **1/10000**, and k and kh range over [0.3495,0.3505] and [1.9995,2.0005]. The other wider J23 parameters do not enter these bank and diode guard derivatives at a fixed state. It recomputes capacitor-matrix inverse and diode max guards exactly, with no division by intervals containing zero.

The six corresponding direction-corrected derivative interval bounds, conditional on true state inclusion, are:

| guard | lower | upper |
|---|---:|---:|
| V diode activates | 0.449123956 | 0.456140625 |
| spark OFF | 0.089315411 | 0.094756846 |
| spark ON | 0.145173115 | 0.150306858 |
| U diode activates | 0.979129603 | 1.001667792 |
| V diode deactivates | 0.436288577 | 0.455679090 |
| U diode deactivates | 0.142637782 | 0.160853447 |

All six exact rational lower bounds are positive: **6/6 conditional local guards PASS**, minimum >0.0893154. These are not proved global crossing margins because the *exact flow's inclusion in the six boxes is NOT yet validated*. Outside these local boxes additional crossings or sign changes are not excluded.

### Exact spark saltation geometry

Let chi change by delta=chi_after-chi_before. In native equations, only the capacitor-bank and HF inductor derivative jumps:

    Delta f_b = -delta i_h / C_b,
    Delta f_{i_h} = delta (b - R_gap i_h) / L_h.

Thus the spark saltation matrix has rank-one correction S=I+Delta f e_b^T/f_b^pre, and the determinant identity is

    det S = f_b^post / f_b^pre.

The J24 exact rational boxes imply determinant intervals approximately **[-2.365731,-2.175700]** for OFF and **[-0.891294,-0.824650]** for ON: both nonsingular and orientation reversing. The two-spark product is orientation preserving at the determinant-sign level, but this does not by itself establish return-map stability.

## Exact rational Newton-budget algebra: a conditional proof interface, not an orbit proof

For one tau-return map P_tau on the *given two-spark, four-diode itinerary*, define H(x)=P_tau(x)-x. Let A0 be a 12-decimal rationalization of the *numerically computed* I-DP_tau(x0), and C a 12-decimal rationalization of its numerical inverse. All stated matrix computations below were repeated **exactly in rationals**:

    ||I-C A0||_infinity = 1.5860226906196e-11 approximately
    ||C||_infinity      = 11.731499450011 approximately.

Choose a hypothetical closed sup-norm state ball radius r=1e-7. If a **future outward-rounded, proven** full-hybrid interval integration established BOTH

    sup_B ||(I-DP_tau(x)) - A0||_infinity <= 0.001
    ||P_tau(x0)-x0||_infinity < 8.424059556455097e-9,

and proved the exact two-spark + four-diode itinerary on B, then the rational bounds would give

    q <= ||I-C A0|| + ||C|| * 0.001
      <= 0.011731499466 < 1,
    ||C H(x0)|| <= (1-q)r,

and the Banach self-map/contraction would establish a unique fixed point *inside B*. The budget is rather forgiving compared with a numerical 1e-12 shooting defect, but **SciPy tolerance is not a validated error bound** and no proof of either of the two ODE-derived premises currently exists. Neither the arbitrary radius nor the proposed 0.001 Jacobian error is declared a certified enclosure.

## Exact outstanding proof obligations for J25

1. Recover exact native J18–J24 source bytes and run source-pinned native regressions without Actions/CI; avoid claiming source-byte acceptance from an independent solver.
2. Build outward-rounded validated Taylor/Picard flow tubes on all seven smooth subsegments (6 interior guards), including diode guard isolation, no extra roots, and exact OFF/ON mode chronology.
3. Validate all six local event-state enclosures and both spark saltation denominator signs, then validate DP_tau(B) over a nonzero closed state ball.
4. Prove return-map defect and Jacobian budgets, self-map, q<1, and uniqueness using exact rational or outward-rounded interval bounds—not sampled corner extrema. Only then may P_T=P_tau^11 transport exact periodic existence to the J12 20*pi window.
5. For a five-parameter uniform certificate, *separately* propagate the interval bounds over the full parameter box. The earlier 32/32 corners remain finite tests only.
6. Original physical pin evidence 0/4; original measured energy roles 0/24. Keep synthetic energy and environmental source, HF delivery and gravitational claims separate.

**Execution/credit:** New local rational check PASS for the conditioned boxes and rational matrix budget only. No measured Filsinger hardware, source identification, superconducting/gravitational energy, global optimisation, or mathematically certified exact nonlinear periodic orbit.
