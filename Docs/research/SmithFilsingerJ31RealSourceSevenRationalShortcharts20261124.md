# Filsinger J31 — seven original-source rational microchart tubes, tangent enclosures and spark turnaround

**24 November 2026 · PR #1537 · Smith/Filsinger-attributed prescribed-wave finite-loss nine-state model.** The new proof producer is [the executable source interval kernel](../../scripts/check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124.py), with [machine acceptance receipt](../../Artifacts/smith-filsinger/j31_native_seven_shortcharts_rational_picard_20261124.json). The executed local Python bytes match GitHub blob **47493fbefba44c20e7cb82e31521627f13611800**. No CI, Agda kernel, measured original environmental wave or physical receiver is claimed. **The original 69D Krawczyk theorem remains OPEN.**

## Actual original nine-state finite-loss smooth vector fields

The state is \(x=(i,j,u,v,b,q,r,i_h,c)\). The smooth mode is \(m=(U,V,\chi)\in\{0,1\}^3\), where diode U/V and spark are separately indexed. Let \(j_u=U(u-b-0.1)/0.12\), \(j_v=V(v-b-0.1)/0.12\), \(a=-0.35i\), and \(d=u-v-0.28j\). The nine original source equations are:
\[
\begin{aligned}
\dot i&=(1.5a-0.6d)/2.64,&\dot j&=(-0.6a+2d)/2.64,\\
\dot u&=[1.55(-j-j_u+0.35q+2i_h)+(j-j_v)]/1.17,\\
\dot v&=[-j-j_u+0.35q+2i_h+1.4(j-j_v)]/1.17,\\
\dot b&=(j_u+j_v-0.018b-\chi i_h)/0.65,\\
\dot q&=1.1r-0.0152q-0.175u+(3\sqrt3/25)\cos(0.3+1.1t),\\
\dot r&=-1.1q-0.0152r-(3\sqrt3/25)\sin(0.3+1.1t),\\
\dot i_h&=[\chi b-c-(0.05+0.09\chi)i_h-2u]/0.15,\\
\dot c&=(i_h-0.52c)/[0.12(1+1.5c^2)].
\end{aligned}
\]
These retain all physical synthetic circuit components, original source quadratures, real nonlinear capacitor and real diode positive-part *branch boundaries*. The smooth extensions are prescribed independently and require actual guard signs to be physically admissible. The exact original seven-mode itinerary used by the executed source kernel is \((0,0,1),(0,1,1),(0,1,0),(0,1,1),(1,1,1),(1,0,1),(0,0,1)\).

All source coefficient and J24-centre literals are exact rational input; interval endpoints are rounded outward to lattice \(10^{-30}\). The source \(\sqrt3\) is enclosed by integer isqrt. Trigonometric source values use 37 rational sine/cosine Taylor terms with explicit geometric absolute remainder and the rigorous bound \(|\sin'|,|\cos'|\le1\) over a rational time interval. Forward dual interval differentiation computes the full real source \(9\times9\) Jacobian, including the nonlinear cap denominator.

## Mathematical validity of the local proof

For each exact-rational input box \(X_0\), start-time interval \(T_0\), physical smooth mode \(m\), duration \(h>0\), and spatial tube \(X\), the code establishes
\[
X_0+[0,h]f_m(T_0+[0,h],X)\subset\operatorname{int}X,\qquad
q=h\max_i\sum_j\sup|J_{m,ij}(X)|<1.
\]
The strict first inclusion and Picard contraction give existence/uniqueness and a *whole-time* tube for all starts in the nonzero input box. Independently, exact integral Taylor acceleration \(\partial_t f+Jf\) proves a second-order 9D endpoint inclusion. For the time-ordered tangent flow, the Peano–Baker expansion gives
\[
D_x\Phi_m\in I+hJ_m(X)+[-e,e]^{9\times9},
\qquad e=q^2/(1-q).
\]
That remainder is a safe positive series bound for \(q<1\), not an empirical ODE solver tolerance. Finally \(\partial_{t_1}\Phi=f_m(t_1,\Phi)\) and \(\partial_{t_0}\Phi=-D_x\Phi\,f_m(t_0,x_0)\) are enclosed on **independent start/end clock rectangles** for **exactly five** nondegenerate shortcharts 1–5; chart 0 has its two original source-clock endpoints fixed at 0 and 1/8192. Their input clock boxes imply the strictly positive elapsed-time interval ([h-2delta_t,h+2delta_t]); Picard and Peano–Baker use its upper endpoint for all-time validity, and each derivative uses the full duration interval. Shortchart 6 is certified only on the **correlated fixed-duration** slice (t_1=t_0+h), because the sixth event input-time uncertainty exceeds the current short step. The complete independently timed 69D whole-segment Jacobian is still OPEN.

For the **physical mode** check, every guard other than the one just switching has strict sign over the entire Picard tube, including the opposing hysteresis spark threshold. For the newly switched diode, the signed post-switch derivative forces physical positive-part branch admissibility at positive local times **provided the true state at the switching instant satisfies its exact guard zero**. The receipt retains that conditional rather than asserting all members of a rectangular seed box themselves satisfy the event guard.

## Seven source-specific enclosures (not full seven segments)

Each input state box has original J24-centre halfwidth \(10^{-4}\); its spatial Picard tube has halfwidth \(10^{-3}\). The source-owned J26–J29 first-five exact event root brackets and J30 sixth exact rational root bracket are individually checked to lie inside the new input clock boxes: halfwidth \(1/200000\) for events 1–5, \(1/5000\) for event 6, and clock \(t_0=0\) for chart 0. The exact previous J29 machine receipt proves **five of six original J24 event-state boxes**; the new geometric input state box coincides with each J24 centre's \(\pm10^{-4}\) original box; it does not shrink the upstream state uncertainty. **The sixth full state box is still OPEN**, even though its exact root time lies in its new time box.

| Chart | Original smooth mode (U,V,spark) | Accepted exact duration \(h\) | Upper rational \(q\) |
|---:|---|---|---:|
| 0 | (0,0,ON) | \(1/8192\) | 0.003369141 |
| 1 | (0,1,ON) | \(1/16384\) | 0.001960571 |
| 2 | (0,1,OFF) | \(1/16384\) | 0.001823382 |
| 3 | (0,1,ON) | \(1/16384\) | 0.001960571 |
| 4 | (1,1,ON) | \(1/8192\) | 0.006979679 |
| 5 | (1,0,ON) | \(1/8192\) | 0.003645141 |
| 6 | (0,0,ON) | \(1/16384\) | 0.001684571 |

All \(q\) and slope display bounds are **coarse rational outward upper/lower bounds** derived from the exact Fraction results, not 64-bit acceptance tests. Each source chart has: complete Picard tube PASS, second-order flow endpoint PASS, 81/81 variational entry enclosures PASS and time-derivative formulas PASS, with **five independent clock rectangles**, **one fixed-clock initial chart** and **one correlated fixed-duration final chart**. Both diode and spark *non-switching* guards are proved strict on the whole microtube. No chart is falsely expanded to its full segment.

## Correct six signed guard transitions and spark-turnaround theorem

The six named crossings have pre-switch slope signs \((+,-,+,+,-,-)\). Their *pre* and *post* uniform intervals, rounded outward to 6 decimal places for display, are:

| Named guard | Pre-switch slope | Post-switch slope |
|---|---|---|
| V diode ON | [0.449285,0.460538] | [0.403701,0.506122] |
| Spark OFF | [-0.119244,-0.064828] | **[0.183060,0.234399]** |
| Spark ON | [0.122071,0.173409] | **[-0.153879,-0.099464]** |
| U diode ON | [0.946039,1.039530] | [0.898319,1.087251] |
| V diode OFF | [-0.534801,-0.352608] | [-0.489217,-0.398192] |
| U diode OFF | [-0.203940,-0.094779] | [-0.156219,-0.142500] |

**The original spark switches REVERSE bank-voltage slope after transition.** Off crossing is descending before the switch but rising afterward; on crossing is rising before the switch but descending afterward. This is consistent with hysteretic rebound and the original \(-\chi i_h\) term. The Schur/event-time determinant must use the **pre-switch** slope, not the post one; a same-signed pre/post requirement would be wrong. For the first five guards this is attached to the existing J29 exact J24 full state boxes and exact crossing brackets by interval inclusion. For the sixth guard it is an independent real-source **local** interval test around the J24 numerical centre and actual root-time range, without the unpaid sixth original state-box admission.

## Executed source, machine reproducibility and exact remaining proof

The committed script was locally executed with Python Fraction and no CI, producing the full 146409-byte exact rational 9×9/timing receipt (SHA256 **6694e27910564f63dae5736fa06fc440a5671d9774acf74422b24d86ab4e11ef**); the smaller committed [machine receipt](../../Artifacts/smith-filsinger/j31_native_seven_shortcharts_rational_picard_20261124.json) pins the full deterministic replay and source blobs. No local-file handoff is requested: on the repository checkout, invoke the committed script with the --out argument to reproduce the full exact JSON.

**Still OPEN:** Carry the full time-indexed seven source segments using high-order Taylor/Lohner or correlated affine-noise transport rather than treating wide local interval output boxes as independently recentered centres; admit the sixth actual event interface state or prove an alternative source-admissible 69D domain; complete independently variable start/end timing across the sixth event and all complete seven-segment 69D Jacobian entries; establish all 69 strict outward-rational Krawczyk slacks and uniqueness. Then and only then claim an exact \(\tau=20\pi/11\) orbit. The original physical Filsinger pin/energy/source metrology, five-parameter family and original hardware 100% energy claim remain separate unproved gates.

This proof carries a typed source zero guard, signed pre/post residuals, physical event time, chart refinement and full interface matching separately; it does not treat a local certificate as global endpoint equality. See [J31 69D projective Schur owner](SmithFilsingerJ31P0ProjectiveSparseResidualConeCrossPR20261124.md) and [authoritative live roadmap](../roadmaps/FilsingerP0SixGuardExactStatusAndJ31ShootingCut20261124.md).
