# J26 — validated nominal first diode V crossing and direct J24 event-box weld

**23 November 2026 | existing PR #1537 against `master`.** This is the original J18/J25 synthetic nine-state source-only receiver with driver OFF and finite ohmic losses. The source remains externally prescribed, not an identified naturally available field or a measured Filsinger generator. Original Smith/Filsinger attribution retained. No GitHub CI/Agda kernel was used.

## Source-first execution and exact status

The new [J26 first-event proof checker](../../scripts/check_smith_filsinger_j26_first_diode_validated_taylor_20261123.py) depends on the [original J25 exact 10^30-grid interval primitive](../../scripts/check_smith_filsinger_j25_first_segment_validated_interval_20261123.py), reads J24's original event-centre data, and independently reuses the original J18 source-only physical equations without replacing the owners.

The **locally executed checker and GitHub committed blob match byte-for-byte**, SHA **78cfdaa6c473eb1712194a17fa5ee46fa9dd5a94**. The full 37-step interval ledger, exact rational residual/majorant witnesses and J24 nine-state event box receipt were emitted locally. A portable standalone replay packet accompanies this work; the concise [machine receipt](../../Artifacts/smith-filsinger/j26_nominal_first_diode_validated_2ns_bracket_20261123.json) is committed. The filename's shorthand “2ns” means a width of **2×10^-9 dimensionless model-time units; it is NOT a nanosecond hardware measurement**.

**Trust boundary:** The nine-state differential equations are transcribed into the exact interval consumer; the original native J18 source Python is not byte-executed as part of the J26 proof checker. The source-owned J25 primitive and the new J26 consumer *are* byte-identical and locally executed. The initial state is the nine exact decimal rational coordinates from the corrected J23 **numerical** seed, not a proven periodic fixed point. This proves a trajectory from that fixed rational initial condition only. Unlike J25's short interval result, the new long J26 continuation does not currently establish the full wider five-parameter rectangle.

## Wrapping-controlled proof method

The proof uses *52nd-order* forward Taylor polynomials anchored at exact rational segment-start states, with rigorous interval recurrence for all nine original variables. The nonlinear HF capacitor is preserved exactly through the polynomial identity

    Ch * (1+3 alpha x^2) * x' = ih-Gload*x,
    alpha = 1/2, hence denominator 1 + 1.5 x^2.

Taylor wave inputs use exact rational Maclaurin evaluations at the start phase `0.3+1.1*t0`, factorial-remainder bounds valid at all used rational angles, and rational recurrence for the local source sine/cosine coefficients. The source amplitude tail is bounded above by the **correct conservative** rational factor 0.21 > 1.2 sqrt(0.03). All state parameters and the two-dimensional source quadrature are preserved.

The computed interval Taylor coefficients define an enclosure for a true representative polynomial with full nonlinear derivative defect bounded on `[0,h]` by the exact positive vector `epsilon`. The coefficient recurrence is not blindly trusted as an ODE solution: the residual polynomial is explicitly recomputed, and the capacitor equation's *denominator-cleared* residual is divided by a strictly positive denominator.

For each step, build a polynomial-based interval tube around the anchored polynomial and derive an entrywise nonnegative matrix majorant A of the actual nine-by-nine state Jacobian throughout this tube. The componentwise comparison inequality follows from Lipschitz mean value and the nonnegative exponential series:

    |e(t)| <= exp(A*t)*(delta_start+t*epsilon),  0 <= t <= h.

The interval checker bounds the RHS **by exact rational arithmetic**, using 90 positive matrix-power Taylor terms and a proven geometric tail from `||A||_infinity`. It asserts every error component is strictly inside the chosen radius R on every segment. The endpoint is then enclosed and re-centred to 23 exact decimal places; the complete rounding loss is included in the next step's input `delta_start`. This prevents the uncentred entire-state interval wrapping which blocked extension of J25.

The proof is thus a genuine, finite, interval-a-posteriori, *initial-value solution* bound. The numeric Taylor centre determines the certificate candidate; it is **not used as a floating-point error budget**.

## Strictly proved first-event itinerary on the nominal point

The accepted pre-event trajectory comprises 33 intervals of length **1/10** and four intervals of length **1/50**, with last endpoint

    33*(1/10)+4*(1/50)=3.38.

**All 37** segments pass full nine-state error enclosure and prove simultaneously:

- diode U guard `u-b-Vd<0`;
- diode V guard `v-b-Vd<0`;
- spark remains in ON mode because `b-Voff>0`.

The largest propagated nine-state error bound at t=3.38 is approximately **5.708052×10^-10**. This is the nominal rational-seed error bound, not an error estimate for a five-dimensional parameter box.

Continue the *mathematical inactive-diode vector field* temporarily from 3.38 past the anticipated diode activation. Two exact rational endpoint integrations certify:

| t | full outward interval for V guard (approximate display only) |
|---|---|
| 3.389367008 | **[-6.5159741×10^-10, -1.6093967×10^-10]** |
| 3.389367010 | **[+2.5822557×10^-10, +7.4888332×10^-10]** |

The signed derivative throughout the entire bracketing interval is at least **0.426247788744** and at most **0.490842212744**; diode-U remains negative and spark-OFF guard remains strictly positive. Because the guard is continuous, has opposite endpoint signs, and has strictly positive derivative on the bracket, a **single, unique first diode-V forward-activation time** exists:

    3.389367008 < t_V < 3.389367010.

The width is **2×10^-9 model-time units**, not SI nanoseconds. The inactive-field extrapolation is only a smooth mathematical extension for locating this root; it **does not constitute a validated physical diode-ON trajectory after the switch**. At the guard the diode constitutive current is continuous with value zero; its Jacobian changes across the event.

## Original J24 first event-state box: 9/9 included

After enclosing the event time, the checker evaluates all nine Taylor state coordinates for the **entire uncertain root interval** `t in (3.389367008,3.389367010)` and adds the rigorous propagated error vector. It reads the original J24 [six-event centre file](../../Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json) with exact Fraction parsing, then asserts the true event-state interval is contained in the first J24 componentwise rational box of radius **10^-4**, in all **nine of nine coordinates**.

This **pays the missing flow-inclusion hypothesis for the first J24 diode-V box**, and its conditional positive diode slope can now be applied to the actual trajectory starting at the chosen rational seed. It does **not** pay the remaining five J24 event boxes.

## Exact remaining J27 maximum-cut

The next welding point is the *actual diode-V-active vector field* immediately after the isolated event, with an interval uncertain event time and state. Preserve the fact that the diode current is zero and vector field continuous at activation but the Jacobian changes. Avoid replacing event-time uncertainty by a single numerical time. Continue verified flow until the spark-OFF boundary near **t=3.4912927**, carrying exact event time/state and enforcing the OFF threshold with an interval saltation denominator. Then spark ON, two remaining diode off/on transitions, and the full `tau=20*pi/11` return-map and derivative enclosures must be certified before Newton/Krawczyk fixed-point inclusion.

J26 does **not** prove that the selected rational J23 initial point is periodic, nor a finite state/parameter box of nearby periodic orbits; it does not prove original naturally available RF power, Filsinger hardware efficiency or any gravitational field mechanism. The J21 finite-loss exact upper bound continues to prohibit 100% environmental-to-load efficiency in this model with positive resistance.
