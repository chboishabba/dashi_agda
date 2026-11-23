# J28 — source-welded exact Picard continuation to third switching event

**23 November 2026 | PR #1537 | nominal synthetic nine-state J18 source-only model | no CI or Agda kernel.**

## Precise inherited premise

The existing J27 local exact-rational theorem validated the actual original-equation first diode-V activation and spark-ON→OFF crossing, and proved that **every admissible spark-OFF event state** lies in the original J24 radius-0.0001 nine-coordinate event box centred at

```
(0.13523459842601, -0.37755904088316, -0.57949133558498,
 0.11808477566022, 0.0018, -0.35976396951008,
 8.14678092946336, 0.19549754734332, 1.25957158565016).
```

J27's root-time enclosure is `3.49129269 < t_OFF < 3.49129275`. At the switch, the bank voltage is exactly `b=Voff=0.0018`, so the initial bank coordinate can be **intersected with that exact singleton**, rather than needlessly carrying the whole radius-0.0001 J24 bank range. The other eight coordinates conservatively retain their full J24 enclosures. This proof is **conditional on the already validated J27 event-state inclusion** and does not substitute the numerical J24 centre for an actual root state.

## True post-OFF mode and exact integration

Use the original J25/J27 nine-state field, with spark OFF, V diode still active, U diode inactive. In particular,

```
jV = (v - b - Vd)/Rd,  jU=0;
db/dt = (jV - Gbleed*b)/Cb;
dih/dt = (-x - Rcoil*ih - kh*u)/Lh;
```

and preserve the original coupled coil, U/V capacitors, source quadratures and nonlinear HF capacitor equation. The source clock remains **uncertain** over the inherited J27 time bracket; each 0.002 increment is an **exact elapsed duration**, not the width of the uncertain absolute clock interval.

The new [byte-identical executed checker](../../scripts/check_smith_filsinger_j28_third_spark_on_picard_20261123.py) uses directed integer-grid rational interval arithmetic with scale `10^22`, a directed integer square root for `sqrt(0.03)`, and a 22-term exact sine/cosine Taylor enclosure plus the global Lipschitz constant 1 for source-clock uncertainty. A self-inclusive interval Picard tube is constructed for **20/20 consecutive increments** of 0.002. All included tubes satisfy

- U diode guard strictly negative: maximum upper bound **-0.6803265198587240702001**.
- V diode guard strictly positive: minimum lower bound **+0.0101320778981963261549**.
- Bank derivative strictly positive: minimum lower bound **+0.1137925300465354631967**.

All three inequalities are conservative, source-uncertainty-aware, exact-grid inequalities, not sampled numerical slopes. The iterative inclusion converged within at most five iterations per step.

At elapsed `s=0.022`, exact outward-grid bank enclosure is

```
[0.0055556743507842829985, 0.0058305289839750970472]
```

entirely below `Von=0.006`. At `s=0.026`, the enclosure is

```
[0.0061124694402624566398, 0.0064572137280549112878]
```

entirely above `Von`. Since the bank derivative is strictly positive on the *entire virtual OFF-mode extension*, the trigger `b=Von` has exactly one crossing before any other diode changes, giving

```
3.51329269 < t_spark_ON < 3.51729275
```

in **dimensionless model time**. As in J26/J27, the OFF-mode equation is used virtually past the earliest possible threshold only to bracket the first root; the actual physical ON-mode flow after the root is **not** advanced by this proof.

## Actual-event spark saltation, independent of the J24 box width

The proven root occurs for elapsed time `0.022<s<0.026`. Hull the two self-inclusive Picard tubes intersecting this interval, then sharpen the bank coordinate to the **exact ON threshold** `b=Von=0.006`. On this whole actual-event enclosure, direct outward arithmetic gives

```
pre-switch bank slope:  [0.1430611029571664763050, 0.1530268714188615243284]
post-switch bank slope: [-0.1343215385828897080985, -0.1183978516917251962495]
saltation determinant:  [-0.9389102684543578790234, -0.7737062817395606533548]
```

The exact rank-one saltation determinant is the ratio `post_bank_slope/pre_bank_slope`; its entire certified interval is **strictly negative**, proving transverse, orientation-reversing ON switching at the **actual third event** of the J27-inherited nominal trajectory. Both physical modes are continuous in state but have different vector fields at the spark threshold; no artificial state reset is introduced. This independently validates the third event's signed saltation even though the original tiny J24 nine-coordinate centre box is **not** enclosed. No actual post-switch ON-mode ODE advance follows.

## Reproducibility and non-promotion

- Committed source Git blob: `8379d029d8ef37b08a5006eb60b71f98cc74ab57`, **byte-identical** to the locally executed Python source; run `python scripts/check_smith_filsinger_j28_third_spark_on_picard_20261123.py` to print all 20 interval witnesses.
- [Machine acceptance](../../Artifacts/smith-filsinger/j28_spark_on_picard_20261123.json): exact integer-grid inequalities and explicit proof boundaries.
- Original six-guard J24 itinerary: **3/6 unique event occurrences and their switching direction/transversality now flow-certified**, but only **2/6 full original J24 nine-coordinate event boxes paid**. The coarse 0.004 event-time bracket is not enough to promote the third event-state box.
- Source-typed original J18 full numerical script, Agda kernel, CI, independent Filsinger circuit pin graph, natural incident energy, full-period hybrid return map, rigorous periodic fixed point and uniform five-parameter orbit family are **not certified**.

**Next J28b big bite:** tighten the third event-state tube using the sharper actual J27 interval root-state enclosure (not just the coarse J24 box), prove 9/9 original J24 spark-ON event-box inclusion and signed spark-ON saltation; carry the physical event-time handoff into the subsequent U-on, V-off and U-off branches. Then weld the six-guard full `tau=20*pi/11` return map, derivative and rational Banach/Krawczyk fixed-point admission. Preserve independent original physical source and measured receiver obligations.
