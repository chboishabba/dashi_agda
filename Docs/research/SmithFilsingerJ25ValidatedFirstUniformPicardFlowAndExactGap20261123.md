# J25 — first genuine outward-rounded 9-state flow tube; five-parameter-uniform guard exclusion

**23 November 2026 | PR #1537 (still separate from master) | source-only J18/J23 nine-state conditional mathematical receiver.** Original Smith/Filsinger/DASHI source ownership retained. The result below is an exact interval **local initial-value flow** theorem, not a proof of a periodic orbit or physical environmental energy transfer.

## Closure of J24 byte-replay gate

The GitHub J24 rational checker was reconstructed exactly from source SHA **aca23be82c5f6e742af4abeb00925594026f589a**, together with its original event-centre JSON SHA **edcec489212e81b473af5ea1049b958236781d12**. Both locally computed Git blob hashes match GitHub, and the checker executed successfully: **6/6 PASS exact rational conditional event-box slopes**, minimum conditional lower bound 0.0893154105253641. As before, this is conditional on inclusion in the six remote event boxes.

## New unconditional local IVP result

The [J25 committed and byte-executed checker](../../scripts/check_smith_filsinger_j25_first_segment_validated_interval_20261123.py), Git blob **5d723374d71281cc5583582cc17d15016deaa8a3**, independently transcribes the **original nine-state J18 differential equations** in source-only mode and constructs actual directed-rounding interval enclosures without SciPy tolerance assumptions. Its coefficients use exact rationals; the prescribed matched wave quadratures use rational alternating Taylor remainders and exact monotonic-angle checks, and the `sqrt(2 gamma_rad)` amplitude uses an integer square-root enclosure.

The numerical J23 corrected two-switch root is represented as nine **exact decimal rational** centre coordinates (a *chosen* initial state, **not** a certified periodic fixed point). For **every** initial state in its nine-dimensional sup-norm box of radius `1e-7`, with initial spark mode **ON**, and for every time in the **entire interval** `0 <= t <= 1/11`, the exact Picard integral operator maps a computed nine-dimensional tube into itself. All interval operations are exact integer arithmetic on a `10^30` directed grid.

A uniform derivative bound on this tube yields a Jacobian row-sum infinity norm strictly below **44**. Consequently on each of the four subintervals of length `1/44` the Picard integral map is contractive. Together with global tube self-inclusion, this proves a unique classical solution on the entire initial interval for the prescribed initial value, without assuming a numerical ODE solver's error estimate.

### 5-parameter uniform result — not sampled corners

The **same proof runs** for the full rectangular product of J23's wide ranges (not merely 32 corners):

| Parameter | Exact input interval |
|---|---|
| gamma_rad | [0.0149,0.0151] |
| gamma_internal | [0.00015,0.00025] |
| k | [0.3495,0.3505] |
| kh | [1.9995,2.0005] |
| Gload | [0.5195,0.5205] |

The incident forcing remains source amplitude 1.2, phase 0.3, handedness -1; no controller driver. The other finite copper, coil/gap, capacitor, bleed and diode parameters are unchanged. Reproducing **both** nominal and uniform-box calculations from the committed checker passes.

| Interval fact through t=1/11 | Nominal | Uniform five-parameter box |
|---|---:|---:|
| Picard inclusion | PASS | PASS |
| Rational tube inflation iterations | 11 | 11 |
| Upper bound on diode U guard u-b-Vd | -0.0654266049 | -0.0637512799 |
| Upper bound on diode V guard v-b-Vd | -0.9385986789 | -0.9373476262 |
| Lower bound on spark-OFF guard b-Voff | +2.1946368295 | +2.1941813183 |
| Outward bound on state Jacobian infinity norm | 27.6000000001 | 27.6033333334 |
| Subinterval Picard contraction | < 27.601/44 < 1 | < 27.604/44 < 1 |

Negative diode guards prove **both diode currents identically zero** during the entire verified initial segment; the ON spark's bank voltage cannot reach the OFF threshold, hence there is **no spark event**. No diode/spark switching occurs on this segment, and denominator `Ch(1+3 alpha x^2)` is uniformly positive.

The machine-readable [J25 acceptance](../../Artifacts/smith-filsinger/j25_validated_uniform_initial_picard_tube_20261123.json) references the exact source hash. The locally emitted receipt contains the raw integer-grid numerator bounds for **all nine tube radii, every Picard self-inclusion slack, three guard intervals and the Jacobian row sums**, rather than relying on rounded displays.

## Scope and next exact geometry

This is the first actual **validated original-equation initial segment**, not a numerical inference from event counts. The interval `1/11 = 0.090909...` spans only **1/((20pi/11)*11) = 1/(20pi)** of one fundamental source period (approximately 1.5915%). The first observed diode V event lies near `t=3.389367`, well outside the certified segment. Therefore the J24 six-event locations, signed crossing margins and saltation determinants are still CONDITIONAL on yet-unproved trajectory entry into their rational boxes.

**J26 next task:** suppress interval wrapping through validated Taylor-model/Lohner (centred polynomial) integration and event isolation over the remaining interval `[1/11,20pi/11]`, including four diode guard roots, two spark roots and every intermediate guard exclusion. Then compute interval `P_tau(x0)`, interval `DP_tau(B)`, the exact centre defect and a Krawczyk/Banach self-map for a nonzero nine-state box. The earlier rational contraction budget is NOT itself a proved orbit existence certificate. The five-parameter periodic-orbit theorem is a further distinct uniform-Banach obligation after the centre case.

Original physical Filsinger netlist/terminal/source measurements, Duga/HAARP/SURA-to-device transfer, useful-work calibration and any antigravity response remain **unverified**. The mathematical finite-coil-loss obstruction to 100% environmental-to-HF-load remains unchanged. No GitHub Actions/CI or Agda kernel run.
