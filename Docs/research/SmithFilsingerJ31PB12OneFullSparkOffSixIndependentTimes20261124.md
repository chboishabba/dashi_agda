# J31 P0 — 1/7 complete source smooth segments, six independent event clocks, and signed PB12/anisotropic proof geometry

*24 November 2026. Original attributed Smith/Filsinger nine-state finite-loss prescribed-wave source equations; [PR #1537](https://github.com/chboishabba/dashi_agda/pull/1537). Not a natural Schumann-energy measurement, hardware pin validation, periodic point, or unrestricted Maxwell computation.*

## Exact executed source and provenance

Two new **directly committed** executable owners:

1. [PB8 source-specific seven-mode proof](../../scripts/check_smith_filsinger_j31_pb8_anisotropic_six_time_20261124.py), Git blob **eb685d88e5fbfb8c33f17b676be7ce01baaeca7e**, with [exact machine receipt](../../Artifacts/smith-filsinger/j31_pb8_anisotropic_six_independent_times_20261124.json).
2. [Four-slab COMPLETE event2→event3 smooth spark-OFF source leg](../../scripts/check_smith_filsinger_j31_full_spark_off_four_slab_20261124.py), Git blob **f9e8ff2389655e45ca6ca2bc9a2e818167a4f442**, with [exact machine receipt](../../Artifacts/smith-filsinger/j31_full_spark_off_four_slab_source_20261124.json).

Both new executables were run **locally** against the original smooth source primitives and the committed executable blobs read back byte-for-byte. The local import of the earlier J31 source kernel was an older byte-version (cd1d8…) with the same source vector-field, Jacobian, phase, original centre and guard primitives; a fresh byte-identical run against the currently committed source-kernel **47493fbefba44c20e7cb82e31521627f13611800** was not performed. This boundary is recorded in receipts, rather than claiming a fabricated remote runtime. No GitHub CI, Agda/Lean kernel, merge, force push, or native physical apparatus test.

The exact full rational outputs (seven 9×9 local matrices and one complete segment matrix, derivatives and every slab) are deterministic and their SHA-256 hashes are pinned by the committed compact machine receipts. The new source scripts replay them with their required out-file argument from the repository, rather than requiring a separate local-file handoff.

## A. Six original event windows now have genuine independent start/end clocks

The prior seven original J31 microcharts were 5 genuine two-time rectangles + one fixed source-clock chart + one final correlated-duration chart. The last root-time bracket extends across about \(3.68\times10^{-4}\), larger than its old \(1/16384\) correlated step. Enlarging the last duration while keeping an *isotropic* radius produces a real obstruction: a uniform radius \(0.01\) admits the short source Picard trajectory but **fails** to certify a strictly negative pre-U-off guard slope. Thus an inclusion of the whole flow alone is NOT enough to pay the diode guard.

The new positive **anisotropic tube** at sixth U-off chart \(k=6\) uses original-source \(x=(i,j,u,v,b,q,r,i_h,c)\) halfwidths
\[
R_6=(0.0015,0.0015,0.0015,0.0015,0.0015,0.006,0.012,0.003,0.003).
\]
This retains narrow diode \(u,b\) guard coordinates while permitting the source quadrature \(r\) to move by a larger amount. Independent clock boxes:
\[
t_0\in t_6\pm 0.0002,\quad t_1\in(t_6+0.0005)\pm0.0002,
\quad \Delta t=t_1-t_0\in[1/10000,9/10000].
\]
The entire exact J30 sixth-root rational time bracket is contained in the \(t_0\) box. The nonzero original J24 state seed remains \(\pm10^{-4}\) around the *numerical sixth centre*, and is **NOT** yet attached to the actual nominal sixth root; original J24 6th state-box admission remains OPEN. This is a true mathematical *local source* theorem independent of the nominal global state identification.

**Executed 7/7 exact source Picard, 7/7 ordered PB8, 6/6 nondegenerate independent event-time rectangles** (k=1,…,6; initial k=0 both clocks fixed). Every old first-order 9×9 Peano–Baker interval contains the new eighth-order corresponding interval, for **all 81 entries per chart**. The isotropic sixth-guard negative control correctly fails the guard sign despite passing Picard. All six pre/post signed original diode/spark guard pairs and the earlier 5 J29 original full source J24 boxes remain geometrically supported, while source timing and state coordinates stay distinguished.

### Exact noncommuting PB bound

For a full-time common interval Jacobian \(J_m(X)\), nonzero independent duration \(H=[h_-,h_+]\), and \(\mathcal A=H J_m(X)\), the **ordered time-domain iterated integrals** are enclosed term-by-term in
\[
D_x\Phi_m(t_1,t_0,X_0)
\in I+\sum_{n=1}^{N}\mathcal A^{n}/n!+[-\eta_N,\eta_N]^{9\times9},
\]
\[
q=h_+\max_i\sum_j\sup |J_{ij}(X)|,\qquad
\eta_N=\frac{q^{N+1}}{(N+1)!\,[1-q/(N+2)]}.
\]
This does **not** assume \(J(t_1)J(t_2)=J(t_2)J(t_1)\); the common interval matrix product is an outward envelope of each chronologically ordered integrand. It is deliberately a safe enclosure, not the exact exponential of a constant matrix. Here \(N=8\) on each microchart; the full spark-OFF leg below uses \(N=12\) on each of its four slabs. Bounds use exact Python Fraction and outward \(10^{-30}\) rational grid arithmetic.

For the sixth microchart, \(q<0.024840001\), the PB8 omitted-tail radius is less than \(9.946754985\times10^{-21}\), versus the old PB1 conservative tail \(>0.0006\). **This compares truncation tails only**, not the entire interval matrix width or computational runtime. The signed and zero-mode event coordinates are preserved; no precision rescaling is silently identified with a source reparametrization.

## B. One genuine COMPLETE original smooth segment: spark OFF (event 2) to spark ON (event 3)

**This is more than a microchart.** For event times varying **independently**, \(t_2\in3.491292721190\pm 1/200000\) and \(t_3\in3.515340479143\pm1/200000\), the 9D start state covers the original J24 numerical event-2 box \(x_2\pm10^{-4}\), paid for the J23 nominal source by the prior exact J29 source receipt.

The *entire* original time span \(t_2\to t_3\) in mode \((U,V,\chi)=(0,1,0)\) is divided by three **fixed original physical rational clock** knots into four slabs, with no event/state labels discarded. This fixed-knot subdivision is an internal source-chart refinement \(k\), **not four new physical switch events**. Each full-time spatial tube \(X_i\) is constructed through a monotone exact-rational Picard majorant starting from its preceding interval endpoint box; no new centre is silently assumed exact. The endpoint follows the rigorous second-order source-integral Taylor inclusion, and the \(9\times9\) variational map follows exact PB12 interval matrices.

The actual four-stage result:

| Slab | Verified \(q\) upper bound | Lower bank slope \(\dot b\) | Verified diode guards | Spark admission |
|---|---:|---:|---|---|
| 0 | 0.154447123 | 0.178146 | U OFF, V ON | Entire tube below \(V_{\rm on}=0.006\) |
| 1 | 0.154318780 | 0.161567 | U OFF, V ON | Entire tube below \(V_{\rm on}\) |
| 2 | 0.154318780 | 0.147422 | U OFF, V ON | Entire tube below \(V_{\rm on}\) |
| 3 | 0.154447123 | 0.135356 | U OFF, V ON | For actual root with terminal guard \(b(t_3)-V_{\rm on}=0\), \(\dot b>0\) excludes an earlier crossing |

Each bound is a **strict outward rational integer comparison**, with exact \(10^{-9}\) or \(10^{-6}\) grid ceilings/floors in the machine receipt. Picard inclusion and source continuation pass **4/4 slabs**, the physical U/V guard signs pass **4/4**, and positive bank slope passes **4/4**. The first three spark-threshold upper bounds, in units \(10^{-6}\), are 3355, 4447, 5459, each strictly below 6000. On the final slab the tube alone allows \(b>0.006\), but strict \(\dot b>0\) **plus** the terminal guard equation ensures every actual matched root stays on the OFF branch until the physical ON event. The last guard-zero premise is an equation of the original 69D shooting system, **not paid by a fabricated full-box hypothesis**.

The proof composes the four time-ordered interval tangents
\[
D_x\Phi_{2\to3}
\in \mathcal P_3\mathcal P_2\mathcal P_1\mathcal P_0,
\]
with explicit outward matrix multiplication; order cannot be reversed. The absolute time derivatives retain
\[
\partial_{t_2}\Phi_{2\to3}=-D_x\Phi_{2\to3}\,f(t_2,x_2),
\qquad
\partial_{t_3}\Phi_{2\to3}=f(t_3,\Phi_{2\to3}).
\]
This produces **a source-valid complete smooth-mode map and full \(9\times9\) state/time derivative interval** over independent event times and nonzero input-state uncertainty, suitable as **one** original 69D matching-row producer.

Numerically displayed maximum resulting component widths: ~0.0030501 for the ordered full \(9\times9\) matrix, ~0.0005419 for the terminal 9D enclosure. All nine numerical event-3 centre coordinates are inside that terminal enclosure, but the **entire original ±\(10^{-4}\) event-3 J24 box is NOT**; do not claim the new endpoint supersedes J29's independently proved fifth original-state-box ledger. Most importantly, the source-normalized event-3 **terminal guard equality** and global simultaneous 69D shooting equations still require a strict enclosing root.

## C. Exact remaining theorem and roadmap

**New source segment counter: 1/7 full original smooth modes paid**, not 7/7. The remaining six original segments include the long \(0\to t_1\), the \(t_1\to t_2\) predecessor, spark ON \((t_3,t_4)\), both later diode segments, and the last \(t_6\to\tau=20\pi/11\). All six original *local* event clocks now have independently timed microchart enclosures, but this is not yet their complete smooth flow or guard-invariant full segment.

The single primary J31 mathematical cut remains producing the **full source 69×69 interval derivative \(DF(B_{69})\)** and \(F(z_0)\) on one nonzero rational state/time ball, with **54 original signed matching errors**, six original guard zeros and independent time labels retained. Apply the already committed 15D-to-69D Schur preconditioner and pay all **69 strict rational Krawczyk row-slack inequalities** plus the original physical guard chronology and uniqueness. Carry correlated high-order affine/Taylor/Lohner representations on the six longer segments rather than naive independent second-order wrapping; reuse exact source J29/J30 nominal checkpoints where source contracts permit.

**No** exact periodic orbit, full five-parameter family, hardware source/receiver metrology, physical 100% energy claim, P≠NP, or Langlands endpoint is proved by this localized result. Original J29 **6/6 nominal switch roots** and **5/6 original J24 full event-state boxes**, and J30 *nominal* period-return interval survive unchanged. Preserve source zero modes, signed residual and event/refinement \(t/k\) indices under all chart transports. No force push or merge.
