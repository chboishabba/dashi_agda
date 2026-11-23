# J30 — full original-source nominal 6-event return to exact τ=20π/11, without fixed-point promotion

**23 November 2026 | original Filsinger mathematical source owner PR #1537 | base master.** Prescribed source-only nine-state J18 mathematical circuit, finite resistive losses, original Smith/Filsinger credit preserved. Does not establish an original Filsinger physical netlist, source pin continuity, naturally available RF input, calibrated terminal work, Schumann/Duga/HAARP/SURA provenance or antigravity phenomenon.

## What genuinely closes

J29 certified six unique, ordered, transverse diode/spark roots of the exact *nominal rational initial-value trajectory*; original J24 stronger nine-coordinate event-state boxes remain only **5 of 6** paid. J30 now certifies the **physical U-inactive/V-inactive/spark-ON continuation after the sixth event** to the original exact irrational source period

`τ = 2π/ω = 20π/11`, with `ω=11/10`, `T=20π=11τ`.

The new J30 rational checker does not simply integrate the original U-active smooth extension beyond the switch. It proves a correlated both-mode handoff, followed by **78/78 exact rational, fully time-validated no-diode smooth slabs** at length 0.01 (ending at `t≈5.708936104895576`), then a final partial slab to a rational lower bound on τ, and an outward Picard enclosure over the last irrational endpoint gap. Both diode guards are negative and the spark remains ON throughout the physical continuation.

**This is a full-period *initial-value return enclosure* for one exact rational numerical-seed point, NOT a periodic orbit existence theorem.** In particular, each of the nine return intervals includes its initial coordinate, but their widths are not small enough for fixed-point self-inclusion/uniqueness. No `DP_τ(B)` certificate, Banach/Krawczyk theorem, 11-fold exact periodic monodromy, or uniform five-parameter periodic family follows.

## A six-event source ledger, preserving the two statuses

| Original switching event | Validated nominal root | Original J24 nine-state event box |
|---|---|---|
| V diode activates | J26 | 9/9 paid |
| Spark ON→OFF | J27 | 9/9 paid |
| Spark OFF→ON | J28 | 9/9 paid |
| U diode activates | J29 repaired full-time transport | 9/9 paid |
| V diode deactivates | J29 | 9/9 paid |
| U diode deactivates | J29 | **Not paid** |

The sixth U-off event root was previously isolated inside `(4.92784016875,4.92984016875)` and narrowed by exact rational mean-value arithmetic to approximately `(4.928568535376962,4.928936104895576)`. The local J30 section-implicit-function projection retains affine time/state correlation, but the interval transition-matrix uncertainties still amplify the eliminated guard direction. The stronger projection now encloses **3 of the 9 original sixth event-state coordinates** inside the unchanged J24 radius-`10^-4` box; the full box is **still unpaid**. Do not promote 3/9 to 9/9 or collapse the entire J24 ledger to 6/6.

## Source-correct final diode deactivation handoff

Let `g_U=u-b-Vd`. At the root, the original continuous diode law is `j_U=max(g_U,0)/Rd`. The state and vector field are continuous at the guard, but its Jacobian changes across the branch. The local J30 checker uses the **exact J29 rational mean-value sixth-root bracket**, not a chosen floating event time.

From the original 60-slab physical U-on/V-off checkpoint, it computes the *virtual U-active smooth extension* at the **same fixed rational right endpoint** of the event-time bracket. An exact Picard tube encloses *both* source-defined U-active and U-inactive extension fields for every admissible root-time/state. Guard-specific Taylor residual plus Jacobian error proves that `g'_U<0` along the virtual trajectory; direct interval source equations give `g'_U<0` for the physical U-off extension in the handoff tube. It also proves V diode remains inactive and spark remains ON.

Along the virtual extension after its true root, `|g_U|≤(t_R-t_L) sup|g'_U|`. Only three original RHS components change with the U diode current; the vector-field difference is bounded in infinity norm by `2 |j_U|`. With `L` a source-defined no-diode Jacobian infinity-norm bound on the verified handoff tube, standard finite-time variation-of-constants gives the exact rational estimate

    ||x_actual(tR)-x_virtual(tR)||_∞
       <= 2 * sup|g'_U| * (tR-tL)^2 / (Rd*(1-L*(tR-tL)))
       < 1e-6.

The checker conservatively adds **1e-6** to every nine-state endpoint residual before continuing. There is no fictitious state reset, no assumption of an exact numerical switch time and no use of the unproved sixth J24 nine-coordinate box.

## Exact outward rational irrational-period endpoint

The source period is irrational, so treating a nearest IEEE floating-point time as `τ` would be insufficient. J30 uses Machin's identity

    π = 16 arctan(1/5) - 4 arctan(1/239).

It bounds each arctangent by 26 alternating rational terms and the next signed term, giving a **proven rational τ bracket narrower than 5×10^-38**. To avoid huge rational denominators during the last high-order Taylor integration, it rounds that bracket **outward** to an exact 16-decimal rational time grid:

    57119866428905331/10000000000000000
       ≤ τ ≤
    14279966607226333/2500000000000000.

The grid bracket width is **exactly 10^-16** model-time units. The last physical no-diode Taylor slab ends at its exact rational left endpoint. Picard self-inclusion then encloses the state at every time in the remaining 10^-16 interval including the actual τ, with both diode guards negative, spark ON and positive nonlinear-capacitor denominator.

## Nine-dimensional exact return enclosure

The [machine receipt](../../Artifacts/smith-filsinger/j30_nominal_full_tau_return_enclosure_20261123.json) stores the nine exact integer-grid lower/upper return-state bounds at scale `10^30`, together with the original nine exact rational initial coordinates. **All 9 return intervals include the corresponding initial rational coordinate**, a valid but weak numerical-root compatibility check.

The largest final interval width is about **0.018040136**, in the HF-inductor-current coordinate. The midpoint return deviations are of order 10^-8 or less, but those midpoint differences are *not rigorous upper bounds on the true return defect*; the true map value may lie anywhere in the validated enclosure. Therefore J24's earlier conditional rational Krawczyk budget (true centre defect below 8.42406×10^-9 and Jacobian error below 0.001) remains **unpaid**.

For completeness the nominal pure initial-value calculation can, in principle, be repeated 11 times, because the prescribed driver-OFF source and static physical circuit coefficients are exactly τ-periodic. However the stronger formula `M_T=M_τ^{11}` at a common fixed state requires a **proved τ-periodic orbit**; it is not yet a theorem of this J30 interval result.

## Independent source execution and committed-repository boundary

New locally executed source files:

- `scripts/j30_section_projection.py`: original sixth event, signed affine event-section projection; full sixth J24 box does not pass.
- `scripts/j30_no_diode_return.py`: original U-active→U-inactive physical handoff, 78 outward-rounded source-equation slabs, rational Machin endpoint and exact return enclosure.

Both scripts reuse the **locally byte-replayed** J29 independent exact rational source chain (J25–J28 source imports), not a byte-execution of the original J18 numerical solver. Source hashes are recorded in the J30 machine receipt. At this cut, the J29/J30 new executable source files are packaged in the independent local replay artefact and **have not all been installed on PR #1537**. The committed result consists of research analysis, machine-readable acceptance and roadmap reconciliation; do not call it GitHub-native byte-execution. No GitHub Actions/CI or Agda kernel were run.

## J31 endpoint, not another acceptance loop

The remaining mathematical weld is **not** to enlarge sampled parameter corner sets. Keep the exact original nine-state source and six-event chronological mode graph. Replace the overly broad per-component interval Jacobian products with a certified Lohner/Taylor-model or block-adapted sensitivity frame carrying exact correlations across event times. Validate `P_τ(x0)` to a centre defect that pays the Banach budget and, separately, `DP_τ(B)` including both spark saltations over a nonzero initial-state box. Then prove rational self-inclusion and strict contraction; only *then* the 11-fold original observation-window periodic monodromy and exact per-period energy equation may be promoted.

The original physical source, empirical terminal continuity and useful-load work remain separate admission gates. Exact 100% source-to-load delivery is not asserted for the present positive-loss model.
