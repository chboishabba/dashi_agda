# J27 — validated physical diode-V handoff, first spark-OFF event, 2/6 J24 event-state boxes

**23 November 2026 | PR #1537, base master | original nine-state synthetic source-only J18 consumer.** Exact original Smith/Filsinger source attribution maintained. Controller drive zero. Original environmental source, hardware pins, natural incoming-wave power, calibrated load and any gravitational effect remain unverified.

## Execution and source identity

[J27 executable](../../scripts/check_smith_filsinger_j27_second_spark_off_validated_20261123.py) reuses [J26 exact first-event consumer](../../scripts/check_smith_filsinger_j26_first_diode_validated_taylor_20261123.py) and the original J25 rational interval primitive. It was **locally executed successfully and matched its committed Git blob byte-for-byte**:

- J25 primitive `5d723374d71281cc5583582cc17d15016deaa8a3`.
- J26 first-event `78cfdaa6c473eb1712194a17fa5ee46fa9dd5a94`.
- J27 physical V-diode and spark-OFF `6c7d7781f11943fc5b1267a6259bf3dc14f374d3`.

The verifier checks the exact rational J23 initial-point trajectory, **not an interval-certified periodic fixed point** and not the five-dimensional parameter rectangle. It reproduces the 37 accepted J26 pre-event slabs and strict first diode-V guard endpoints before introducing the actual active V-diode equations. The native original J18 numeric script is **not** byte-executed: its physical equations are independently transcribed and checked via these exact-arithmetic consumers. No CI, GitHub Actions or Agda kernel was used.

## Physical diode handoff: do not replace an uncertain event by a sample

J26 proves a single forward V-diode activation at

    3.389367008 < t_V < 3.389367010.

The physical diode constitutive current is `jv=max((v-b-Vd)/Rd,0)`. At the activation guard its current is **exactly zero**, so state and vector field are continuous, but the Jacobian changes. The J27 handoff is performed at the **exact rational right endpoint** `t_R=3.389367010`, not at a nominal floating event time.

On the mathematical virtual inactive-field trajectory, the V guard is strictly increasing throughout the proven crossing bracket with slope less than 0.5. Therefore for the at-most `2e-9` model-time delay after the actual root,

    0 <= gV_virtual(t) < 1e-9,
    0 <= jv_virtual(t) < (1e-9)/0.12.

The difference in the original nine-state vector fields is restricted to three capacitor/bank components and has sup norm less than `13e-9` over that source trajectory. A direct J27 exact interval Jacobian bound for the diode-active affine extension is **strictly below 100** in the bracketing tube, and the active guard derivative there stays positive. Using variation of constants and a simple rational upper bound,

    ||x_physical(tR)-x_virtual(tR)||_inf
      <= (2e-9) (13e-9) exp(100*(2e-9))
      <= 13/499999900000000000
      < 1e-15.

The full `1e-15` is added as an interval uncertainty to **all nine** virtual-state coordinate errors before resuming physical diode-V-active integration. This is a **validated no-reset handoff**, not an invented exact switching time. The first physical `0.002`-length segment validates a positive active-diode slope starting from a strictly positive V guard; later segments directly prove the entire V guard interval positive.

## Genuine active V-diode evolution and the second event

The physical V-active diode current `jv=(v-b-Vd)/Rd`, U diode current `ju=0`, and original spark ON constitutive term are retained in **explicit** nine-state, order-52 Taylor coefficient and residual equations. The new Jacobian incorporates the V-diode active-set entries in the two capacitor rows and the bank. The same 10^30 outward integer-grid and exact rational 90-term matrix-exponential tail used for J26 proves 13/13 guard-free physical V-active segments from `tR` through

    t = 3.490367010.

They exclude U-diode activation, V-diode deactivation and spark-OFF until the final bracket. Temporary smooth extension of the ON-spark field then proves one unique bank-voltage downward crossing:

    3.49129269 < t_OFF < 3.49129275.

| Interval fact, exact rational numerators on grid 10^30 | Lower | Upper |
|---|---:|---:|
| Spark guard at left endpoint, positive | 835604387886156863784 | 4905633029523974031447 |
| Spark guard at right endpoint, negative | -4686566508518742755322 | -616531726389373125989 |
| Direction-corrected spark crossing slope | 91248020302944744320890109809 | 94346345898621305380292417041 |
| Spark saltation determinant | -2267911308167538426014111777576 | -2267901476781109364209437589017 |

The spark slope interval is approximately **[0.09124802030,0.09434634590]**; its positive minimum ensures transversality and a unique OFF root. The spark-saltation determinant formula is the native rank-one **post-bank-slope / pre-bank-slope**, here approximately **[-2.26791131,-2.26790148]**, strictly negative and nonsingular. This is the spark-ON→OFF event, **not** the first diode event.

## J24 original state-box inclusion is now paid for the first TWO events

J26 already enclosed all nine state coordinates of the first original J24 `V diode activates` event in its preselected rational half-width `1e-4` event box.

J27 now evaluates **every possible time** in the certified spark-OFF interval, with the full rigorously propagated nine-state state error vector, and proves inclusion in the **second original J24 spark-OFF event state box**, **9/9 original coordinates**. Hence J24's conditional rational transversality and saltation geometry for these **two events** are attached to the actual nominal exactly specified original-equation trajectory, not merely to numerical event-centre guesses. The remaining four J24 original event boxes are still open.

## Remaining J28 forward construction

Start from the **uncertain spark-OFF time and state**, preserving the signed rank-one saltation and the actual OFF-mode changed bank and HF-inductor vector field. The next original switch is spark ON near `t=3.51534048`, followed by U-diode ON near `4.275489`, V-diode OFF near `4.323838`, and U-diode OFF near `4.928751`; all must receive validated event-time/state enclosures and no-extra-event proofs. Continue to exact `tau=20*pi/11` and enclose the full hybrid monodromy and centre defect. Only a validated state-box Krawczyk/Banach inclusion can prove an exact periodic orbit; the existing numerical J23 initial rational centre is **not certified periodic**. Uniform five-parameter period-box existence is a further step, not a consequence of the nominal two-event proof.

All numerical time widths are **dimensionless model time**; e.g. the spark bracket width `6e-8` must not be called nanoseconds. The finite-loss topology still excludes exact 100% environmental-to-load recovery for positive coil resistance and load, and no real environmental source measurement is claimed.
