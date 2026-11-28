# J28 — validated uncertain spark-OFF handoff, physical OFF-mode return, and 3/6 original event-state boxes

**23 November 2026 | Filsinger original source-owner PR #1537 against master.** This is the source-only nine-state mathematical model with a prescribed synthetic incident wave, driver OFF, finite resistances and unchanged original source attribution. No original pin netlist, measured environmental source or physical extraction efficiency is implied.

## Source/readback and execution

[J28 exact-rational checker](../../scripts/check_smith_filsinger_j28_spark_return_on_interval_20261123.py) Git blob **e22573e6189ff460e80f9bc1de13b3787d169b79** was executed locally, and the committed GitHub content verified byte-for-byte by its Git blob hash. It consumes the unchanged J25/J26/J27 validated independent J18-equation source chain, including the original first two J24 event-state admissions, and imports J24's six source event-state coordinates. The original J18 numerical Python itself is not byte-executed here. No GitHub Actions, CI or Agda kernel.

The input is one exactly specified rational nine-state initial point from J23, which is **not known to be periodic**. J28's exact integer/rational proof is **nominal**, not the five-parameter family.

## Event-2 to event-3: genuine switched OFF equations and time uncertainty

J27 certifies the second hybrid event, spark ON→OFF, at uncertain time `3.49129269<t_OFF<3.49129275` and its nine-state interval event vector. A direct switch-state reset would be wrong: bank and HF inductor state coordinates remain continuous, but their derivatives change.

For source-defined spark mode chi=1 when ON and chi=0 when OFF, the relevant physical equations include

    db/dt=(j_U+j_V-G_bleed*b-chi*i_h)/C_b,
    di_h/dt=(chi*b-x-(R_coil+chi*R_gap)*i_h-k_h*u)/L_h.

Thus OFF changes the bank derivative by `+i_h/C_b` relative to ON and changes the HF inductor derivative by `(-b+R_gap*i_h)/L_h`; no state reset or energy insertion is introduced.

The checker builds an exact rational nine-dimensional state tube containing every admissible event state from J27, across every uncertain OFF time. It evaluates the actual **diode-V-active, U-inactive, spark-OFF** vector field on the whole time interval and proves Picard self-inclusion from the uncertain event time to the fixed right endpoint `t_R=3.49129275`. It also verifies the two diode active-set guard signs and that the bank cannot reach the ON threshold in this tiny interval. The interval Jacobian norm bound is approximately **25.66871795**, and `L*(t_R-t_L)<1/2` validates uniqueness. The fixed-right-endpoint enclosure width is about **1.074732e-6** in the worst coordinate (not a claim of a uniquely known event time).

The physical OFF field, original nonlinear HF capacitor, externally prescribed matched wave quadratures and all dissipative channels are preserved in a 52nd-order Taylor/residual recurrence. The same exact `10^30` directed integer grid and a rigorously bounded nine-by-nine comparison matrix exponential control each step. Five consecutive segments (four of length 0.005 and one of length 0.002) pass Picard/error self-consistency and strict original diode/spark guards to

    t=3.51329275.

There are no extra ON, U-active or V-inactive guard events on this validated segment.

## Third original event: spark OFF → ON, unique upward root

From the fixed pre-event time, virtual smooth OFF-field integration is used solely to bracket the next threshold. It yields exact outward bank guard numerator enclosures on the `10^30` grid:

| Bound | Lower numerator | Upper numerator |
|---|---:|---:|
| Left bank-minus-Von at t=3.51534025 | -52758619633402386075209 | -14393509752171757963516 |
| Right bank-minus-Von at t=3.51534095 | 50658885676384984352089 | 89024671736032091849592 |
| Direction-corrected ON-crossing slope throughout | 147368577971186488764594187387 | 151700834822405639423069432271 |

All numbers are exact integers divided by `10^30`; rounded displays are not used for assertions. Since the left guard is strictly negative, the right strictly positive and the bank-crossing derivative strictly positive throughout, one unique spark ON root exists in

    3.51534025<t_ON<3.51534095,

width `7e-7` **dimensionless model-time units**, not hardware microseconds.

The checker evaluates **all nine coordinates** for the whole root-time interval, with validated original-equation error, and proves componentwise containment inside J24's third original `spark ON` event-state box (radius `10^-4`). U diode stays inactive; V stays active. The spark rank-one saltation determinant (post/pre bank derivative) lies in

    [-0.857413612055,-0.857376183230],

strictly negative and nonsingular. The spark field is discontinuous across the event but its state vector is continuous, which is why post-event time uncertainty needs a distinct interval transfer.

**Original J24 hypothesis payment: 3 of its six event-state boxes are now welded to one validated nominal trajectory.** The first diode-V ON was certified by J26, second spark OFF by J27, third spark ON by J28.

## Longer continuation and unresolved certificate

The J28 consumer intentionally ends before integrating the physical ON field after event three. A separate **exploratory** signed Peano–Baker matrix interval trial (not yet committed or native-replayed) indicated that a time–state-correlated handoff is more effective than naively propagating the entire uncertain event-state box; a finite nominal continuation can reach about `t=4.265` before the expected U-diode activation near 4.27549, but a validated fourth J24 event-state box has **not** been recorded. Do not promote that exploratory path to a fourth-event pass.

The rigorous next work is to derive and run the true post-ON fixed-right-endpoint handoff by comparing the physical ON field against the validated virtual OFF field, while retaining the exact jump forcing in bank and HF inductor components. Then use a sign-aware validated transition matrix (or full Taylor/Lohner model) to control wrapping through the remaining diode-U ON, diode-V OFF and diode-U OFF guard roots, and finish at `tau=20*pi/11`. Only a validated full-period map, its derivative on a nonzero state box, and rational Banach/Krawczyk inclusion can certify an exact periodic orbit. The initial rational J23 numerical centre is **not** itself such a proof.

The J21 positive-coil-loss obstruction to 100% source-to-load transfer remains valid in this finite-loss model. No Duga/HAARP/SURA/ionospheric natural field, physical Filsinger terminal, useful-work meter or gravity mechanism has been empirically identified.
