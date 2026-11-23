# J28B — validated signed Peano–Baker continuation and fourth hybrid crossing, with J24 box still open

**23 November 2026 | Filsinger original-source PR #1537 | base `master`.** Extends the actual J28 certified synthetic source-only mathematical orbit, **not** a measured original Filsinger physical device. The controller driver remains OFF, the incident quadratures are prescribed, resistive losses and source attribution are unchanged. No CI/Agda kernel.

## Distinguish event existence from source-box payment

The J28/J28B cut ends with **four rigorously isolated and ordered threshold roots** for the exact nine-state initial-value trajectory specified by the rationalized J23 numerical initial state: diode V ON, spark OFF, spark ON, diode U ON. The first three coincide with all nine coordinates of their original J24 rational event-state boxes. The fourth U ON event **exists and is transverse**, but its current interval event-state enclosure fits **only 2 of the 9** coordinates of the original J24 fourth radius-`10^-4` box. **Therefore the admission ledger is 4/6 validated crossing roots, but only 3/6 original J24 event-state boxes discharged.** It would be false to call J24 4/6 complete.

## Source and executed proof chain

[Byte-identical J28 spark return checker](../../scripts/check_smith_filsinger_j28_spark_return_on_interval_20261123.py) Git blob **e22573e6189ff460e80f9bc1de13b3787d169b79** proves spark ON and the J24 third box. [New J28B exact interval Peano–Baker checker](../../scripts/check_smith_filsinger_j28b_signed_peano_baker_20261123.py) Git blob **1a357ce4719fb552680c1b042237283abb977b6a** was executed locally in reproducible checkpoint stages, and read back from GitHub to confirm exact source content.

The independent mathematical checker reuses the J25–J28 exact interval transcription of J18, not byte-execution of original J18 SciPy code. All relevant nonlinear HF capacitor and damping terms, diode modes and switched bank/HF inductor changes remain. The source model is original-Smith/Filsinger-attributed; no original physical terminal or naturally available wave input was established.

## Correlated ON-switch handoff

J28 proves the third event `3.51534025<t_ON<3.51534095`. Naively treating the nine-state event enclosure and event time as independent widens the fixed-time initial state by about `7.352023e-6`. J28B instead compares the **actual ON trajectory** after that uncertain switch to the already validated **virtual OFF trajectory at the same fixed right endpoint**, rather than taking independent state/time products.

The ON minus OFF vector field jumps in precisely two original equations:

    Delta f_bank = -i_h/C_b,
    Delta f_hf_current = (b-R_gap*i_h)/L_h.

No state jump is inserted. For every admissible switching time in the 7e-7 model-time bracket, an exact rational tube encloses both the virtual OFF and the actual ON flow through the short handoff, verifies the U and V diode signs and the spark ON-branch guard, and proves a contraction-capable common Jacobian bound. The componentwise variation-of-constants error is bounded using the original nonnegative majorant, with largest jump-induced state deviation `1.921976e-7` in the bank component and `4.742421e-8` in the HF inductor. Other state components are many orders smaller. Correlation reduces the fixed-time state enclosure maximum width to about **1.077213e-6**, rather than 7.352023e-6.

## Signed Peano–Baker, not a sampled or unvalidated tangent matrix

The original J27 componentwise comparison uses a positive matrix `A=|J|` and bounds errors by `exp(Ah)`. Over a long time interval it causes severe wrapping, despite the actual damped dynamics. The J28B solver retains a signed nine-by-nine interval Jacobian **[J] containing every derivative on the current smooth state tube**, then encloses the time-varying fundamental matrix via the time-ordered Peano–Baker series:

    Phi(h) = I + int J(t1) dt1
               + int_{0<t2<t1<h} J(t1) J(t2) dt2 dt1 + ...

Each order-`n` integrand is contained in the exact directed interval product `[J]^n`, and the ordered integration region has volume `h^n/n!`. The finite order-`N=8` interval sum and geometric norm tail enclose every entry of the actual `Phi(h)`, even when Jacobians at different times do **not** commute. With `L=sup||J||_infty` and `hL<N+2`, the omitted remainder has the exact positive rational bound

    tail <= (hL)^(N+1)/((N+1)!(1-hL/(N+2))).

The signed interval matrix is used to propagate the start-state error `delta`, while the same rigorously positive J27 matrix-exponential bound controls the polynomial ODE-defect forcing `epsilon`. An exact 52nd-order source-equation Taylor residual is recomputed at each stage. The checker proves strict tube inclusion, and all three inactive-U, active-V and spark-ON guard signs, **before** accepting each interval. Rounded displays and numerical solver tolerances are not used as proof inputs.

To bound runtime and preserve incremental proof witnesses, the user-facing local execution ran:

| Step group | Exact successful intervals | Time reached |
| --- | ---: | --- |
| Correlated switching-time handoff | Picard / componentwise error PASS | 3.51534095 |
| Block 1 | 20/20 at h=0.01 | 3.71534095 |
| Block 2 | 20/20 | 3.91534095 |
| Block 3 | 20/20 | 4.11534095 |
| Block 4 | 15/15 | **4.26534095** |
| U event isolation | Left/right virtual-inactive source flow PASS | 4.27514095…4.27574095 |

The interval rounding is exact rational / outward `10^30` integer grid. The end of block 4 has maximum endpoint component error `2.161732e-4`, and its U-diode guard remains strictly negative. The [compact rational 75-step checkpoint](../../Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json) preserves the exact endpoint centre, uncertainty radii and current guards for future source-reused continuation. The full four block receipts are in the accompanying local replay bundle. No GitHub Actions or Agda kernel.

## Fourth U-diode crossing: exact time bracket and unsuccessful original event-box inclusion

At `t0=4.26534095`, continue the **mathematical original U-inactive field** for bracketing, but do not use that field beyond the root as the physical evolution. The signed variational comparison proves:

| Exact outward 10^30-grid numerators | Lower | Upper |
| --- | ---: | ---: |
| U guard at t=4.27514095 (left) | -493670018764633578177957834 | -197624742905230032107900594 |
| U guard at t=4.27574095 (right) | +101314275505167737563488545 | +398794631141835659556052187 |
| U guard derivative over bracket | +745538856686118870906132101358 | +1250439215531312157277744411153 |

Hence the U guard is negative at the left endpoint, positive at the right and strictly increasing throughout (minimum derivative **0.745538856686**), giving a **unique transverse U diode ON root** in

    4.27514095 < t_U_ON < 4.27574095.

The V diode remains forward active and spark ON persists. This is the **fourth** original hybrid crossing and its time interval has width **0.0006 dimensionless model time**, NOT hardware milliseconds.

The interval state at this fourth root is a genuine enclosure, but it is still too wide to fit the original J24 event-state box. **Only 2/9 coordinates are included**, with 7/9 failing. This is a verified *failure of the current enclosure*, NOT a counterexample to the trajectory's actual proximity to the J24 numerical centre and NOT a proof of event-branch bifurcation. Narrower correlated event-time/sensitivity or full Lohner Taylor-model transport is required to pay that box.

[Machine acceptance with correct success/failure separation](../../Artifacts/smith-filsinger/j28b_fourth_diode_U_root_3of6_boxes_20261123.json) preserves guard signs, numerical error budget, exact source hash and the seven outstanding original-coordinate inclusions.

## Remaining next proof work

J29 should first tighten the U activation state/time enclosure so that **all nine original J24 fourth coordinates** are paid; preserve the discontinuity-free but Jacobian-changing U diode handoff into a rigorously validated U-and-V-active field. Then isolate V OFF near `t=4.323838`, U OFF near 4.928751, and return to `tau=20pi/11`, integrating the full hybrid tangent/saltation corrections and proving a rational fixed-point self-map. The exact source clock `T=11tau` reduces the periodic work only **after** a true tau-periodic orbit exists.

No full nonlinear periodic fixed-point theorem, uniform five-parameter family, 100% finite-loss input-to-load efficiency, gravitational phenomenon, or naturally available Duga/HAARP/SURA-to-device source work has been established.
