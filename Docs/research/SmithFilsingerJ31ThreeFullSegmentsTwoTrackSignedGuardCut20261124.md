# J31 P0 — three source-certified full smooth segments, exact two-track correlation, event-guard chronology

24 November 2026. Original Smith/Filsinger-attributed prescribed-wave nine-state finite-loss circuit, on [PR #1537](https://github.com/chboishabba/dashi_agda/pull/1537). This is an **exact-rational source ODE conditional smooth-mode result**: the physical mode persists provided the actual original start/terminal switching guards equal zero. It is NOT an existence proof for the simultaneous 69D shooting root, period orbit, five-parameter family, actual hardware, or physical 100% energy transfer.

## Executables, precise source ownership and receipts

- [Shared two-track original-source executable](../../scripts/check_smith_filsinger_j31_two_track_full_uv_on_20261124.py), verified Git blob **d4c8513c3142bb87ed8ebf06a7503409da34bd86**, locally executed byte-identically on both branches. Choose the segment with the CLI option --segment 1 (64 rational slabs) or --segment 4 (32 rational slabs).
- [Exact 64-slab event1 V-ON→event2 spark-OFF compact receipt](../../Artifacts/smith-filsinger/j31_two_track_full_v_on_spark_off_64_slab_receipt_20261124.json). Full deterministic local Fraction output 282,675 bytes, SHA256 **34e4dc04ff414439c238e866dce5e2e53c94e7ba7968c3225799202fd6071b16**.
- [Exact 32-slab event4 U-ON→event5 V-OFF compact receipt](../../Artifacts/smith-filsinger/j31_two_track_full_uv_on_32_slab_receipt_20261124.json). Full local Fraction output 150,496 bytes, SHA256 **629e7bc54e23c1281b13d045c95206bf0e60f4e3948ad244bbcd171ccf372663**.
- [Independent numerical original-source and 9×9 variational parity checker](../../scripts/check_smith_filsinger_j31_two_track_independent_numeric_20261124.py), [numeric-only machine receipt](../../Artifacts/smith-filsinger/j31_two_track_two_full_legs_independent_scipy_20261124.json): **9/9 states and 81/81 tangent entries contained** on each of the two source legs. These are double-precision diagnostic memberships, NOT a rigorous validation method.
- [Negative control executable](../../scripts/check_smith_filsinger_j31_naive_box_wrapping_negative_control_20261124.py), [exact negative receipt](../../Artifacts/smith-filsinger/j31_naive_wrapping_physical_guard_negative_control_20261124.json): a broad naive interval Picard step passes full-time flow inclusion but U ON guard, V ON guard and V-OFF slope all straddle zero. Source Picard alone does not pay physical mode admission.
- Earlier independent complete source event2 spark OFF→event3 spark ON is paid by [four-slab exact PB12 code](../../scripts/check_smith_filsinger_j31_full_spark_off_four_slab_20261124.py), [machine proof receipt](../../Artifacts/smith-filsinger/j31_full_spark_off_four_slab_source_20261124.json).

Every source uses original nine-state f, fJ, real nonlinear capacitor, prescribed trigonometric phase and diode/spark modes. The original source kernel prefix (all actual imported source primitives) was independently verified **byte-identical** between the older locally loaded and current committed GitHub modules; their unused later chart wrapper differs. No GitHub CI, proof-assistant kernel, merging or rebasing.

## Exact source centre/residual split

Rather than feeding independently widened interval output boxes into the next slab and losing source guards, carry a narrowly enclosed original centre solution C_j and a distinct nonnegative 9-component deviation E_j. The original input state uncertainty is exactly the source J24 ±10^-4 box. Both physical event clocks independently vary by ±1/200000. The first clock variation is paid by a short Picard-validated smooth extension and the absolute-time sensitivity; the final one by the true source terminal field.

Let J_j=[Df_m(X_j,T_j)], M_{uv}=sup |J_{j,uv}|, L=max_u sum_v M_{uv}, h_+ an upper duration, q=Lh_+ less than 1. For each source-mode slab the implementation checks the **strict whole-time Picard inclusion**
\[
C_j+[-E_j,E_j]+[0,h_+]f_m(X_j,T_j)\subset\operatorname{int}(X_j).
\]
It advances C_j using the exact source second-order integral Taylor interval, including the original source time derivative and nonlinear cap, **without claiming a guessed midpoint is exact**. Its source-labelled componentwise residual majorant, rounded *upward* to the original rational grid, is
\[
E_{j+1,u}\le E_{j,u}+h_+\sum_v M_{uv}E_{j,v}
 + \frac{q^2}{2(1-q/3)} \max_v E_{j,v}.
\]
This is the ordered variational series bounded by a nonnegative comparison, not a claim original signed Jacobians commute. Independently, all 81 entries of D_x Phi are enclosed by the eighth-order noncommutative time-ordered Peano–Baker products, and the entire segment uses **chronological left multiplication**. Absolute clock derivatives are paid by the source identities
\[
\partial_{t_0}\Phi=-D_x\Phi\,f_m(t_0,x_0),\qquad
\partial_{t_1}\Phi=f_m(t_1,\Phi).
\]
These are exact outer intervals on independently uncertain start/end event clocks of the complete smooth leg, not just one microchart.

## Full smooth leg 1: event1 V ON → event2 spark OFF

Mode (U,V,spark)=(0,1,1), nominal event clocks 3.389367008894 and 3.491292721190; 64 full-time strict source Picard slabs and 64 ordered PB8 original-source 9×9 derivatives **PASS**. Original U diode remains OFF throughout (greatest verified U-guard upper bound about -0.6786099). V-ON initial zero guard has strictly positive post-switch slope (lower >0.4034455) until the V-positive guard is strict from slab 2. The spark remains above its OFF threshold for slabs 0–55 (smallest positive bank-offset >0.000143784); on slabs 56–63 the source bank derivative stays strictly negative (largest upper < -0.0498101), so a matched final spark-OFF guard zero would exclude any premature OFF switch. The terminal exact box contains the nominal event2 J24 centre 9/9. Maximum q <0.044094; max 9D terminal component width approximately 0.003154 and max 9×9 derivative component width about 0.003403.

The final spark-OFF guard equation **is still unproved** as a simultaneous shooting root; this is conditional physical branch validity and a genuine full smooth-mode map for all admitted source state/time variations.

## Full smooth leg 2: event4 U ON → event5 V OFF

Mode (1,1,1), source clocks 4.275489023275 and 4.323837945006, 32 full-time strict source Picard slabs and 32 ordered PB8 original 9×9 derivatives **PASS**. U-ON start zero guard has strictly positive post-switch slope on initial slabs 0–3 (lower >0.7059700), then U guard stays strictly positive from slab 4. V-ON guard stays strictly positive through slab 24 (minimum lower >0.00057418); on slabs 25–31 its slope stays strictly negative (greatest upper < -0.1463793). Thus any actual matched terminal V-OFF zero guard is the first such crossing on the whole segment. The spark remains ON, with its bank voltage strictly above its OFF threshold. The exact terminal box contains the numerical event5 source centre 9/9; maximum q <0.080113; state component width approximately 0.003453 and tangent width 0.007118.

The start U-ON and terminal V-OFF zero guard equations must be **simultaneously paid by the 69D owner**. No alternative physical wire/switch assumptions were introduced.

## Crucial directional J24 box counterexample, paid by source code

Both new computed outputs satisfy the strict distinction
\[
B^{\rm J24}_{\rm target}\subset B_{\rm output}\quad\text{for all 9 coordinates},
\qquad
B_{\rm output}\subset B^{\rm J24}_{\rm target}\quad\text{for 0 of 9}.
\]
The desired **target numerical J24 box is contained in the broad output**, not conversely. This means the full flow is compatible with the target; it **does not admit the broad flow into that target**, nor prove the actual original switched trajectory enters it. The source checker explicitly computes and asserts both directions. The numerical centre inclusion, J24 source event box admission, signed matching residual and guard-zero root are logically different mathematical objects.

## Correct current J31 P0 ledger

**3/7 original complete conditional smooth source-mode maps:** event1→2 (64-slab), event2→3 (four-slab PB12), event4→5 (32-slab). The other **four whole segments OPEN:** source t=0→event1, event3 spark ON→event4 U ON, event5 V OFF→event6 U OFF, and event6→the original irrational source period tau=20pi/11. The earlier J29/J30 nominal source continuation and six exact root-time brackets (with 5/6 original J24 event-state boxes) remain valid as independently owned evidence, not automatic proofs of a nonzero-ball global source derivative. The actual sixth original event-state box remains unpaid.

**Still one simultaneous theorem:** construct full physically ordered source 69×69 [DF(B69)] and F69(z0) on a nonzero 69D state/time rational ball, with all six original event times, all 54 labelled signed matching errors, nine full-period return components, and six actual zero-guard constraints. Apply the existing source-preserving 15D Schur-to-69D rational preconditioner and prove all **69 strict Krawczyk row inclusions** plus uniqueness. The zero mode, signed residual, original source coordinate, physical time t and refinement index k must not be erased. No exact periodic orbit or empirical 100%-energy extraction is claimed by this source programme.
