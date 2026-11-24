# J32 — complete fifth-to-sixth original source leg with signed Taylor jets

**24 November 2026 · [PR #1537](https://github.com/chboishabba/dashi_agda/pull/1537) · Smith/Filsinger-attributed nine-state synthetic prescribed-wave finite-loss receiver.** This proves a **conditional original-source smooth-mode interval map**, not a simultaneous 69D shooting root, an exact periodic orbit, hardware validity, or energy extraction.

## Proof-producing source and reproducibility

The actual original physical circuit f/fJ, phase, nine coordinates, six true named event guards, source constants and J29/J30 exact-root brackets are reused from the existing [J31 source module](../../scripts/check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124.py).

- [J32 rational Taylor-jet algebra](../../scripts/check_smith_filsinger_j32_source_taylor_jets_20261124.py), Git blob **22cff0bcc48f9cec68ec2c173237b0b224745197**.
- [J32 source long-leg strict Picard, signed variational and independent two-time checker](../../scripts/check_smith_filsinger_j32_signed_affine_full_leg_20261124.py), Git blob **d87baf7ef935be5041bb36216cd2ee8a78d3345a**.
- [Exact machine acceptance receipt](../../Artifacts/smith-filsinger/j32_event5_to_event6_signed_taylor_128slab_20261124.json), pinning **55,802 bytes of deterministic full Fraction output, SHA-256 91025015aa33aa0422346d8a3aa2b504254f7a8a65f75adc3ce256ebe8973520**.

New producer Git blobs match the locally executed bytes. The local reference copy of the earlier J31 source primitives memoized sine/cosine evaluation but used the same mathematical source; this is **not** a claim that the full current original J31 dependency blob was byte-replayed. The unchanged old/new GitHub original-source primitive prefix was verified separately in J31. No CI, Agda or Lean kernel.

Run the J32 long-leg checker on a checkout of PR #1537 with **--k 5 --N 128 --order 6** and its output/checkpoint options. To retain bounded local execution, the exact four checkpoint steps are stop 32, stop 64 with resume, stop 96 with resume, and the final resume to 128. The compact receipt records the exact result digest; no detached runtime file is needed.

## Original physical source segment and genuine independent clocks

Event5 V-diode OFF to event6 U-diode OFF, physical mode \((U,V,\chi)=(1,0,1)\), original clock centres:
\[
 t_5=4.323837945006,\quad t_6=4.928751407316.
\]
The input is the original nine-coordinate event5 J24 source state box, halfwidth \(10^{-4}\), previously source-admitted in the J29 nominal original trajectory. Actual event clocks are **independent**: \(t_5\pm 5\cdot10^{-6}\), \(t_6\pm2\cdot10^{-4}\). Their previously established J29/J30 exact-rational source root-time brackets lie strictly inside those domains.

All **128/128 strict rational Picard full-time slabs**, **128/128 chronological PB6 9×9 source variational slabs**, and the original-mode branch checks pass. On the first **127/128** slabs, the original signed U-on diode guard \(g_U=u-b-0.1\) is **strictly positive**. On the last slab it may contain zero, but its derivative is **strictly negative**, enclosed by the outward interval \([-0.201185,-0.097554]\). The V diode remains OFF throughout, with its negative post-OFF entry slope checked; the spark remains ON above its hysteretic OFF threshold. The independently moving event6 endpoint also has strictly negative original U-off pre-switch derivative. Therefore an actual *matched* endpoint satisfying \(g_U(x_6)=0\) is its first named U-off crossing. **That equation is still an unpaid simultaneous shooting requirement**, not an inferred root.

## New geometric mechanism — retain point, signed residual and source tangent separately

A previously attempted independent interval-centre propagation produced expanding interval diameters, so the broad fulltime Cartesian source tube eventually lost the signed diode derivative even while Picard passed. An example earlier direct-tube U-off derivative interval at step 102 was about \([-0.528,0.307]\), which contains both signs. That is an **observer collision**, not a physical trajectory counterexample.

The corrected transport uses three distinct objects at every original source/refinement time:
\[
 x_k\in p_k+R_k+H_k\Delta_0.
\]
Here \(p_k\in\mathbb Q^9\) is a selected *rational reference point*, \(R_k\) is its accumulated **signed original-source error interval**, \(H_k\) is an outward 9×9 original-source variational enclosure transported in **chronological order**, and \(\Delta_0\) retains the original labelled nonzero input-state/time uncertainty. Every whole-time tube \(X_k\) is checked by **strict Picard self-inclusion** and \(q=h\|[Df(X_k,T_k)]\|_\infty<1\).

The J32 algebraic source jet differentiates the original nine equations, the source sine/cosine quadratures, and the nonlinear capacitor denominator. It computes degree-6 Taylor coefficients on the rational point, then bounds the **seventh-order derivative coefficient** over the entire validated source time/state tube:
\[
 \left|\mathcal R_{7,i}\right|\le h^7
 \sup_{(x,t)\in X_k\times T_k}
 \left|\frac{d^7x_i/dt^7}{7!}\right|.
\]
This is a source-analytic outward-rational Lagrange remainder, not an empirical solver tolerance. If the reference endpoint enclosure is \(\widehat\Phi_k(p_k)\), the selected rational recentering error is explicitly
\[
 \ell_k=\widehat\Phi_k(p_k)-p_{k+1},
\quad H_{k+1}=\mathcal P_kH_k,\quad
 R_{k+1}=\mathcal P_kR_k+\ell_k,
\]
where \(\mathcal P_k\) is the ordered PB6 slab derivative. The error is **not silently erased** at recentering, and no product of time-varying source Jacobians is assumed commuting.

The key diode observer is **signed before interval projection**. In each fixed source mode, \(g'_U=f_u-f_b\) is affine in the state. The checker therefore evaluates \(g_U(p_k)+e_UR_k+(e_UH_k)\Delta_0\), then integrates a rigorous interval for the source-affine \(g'_U\) and its derivative on the full slab. This retains the original sign and source-identity relation between \(u\) and \(b\). A broad independent Cartesian evaluation of \(f_u(X_k)-f_b(X_k)\) would lose the source correlation.

**Measured exact-rational ceilings:** \(\max q<0.130435\); accumulated reference error radius \(<3\cdot10^{-9}\); labelled input variation image radius \(<0.000308\); maximum endpoint coordinate enclosure diameter \(<0.003910\).

## Independent start and end time derivatives

The initial/event5 and terminal/event6 clock uncertainty is paid using **two independently validated short virtual smooth extensions**, with exact outward state Picard checks and interval Peano–Baker tangents. For independent times:
\[
 [D_x\Phi(t_6,t_5)]\subset
 \mathcal P_{\rm end}\,H_{\rm nominal}\,\mathcal P_{\rm start}.
\]
The full source 9×9 interval state derivative and **both** original absolute-time derivative vectors are produced from
\[
 \partial_{t_5}\Phi=-D_x\Phi\,f(t_5,x_5),\qquad
 \partial_{t_6}\Phi=f(t_6,\Phi).
\]
These virtual extensions outside an event are mathematical smooth-branch derivative tools; they are **not** assertions that the physical device fails to switch across an event.

An independent numerical SciPy replay of the original nine-state IVP and derivative (numerical only) yielded **9/9 terminal coordinates, 81/81 fixed-clock derivative entries, 81/81 independently timed derivative entries and both 9/9 clock partials inside the rational intervals**. It is explicitly not the rigorous acceptance authority.

## Sixth state box and actual remaining J31 P0

The source-generated broad event6 output contains the original **numerical J24 event6 centre in 9/9 coordinates**, and includes the entire narrow numerical target J24 box in 9/9 coordinates, but is **not contained inside that narrow target in any coordinate (0/9)**. Thus J24's original sixth complete state-box admission is **still OPEN**; do not invert the inclusion arrow or identify a coarse observation with the original event state. Nonetheless the new source-derived **broad physical event6 input domain** can feed the remaining last-segment \(t_6\to\tau=20\pi/11\) proof without relying on the old narrow J24 box, provided the entire source matching/guard equation is retained.

New complete conditional original source legs count: **4/7** — event1→2, event2→3, event4→5, and now event5→6. Remaining **3/7** are \(0\to t_1\), \(t_3\to t_4\), and \(t_6\to\tau\). The original full 69D \(F\) and \([DF]\) on a common nonzero state/time ball, 54 signed original interface matches, six zero guards, 69 strict Krawczyk inequalities and uniqueness are all **OPEN**. Original six nominal exact root times, J24 5/6 narrow state-box admissions, J30 nominal full-period return and unmeasured Filsinger hardware/source/energy programme remain separately owned, not promoted.
