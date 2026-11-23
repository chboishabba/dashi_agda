# J29A — physical diode-U activation: exact Picard continuation and quadratic switch-time comparison

**23 November 2026 | original-source Filsinger model PR #1537 | nominal prescribed-source nine-state circuit.** This is not a hardware observation, an original-source pin/wattage identification, or a periodic fixed-point certificate. Controller driver remains OFF. No CI, Agda kernel, or physical 100% recovery claim.

## Reuse, without replacing prior proof owners

- Source-validated predecessor J28B isolates the fourth original switching root, U diode ON, at `4.27514095 < t_U < 4.27574095`, with both spark ON and diode V active. **J28B's original J24 fourth nine-coordinate state box still fails 7/9 inclusions.**
- J28B's 75-step rational stage checkpoint at `t_0=4.26534095`: [canonical root and error radii](../../Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json), Git blob `74c1a94b30c44a772016c93b39558bc446359832`. The original GitHub checkpoint was reconstructed **byte-for-byte** in the local runtime and verified using `git hash-object` (`74c1a94b30c44a772016c93b39558bc446359832`). J29A then executed successfully against those original checkpoint bytes. The J29A checker itself also matches its committed Git blob exactly.
- New [locally executed independent Fraction checker](../../scripts/check_smith_filsinger_j29a_diode_u_continuity.py), Git blob `07b1c4a48f69d08e53e5221c25ea47f685b63121`, reads the checked-in checkpoint when executed in the repository. [Machine acceptance](../../Artifacts/smith-filsinger/j29a_fourth_U_physical_handoff_20261123.json).

## Exact physical flow over the root, not virtual U-inactive prolongation

Retain the original J25/J27 nine-state equations and the J28B stage-75 initial uncertainty, but use **both physical positive-part diodes** in the full continuous field throughout `[4.26534095,4.27574095]` with spark ON. Both source quadratures are conservatively enclosed in `[-1,1]` and `sqrt(0.03)` is enclosed by the exact rational interval `[0.17,0.18]`. Nothing depends on choosing one source-clock phase sample.

An initial radius-`1/5` nine-state interval box satisfies the exact rational Picard self-inclusion

\[
X_0+[0,0.0104]\,f(B)\subset \operatorname{interior}(B).
\]

Twelve monotone tightening steps of the form `B_next=X_0+[0,h]f(B)`, each with exact inclusion `B_next ⊆ B`, retain a self-inclusive tube for the *physical* switched system. The checker verifies throughout the whole enclosing tube:

- Original V forward guard strictly positive: lower bound approximately `+0.00546443412`.
- Spark-ON bank-above-off guard strictly positive (original Voff is `0.0018`).
- Original U activation guard derivative strictly positive: lower bound approximately `+0.51155662323`.

Consequently, in combination with J28B's already certified opposite endpoint U-guard signs, the **actual physical diode-U root is unique and the resulting U-positive branch continues through the fixed right endpoint `4.27574095`** without a V-off or spark event. Unlike the former virtual U-inactive right-endpoint bracket, this is a true (coarse) mathematical flow enclosure of the switching constitutive law.

## Original U diode kink: no state/vector jump

Let `g_U=u-b-V_d`, `j_U=max(g_U/R_d,0)`. The original U-only mode difference is

\[
 f_{\rm Uon}-f_{\rm Uoff}
 =\frac{g_U}{R_d}
 (0,0,-1.55/1.17,-1/1.17,1/C_b,0,0,0,0)^{\mathsf T}
\]

on the U-active side. Thus the vector fields **agree exactly at `g_U=0`**, while their Jacobians differ by the rank-one outer product of that coefficient vector and \(\nabla g_U=e_u-e_b\), divided by `R_d`. Since the existing U crossing is transverse, the classical state saltation matrix is **exactly identity**, although the Jacobian and subsequent smooth variational flow change. No reset, extra energy, or invented saltation factor is inserted.

## Quadratic common-endpoint uncertainty bound

On the containing tube, the first eight Jacobian rows are bounded by an exact rational per-mode row-sum computation for all four possible U/V diode active combinations. On `|x|<=1, |i_h|<=2`, the nonlinear HF capacitor derivative row is bounded by

\[
\frac{1}{C_h}+\frac{G_{\rm load}}{C_h}
+\frac{3(2+G_{\rm load})}{C_h}
=\frac{227}{3}<100 .
\]

This provides the conservative Lipschitz constant `L=100` for the full continuous positive-part flow. The inherited J28B verified U-guard slope upper in the fourth bracket is `1.250439215531...`; use `M=63/50` and width `w=3/5000`. Since the positive-part input is 1-Lipschitz and the virtual U-off trajectory has `g_U(t_*)=0`, variation of constants yields the rigorous **conditional comparison after the actual root**:

\[
\begin{aligned}
\lVert x_{\rm physical}(t_R)-x_{\rm virtual}(t_R)\rVert_\infty
&\le \frac{\|c\|_\infty}{R_d}\,\frac{M w^2}{2}\,e^{Lw}\\
&\le \frac{500}{39}\frac{63}{50}\frac{(3/5000)^2}{2}
       \frac{1}{1-100(3/5000)}\\
&=\boxed{\frac{189}{61100000}<3.094\times10^{-6}} .
\end{aligned}
\]

This is a **model-time / dimensionless nine-state sup-norm error**, not nanoseconds or watts, and it is not a claim that all original J24 fourth-event coordinates fit their radius-`10^-4` source boxes. The local checker asserts the exact fractions; decimals are only displays.

## Open frontier

1. Source-tighter J29B fourth-event state enclosure: use the original time-correlated J28B Peano–Baker endpoint or high-order Taylor/Lohner to pay all original 9/9 J24 fourth-box coordinates. The new coarse Picard tube proves the physical mode but is too wide for this.
2. Continue both active diodes after the fourth switch, certify V diode OFF near `4.323838`, then U OFF near `4.928751` with the original modes, no-extra-event guards and state-box receipts.
3. Weld exact source-clock \(\tau=20\pi/11\), full hybrid tangent/return defect and rational Banach/Krawczyk admission. Only then is an exact periodic orbit proved; separately address the uniform five-parameter family, original device wiring, field work and metrology.

**Status after J29A:** 4/6 original crossing roots isolated, 3/6 original J24 full event-state boxes paid; physical U-on branch now locally contained through `4.27574095`. No AGDA/CI or measured environmental extraction.
