# Navier-Stokes Analytic State

Status: fixed-cutoff LP identity and conditional danger-shell route recorded; Clay-level steps remain open.

## What Landed

1. Full fixed-K LP identity
   - Receipt: `NSTailFluxLPIdentityFullDerivationReceipt`
   - Result: the fixed cutoff tail identity is recorded with pressure term zero, viscous term negative, and nonlinear term isolated as flux.
   - Boundary: it does not prove `theta < 1`.

2. Adjacent-shell leakage bound
   - Receipt: `NSAdjacentShellLeakageBoundReceipt`
   - Result: adjacent leakage is recorded as conditionally absorbable by an epsilon fraction of dissipation.
   - Diagnostic update: the LH/paraproduct ratio stays below `theta=1`; HH, not adjacent LH leakage, is the computed barrier-crossing term.
   - Boundary: the estimate depends on the K-star drift/scale hypothesis and does not preserve theta by itself.

3. Conditional danger-shell maximum principle
   - Receipt: `NSDangerShellMaxPrincipleConditionalProofReceipt`
   - Result: under H1 controlled K-star drift, H2 mild regularity or weak domination, and H3 positive dissipation, theta at the danger shell stays below 1.
   - Boundary: H1/H2 contain the missing control.  The computed HH term crosses/exceeds the barrier in small-`nu`, large-shell regimes.  The non-circular replacement target is an `H^{-1/2}` nonlinear-defect estimate; importing `H^{1/2}` velocity control directly would be circular as a Clay proof.

4. Conditional theta-to-BKM/Serrin bridge
   - Receipt: `NSThetaTailToBKMBridgeReceipt`
   - Result: theta control plus a uniform K-star bound is routed toward BKM/Serrin continuation.
   - Boundary: the BKM criterion is not discharged unconditionally.

5. Paper 1 comparison-theorem target
   - Receipt: `NSPaper1ClayTargetReceipt`
   - Result: the achievable Paper 1 target is conditional `Theta < 1` control of `H^{11/8}` by interpolation.
   - Boundary: this comparison theorem is open/conditional and is not a Clay proof.

## Diagnostic

Script: `../dashiCFD/scripts/ns_theta_full_sweep.py`

Output: `../dashiCFD/outputs/ns_theta_full_sweep.csv`

The default synthetic sweep covers five regimes and reports all rows with `NO_PROMOTION`. In the default run, `K_star_le_K_nu` held for all rows. That is diagnostic support for the seam locator, not a theorem about drift.

The new diagnostic content is a component split:

- LH ratio stays below the `theta=1` barrier.
- HH term crosses/exceeds the barrier in dangerous small-`nu`, large-shell regimes.

This sharpens the blocker: the hard analytic term is HH.  The revised route is
to control the nonlinear defect in `H^{-1/2}` and then use dual pairing against
the tail in `H^{1/2}`.  Using `H^{1/2}` velocity regularity as an input would be
circular for a Clay proof.

Second-pass tail restriction:

- Generated file:
  `Docs/Images/clay-analytic-sprint/ns_theta_tail_restricted.csv`.
- `Theta_global` is low-shell dominated at `k=2` in the sampled traces.
- The tail theorem should use
  `Theta_tail = sup_{k >= K_diss(nu)} theta(k)`.
- Sampled `Theta_tail` passes for `smooth` and `kolmogorov`, fails for
  `near_critical` and `rough`, and is unavailable for the sampled `inviscid`
  row because `K_diss = 178` exceeds `k <= 64`.

## Remaining NS Lemmas

1. Non-circular K-star drift control: prove `K*(t)` stays in the dissipation range from initial finite-energy/smooth data alone.
2. Non-circular weak domination: replace the mild-regularity hypothesis in the danger-shell max principle with a direct flux/dissipation domination estimate.
3. Tail-to-vorticity closure: discharge the BKM/Serrin bridge without assuming the regularity it is meant to prove.
4. HH replacement estimate: prove `||P_{>K*}(u.grad u)||_{H^{-1/2}} <= epsilon*nu*||P_{>K*}u||_{H^{3/2}}` without importing `H^{1/2}` velocity regularity, Serrin, BKM, or stronger regularity.
5. Comparison theorem: prove the conditional interpolation target `Theta < 1 -> H^{11/8}` without promoting it to Clay.

## Publication Posture

Publishable claim: theta is a computable seam variable, the fixed-K LP identity plus diagnostics isolate HH as the exact analytic obstruction, and Paper 1 can target a conditional comparison theorem where `Theta < 1` controls `H^{11/8}` by interpolation.

Forbidden claim: unconditional regularity or Clay promotion.
