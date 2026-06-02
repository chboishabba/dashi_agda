# NS Paper 1 Clay Target

This document is the Manager B spine for the Navier-Stokes lane.

## Claim Chain

1. Fixed shell cutoff `K` is selected before differentiation.
2. The Littlewood-Paley tail identity is locked with the correct signs:
   `d/dt E_{>K} = -Diss_{>K} + Flux_{>K}`.
3. The seam variable is `theta(K,t) = |Flux_{>K}| / Diss_{>K}` with
   positive dissipation required.
4. If `theta(K,t) < 1`, then the fixed-`K` tail energy decreases.
5. The runtime danger shell is the argmax of the finite theta profile.
6. The EV5 projection records `lane2 = danger shell` and
   `lane7 = tail energy`, with `v3` diagnostic-only.
7. The NS-to-EV5 shadow is exact only up to an LP commutator defect.
8. The computed paraproduct split separates the obstruction: the low-high
   ratio remains below the `theta=1` barrier in diagnostics, while the
   high-high term crosses/exceeds the barrier in dangerous small-viscosity,
   large-shell regimes.
9. The achievable Paper 1 contribution is a comparison-theorem target:
   conditional `Theta < 1` control of `H^{11/8}` by interpolation, recorded
   as open/conditional and not as a Clay proof.

## Refined Theta Diagnostic

The second-pass calculation generated:

```text
Docs/Images/clay-analytic-sprint/ns_theta_tail_restricted.csv
```

It separates:

```text
Theta_global = sup_k theta(k)
Theta_tail   = sup_{k >= K_diss(nu)} theta(k)
```

The current sweep has `Theta_global` dominated by the low shell `k=2` for every
trace.  That is not a dissipative-tail shell, so Paper 1 should consume
`Theta_tail`, `danger_shell_tail`, and `low_shell_warning`.  In the generated
CSV, sampled tail-restricted theta passes for `smooth` and `kolmogorov`, fails
for `near_critical` and `rough`, and has no sampled `inviscid` tail row because
`K_diss = 178` exceeds the available `k <= 64` range.

Checked Agda receipt:

```text
DASHI/Physics/Closure/NSTailRestrictedThetaDiagnosticReceipt.agda
```

## Open Clay Points

- `NS5`: prove the danger-shell maximum principle.
- `NS6`: prove an unconditional theta bound.
- Control adjacent-shell edge leakage at the danger shell.
- Replace the circular high-high estimate with the negative-Sobolev target:
  prove `||P_{>K*}(u.grad u)||_{H^{-1/2}} <= epsilon*nu*||P_{>K*}u||_{H^{3/2}}`
  without importing `H^{1/2}` velocity regularity, Serrin, BKM, or stronger
  regularity.
- Eliminate the LP commutator defect or bind it to Serrin/BKM control.
- Convert conditional tail decay into a full BKM continuation theorem.
- Prove the comparison theorem target `Theta < 1 -> H^{11/8}` by
  interpolation under explicit non-circular hypotheses.

## Publishable Boundary

The publishable Paper 1 claim is:

> NS theta is a computable seam variable; `theta < 1` implies conditional
> fixed-`K` tail decay; diagnostics separate harmless LH from barrier-crossing
> HH; the danger-shell locator is implemented; theta preservation and the
> `H^{-1/2}` nonlinear-defect estimate are the hard open points.

This does not claim Clay Navier-Stokes, unconditional regularity, or BKM
closure.  The Paper 1 target is a conditional comparison theorem: if
`Theta < 1` is supplied with the required interpolation hypotheses, then the
tail control should bind `H^{11/8}`.  That comparison theorem is still a target,
not an inhabited proof.

## Implemented Surfaces

- `DASHI.Physics.Closure.NSTailFluxLPIdentityAnalyticReceipt`
- `DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt`
- `DASHI.Physics.Closure.NSThetaImpliesTailDecayReceipt`
- `DASHI.Physics.Closure.NSToEV5ForwardSimulationActualReceipt`
- `DASHI.Physics.Closure.NSPaper1ClayTargetReceipt`
- `../dashiCFD/scripts/ns_theta_sweep.py`

## Runtime Diagnostic

The sweep script generates synthetic forced, unforced, and near-critical shell
traces and writes `promotion_status=NO_PROMOTION` for every row:

```bash
python3 ../dashiCFD/scripts/ns_theta_sweep.py \
  --out ../dashiCFD/outputs/ns_theta_sweep.csv
```

The output columns include `trace_type`, `k`, `theta_k`, `theta`,
`danger_shell`, `margin`, `dissipation`, and `flux`.

The current full-sweep evidence bundle is:

```text
Docs/Images/clay-analytic-sprint/ns_theta_full_sweep.csv
Docs/Images/clay-analytic-sprint/ns_theta_profile.png
Docs/Images/clay-analytic-sprint/ns_theta_profile_1.png
Docs/Images/clay-analytic-sprint/ns_theta_profile_2.png
```

This CSV must be read as a danger-shell diagnostic, not a pass certificate.  The
new split diagnostics are sharper than a single full-sweep pass/fail flag:

- LH/paraproduct leakage ratios stay below the `theta=1` barrier.
- HH/paraproduct terms cross or exceed the barrier in dangerous small-`nu`,
  large-shell regimes.

The evidence therefore identifies HH, not LH leakage, as the load-bearing
obstruction.  The needed analytic lemma remains:

```text
NonCircularKStarDriftBound
  + adjacent-shell edge-influx control
  + enough tail/Sobolev control
  -> BKM/Serrin continuation
```

Checked receipt links for this boundary:

- `DASHI/Physics/Closure/NSTailFluxLPIdentityFullDerivationReceipt.agda`
- `DASHI/Physics/Closure/NSAdjacentShellLeakageBoundReceipt.agda`
- `DASHI/Physics/Closure/NSDangerShellMaxPrincipleConditionalProofReceipt.agda`
- `DASHI/Physics/Closure/NSThetaTailToBKMBridgeReceipt.agda`
- `DASHI/Physics/Closure/NSNegativeSobolevDangerShellReceipt.agda`
- `DASHI/Physics/Closure/ClayBlockerAsymmetryReceipt.agda`

## Why The Drift Bound Is Still Open

The fixed-`K` identity and theta diagnostic isolate the right obstruction, but
they do not remove it.  The unresolved term is the high-high paraproduct in the
tail flux.  Low-high transfer can be bounded by standard Bernstein/Sobolev
bookkeeping and stays below `theta=1` in the diagnostics.  The high-high
interaction is different: it crosses/exceeds the barrier in small-`nu`,
large-shell danger regimes.  The corrected non-circular route is to place the
nonlinear defect in the dual space `H^{-1/2}` and pair it against the tail
velocity in `H^{1/2}`:

```text
||P_{>K*}(u.grad u)||_{H^{-1/2}}
  <= epsilon * nu * ||P_{>K*}u||_{H^{3/2}}
```

Importing `H^{1/2}` velocity regularity directly would be circular because it
is already regularity information of the type the programme is trying to
derive.

So the Clay-level lemma must be non-circular:

```text
Diss_{>K*}(t) dominates Flux_{>K*}(t)
via the H^{-1/2} nonlinear-defect estimate, without assuming H^{1/2}
velocity regularity, Serrin, BKM, or stronger regularity.
```

Equivalently, the programme needs `K*(t) <= K*(nu)` as a genuine consequence of
the NS dynamics, not as a moving-cutoff definition or a diagnostic observation.
Until then, Paper 1 is a precise reduction and runtime locator, not a proof of
global smoothness.

The corrected blocker status is therefore not merely `OpenUnknown`.  It is:

```text
OpenWithHighHighParaproductObstruction
```

The point is publication-critical: Paper 1 may say that DASHI isolates the
irreducible high-high paraproduct obstruction and gives a conditional barrier
theorem if a non-circular estimate is supplied.  It must not say that NS has
been reduced to a routine remaining lemma.

## Paper 1 Comparison-Theorem Target

The correct Paper 1 promotion target is not Clay regularity.  It is:

```text
Theta < 1
  + explicit interpolation hypotheses
  -> H^{11/8} control
```

This should be presented as a conditional comparison theorem.  It may be a
publishable analytic target because it connects the computable theta seam to
the `H^{11/8}` regularity lane, but it remains open until the interpolation
comparison is proved and the HH circularity is removed.  `NS Clay promotion =
false`.
