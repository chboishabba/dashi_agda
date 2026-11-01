# YM Nonperturbative Packet

Date: 2026-06-03

Worker 4 inspected the Sprint 40 YM artifacts, Agda receipts, and sibling
`../dashiCFD` p=7 diagnostics.  The most promising route is the
all-diameter KP/activity route, not the Balaban physical beta bridge and not
OS/Wightman transfer.

Status: **NO-GO for promotion, productive packet for all-diameter KP/activity**.

## Route Choice

### Selected route: all-diameter KP/activity bound

This lane has the strongest local substrate:

- `DASHI/Physics/Closure/YMActualP7WilsonPolymerActivityReceipt.agda`
  records an actual same-prime p=7 Wilson polymer activity surface and
  explicitly replaces the toy rho input.
- `DASHI/Physics/Closure/YMSamePrimeKPConvergenceProofReceipt.agda`
  records the KP grammar:
  `sum_{Gamma containing e0} |z(Gamma)| exp(a |Gamma|) < 1`.
- `DASHI/Physics/Closure/YMBTPathCountingKPThresholdReceipt.agda`
  records p=7 non-backtracking branching.
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ym_p7_d3.csv` gives a
  finite diameter 1-3 analytic majorant table.

The open gap is sharp: the repo has an actual activity definition and a
finite bound table, but not an all-diameter theorem tying every retained
same-prime Wilson polymer to the same geometric majorant uniformly in volume,
depth, and carrier scale.

### Rejected route: Balaban physical beta bridge

Current receipts mark this as target-only.  In particular:

- `YMBalabanPhysicalBetaBridgeTargetReceipt.agda` requires a
  nonperturbative block-spin/RG flow from `beta_phys ~= 6` to a KP-safe
  carrier beta.
- `YMBetaBridgeQuantitativeGapReceipt.agda` records the blocker: physical
  beta is below convergence by about `4.11` and below strict absorption by
  about `6.97`; naive perturbative running is recorded as insufficient.
- `Docs/YMBalabanContinuumLimit.md` retracts finite 43-step induction as a
  proof target and replaces it by a continuum-uniform target.

No local sibling artifact supplies the missing nonperturbative RG transfer.

### Rejected route: OS/Wightman transfer

The OS/Wightman lane is conditional, not promotable:

- `YML5OSAxiomsForGaugeSectorReceipt.agda` records OS data conditional on
  L4 and candidate-only L3 tightness, with finite reflection positivity not
  upgraded to continuum reflection positivity.
- `YML6WightmanReconstructionReceipt.agda` accepts OS reconstruction only as
  conditional authority over that YML5 package.

This lane cannot move until L3/L4 and continuum OS positivity are promoted.

## Evidence Inventory

`Docs/ClaySprintFortyCalculationHarvest.md` records the local p=7 result:

- diameter 1 and 2 enumerator: finite ratios are large and non-promoting.
- diameter 1-3 analytic table:
  - beta `6`: cumulative through D3 `29.7232985113`
  - beta `7.69`: cumulative through D3 `10.7986440908`
  - beta `10.13`: cumulative through D3 `2.96691547847`
  - beta `13.64`: cumulative through D3 `0.683098850852`
  - beta `16.7`: cumulative through D3 `0.252282568378`

`../dashiCFD/scripts/ym_p7_polymer_enumerator_d3.py` uses:

```text
p = 7
c_min = 0.242
a = 0.5
count(d) = 7^d
activity_bound(beta,d) = exp(-beta*c_min*d)
entropy_weight(d) = exp(a*d)
```

So the intended all-diameter majorant is geometric:

```text
r(beta) = exp(log(7) + a - beta*c_min)
sum_{d>=1} r(beta)^d = r(beta)/(1-r(beta))
```

With those constants:

```text
beta=10.13: r=0.9944655210, all-diameter sum=179.6854818629
beta=13.64: r=0.4252960132, all-diameter sum=0.7400262098
beta=13.70: r=0.4191653315, all-diameter sum=0.7216603179
beta=16.70: r=0.2028091579, all-diameter sum=0.2544047764
```

This is the concrete opportunity: if the table's bound is promoted from a
diameter 1-3 diagnostic to an actual all-diameter Wilson-polymer theorem,
then the same constants give a strict KP pass for carrier beta at or above the
active strict seed window.

## Packet Theorem Target

Prove the following carrier theorem, without invoking physical beta transfer:

```text
AllDiameterP7WilsonActivityBound:
  Fix a same-prime p=7 root edge e0.
  For every retained p=7 Wilson polymer Gamma containing e0,
  assume:
    1. |z(Gamma)| <= C0 * exp(-beta * c_min * diam(Gamma))
    2. the incompatible same-prime polymer count at diameter d is <= 7^d
    3. the KP size/compatibility weight is <= exp(a*d)
    4. C0 is volume/depth/scale uniform
  Then:
    local_KP_sum(e0)
      <= sum_{d>=1} C0 * exp(d*(log 7 + a - beta*c_min)).
  Hence local_KP_sum(e0) < 1 whenever
    C0 * r(beta) / (1-r(beta)) < 1.
```

For `C0=1`, `c_min=0.242`, `a=0.5`, this proves a carrier KP pass at
`beta=13.64` and above.  Use `beta>=13.7` for robust statements, matching the
margin-split receipt.

## Required Checks

Pass requires all of the following:

- Actual Wilson activity: the inequality must be for
  `z(Gamma)=exp(-beta*S_carrier(Gamma))-1` or a valid absolute-value upper
  bound from the same carrier Wilson action, not toy rho.
- All-diameter coverage: every retained same-prime p=7 polymer containing
  `e0` is covered, not only minimal D1-D3 samples.
- Uniform constants: `C0`, `c_min`, and `a` must be independent of finite
  volume, carrier depth, and block scale.
- Overlap compatibility: the count must cover the actual incompatibility
  neighborhood used by KP, not only non-backtracking paths.
- Tail closure: compute `C0*r/(1-r)` and verify it is strictly below one.
- Boundary preserved: no physical beta bridge, continuum YM, OS/Wightman, mass
  gap, or Clay promotion follows from this carrier theorem alone.

## Known No-Go Boundaries

- The finite enumerator output
  `../dashiCFD/outputs/ym_p7_polymer_d3/ym_p7_polymer_d3.csv` is not the
  promotable bound: its `exp(-beta*S)-1` diagnostic saturates near one in
  magnitude per polymer and yields huge cumulative ratios.
- The analytic D1-D3 table is evidence for the geometric route only.  It is
  not an all-diameter theorem.
- A pass here would close carrier KP/activity only.  It would still leave the
  Balaban physical beta bridge and continuum/OS transfer open.

## Verdict

**Pass:** no.

**Fail/no-go:** current artifacts do not prove actual all-diameter KP, Balaban
physical beta transfer, or OS/Wightman transfer.

**Most promising packet:** prove the all-diameter p=7 Wilson activity
geometric majorant above.  It has explicit constants, a computable tail, and a
strict carrier KP pass condition.  The remaining work is real: replace the
finite diagnostic table by a uniform theorem over actual retained Wilson
polymers.
