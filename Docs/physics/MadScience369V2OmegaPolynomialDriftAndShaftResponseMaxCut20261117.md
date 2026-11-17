# V2 Ω — polynomial drift and shaft-response discriminator (17 Nov 2026)

This is a source-independent **mathematical/experimental protocol**, not measured evidence about @madscience369 V2. The complete locally tested Python source, tests and receipts are packaged separately; do not claim they are contained in this GitHub commit.

## Exact 32-run design theorem

The pre-existing four-block schedule contains two observations per arm per block, paired at local sequence positions summing to seven, with cyclically rotated arm order across four blocks. Assign weights +1/8 to arms 00 and 11, −1/8 to 01 and 10, and index the 32 observations by global position t = 0,…,31.

The exact polynomial moments Σ w(t) t^k for k = 0,…,4 are

`(0, 0, 0, 144, 12768)`.

Consequently a **single uniform** additive sensor drift of degree at most two cancels from the factorial load×recovery contrast without restrictions on its polynomial coefficients. The cancellation requires the whole four-block schedule: an individual eight-run block does not generally cancel quadratic drift. A fixed-recovery loaded-minus-unloaded contrast also cancels global quadratic drift, but its cubic moment is nonzero. This does *not* cancel changing block-by-block drift, sensor carryover or differential calibration bias.

For a contrast with measured row errors |e_t| ≤ ε_t, the deterministic bound is Σ |w_t| ε_t. For a globally shared polynomial nuisance Σ a_k t^k with |a_k| ≤ B_k, add Σ B_k |Σ w_t t^k|. No Gaussian/independence assumptions enter this bound.

## Distinguish two different mechanical claims

The factorial shaft interaction is `I_shaft = (S11 − S01) − (S10 − S00)`. A negative interaction means enhanced recovery reduces the *incremental* shaft demand compared with ordinary recovery. It does **not** mean the recovered configuration requires no additional shaft power under loading; that stronger claim concerns the separately measured `S11 − S01`.

A conservation-consistent negative control gives incremental shaft demand of +8 W with ordinary recovery and +5 W with enhanced recovery. Then I_shaft = −3 W **yet shaft demand still rises by 5 W**. A positive electrical interaction alone cannot demonstrate reduced shaft backaction.

## Two measured energy boundaries, not inferred stores

`P_motor = P_shaft + D_motor + dE_motor/dt`
`P_shaft + P_aux = P_load + P_other + D_generator + dE_generator/dt`

Both balances must close *within stated measurement errors*. A physical claim about stationary operation must independently account for motor and generator stored-energy endpoints. Losses inferred as balancing residuals are not independently measured loss reductions.

## Acceptance and current unresolved gates

Local original-source implementation: 22/22 new tests; 309/309 tests in the available stitched integrated subset; the legacy PWM donor test was excluded because its donor module was not in that local source tree. The local result is not GitHub Actions or Agda kernel acceptance. All original 16 strict P0–P4 physical/formal gates remain OPEN.

No original V2 shaft torque, source-selected winding/controller topology, simultaneous electrical measurements or independent storage endpoints were supplied. The next evidence cut must apply these exact criteria to calibrated, randomized original-apparatus load/recovery interventions; until then causal efficacy and device attribution remain unverified.

Source attribution: the V2 claim belongs to @madscience369; Smith/Filsinger mechanisms are comparative mathematical analogies, not identified hardware.
