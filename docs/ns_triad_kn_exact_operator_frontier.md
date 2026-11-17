# NS triad K_N exact operator frontier

Date: 2026-06-25

## Status

The exact scripted mixed-tail cross block is now the only live Schur object in
this lane:

`L_FT,script^+(k,p) = -sum_{triads touching {k,p}} (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0).`

The sampled `N=6,8,10,12` Schur witness matches that exact object, and the bare
shell-geometry proxy has been separated off as a different object.

## What Is Not Proved

The following theorem is still open:

`||L_FT,script^N||_op <= C / N`

uniformly over NS-compatible profiles for the exact scripted operator.

So this lane is not promoted. Theorem authority, full-NS promotion,
BKM-exclusion, and Clay promotion remain false.

## Resumed Path

1. Kernel formula:
   the exact cross-block entry is now fixed as a repeated-pair incidence sum
   over retained positive-sector triad weights.
2. Exact scripted operator bound:
   prove a profile-uniform weighted Schur product bound
   `R_N(w_N) * C_N(w_N) <= C^2 / N^2` for the exact scripted pair-incidence
   cross block, then deduce `||L_FT,script^N||_op <= C / N`.
3. Schur residue transfer:
   use that bound to discharge `SchurResidueScale`, i.e.
   `q_gap(N) >= c_gap / N^2`.
4. BKM projection step:
   replace the sampled tiny BKM-tail projection with a structural
   orthogonality/projection estimate.
5. Residence bridge:
   combine the projection estimate with the trajectory-level residence-time
   control needed for the BKM contradiction/exclusion route.

## Boundary

This note resumes the live route without claiming the missing theorem. The
exact-object gate is upstream of both `SchurResidueScale` and the
BKM/residence bridge, so those downstream steps stay open until the
weighted-Schur `C/N` estimate is actually proved.
# R588 continuation: literal outer signed-cross decomposition

Direct-row correction: R541 constructs a literal fixed-spectator reciprocal
weight, but R545 applies it on only one side of a signed pair. R440 weights
both aggregates. Thus specialization of R589 to R541 is not a same-object
proof for R406. Implement a deep-FL/complement split directly on R545's
forcing half, retaining its fixed spectator and single weight factor.

Implemented in R590: `SpectatorSplit.At.literalForcingHalfDeepSplit590` uses
R545's `forcingHalfFactors`, the R589 complementary-fold theorem, and R291
left additivity. `deepOuterFarLow590` requires the actual outer far-low class
as well as the shell threshold. This is a direct-row algebraic result; the
remainder includes FL shoulder, HH, and comparable incidences. Bounds for
both terms and the spectator sum remain open. Source review and whitespace
checks are not Agda elaboration.

Next connection: construct R588's historical record from inequalities on the
literal R589 signed masses. The decomposition equality must be derived from
`literalCriticalConeDecomposition589`, not supplied by the caller. The caller
still supplies the physical energy/dissipation and companion quantities and
their three inequalities. R294's weight record has only swap symmetry, so no
weight-independent analytic constant is justified by that interface alone.

Implemented: `historicalWeldFromLiteralPayments589` derives the R434
decomposition field from R589 and closes the R588 scalar identity by `refl`.
`literalPaymentsBoundCommonCross589` consumes it in the existing R588 compiler.
Both remain conditional on the three literal inequalities. This is a
constructor of conditional witnesses, not a canonical physically paid witness;
the current closed-status flags remain false.

The next slice splits R589's actual outer FL and HH forcing vectors with
canonical `Shell.shellIndex` values. FL uses `3 min(p,q) ≤ 2 max(p,q)`;
HH uses `5 shell(k) ≤ 4 min(p,q)`, conservatively using the smaller high input
shell. Complementary masks define the shoulders. These are explicit finite
partition conventions calibrated to R234/R235, not physical payment theorems.
Their sums must recover the original R589 contributions exactly.

Implemented: `splitFold589` proves complementary masks recombine for any
physical incidence list. `farLowDeepShoulder589` and `highHighDeepShoulder589`
instantiate it on the actual forcing; `literalCriticalConeDecomposition589`
regroups their signed crosses into deep FL + deep HH + critical core. This
constructs the decomposition without assuming any R284 inequality. Zero-shell
handling follows the canonical ceil-log carrier; no nonzero analytic bound is
inferred. Static checks pass, but Agda elaboration remains unverified.

The 2026-09-10 upstream checkpoint is `6cd63dcd7` on
`origin/agent/ns-r580-bony-gram-frontier`. The next implementation constructs
the three outer R186 Bony contributions of the actual R440 common cross by
finite signed summation. Each contribution retains the complete amplitude
aggregate; only the forcing incidence is classified. This preserves cross-class
interference and does not identify outer classes with R587 inner classes.

Acceptance: an exact identity with no cardinality factor, no postulates, and
no assumed decomposition equality. This is repository-native algebra based on
R186, R291, R438 and R440, not a new external analytic result. Deep/shoulder
refinement, cutoff-uniform physical payments, and Clay closure remain open.
Agda execution is prohibited for this run; static review is not typechecking.

Implemented in `NSTriadKNLiveOuterSignedCrossDecompositionRound589Exact.agda`:
`LiteralOuterSplit.literalCommonCrossSplits589` composes the actual R438 forcing
fold with R581 routing and R291 right additivity. The equality retains the
complete R440 amplitude in all three signed contributions. R569 imports this
draft. This closes the algebraic outer split at source level; it does not
construct `LiveHistoricalSignedCrossWeld588`, whose historical decomposition
already includes all three R284 analytic inequalities.
