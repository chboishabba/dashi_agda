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
