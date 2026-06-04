# Clay Sprint 47A Packet Lineage Audit

Date: 2026-06-04

Sprint 47A replaces the Sprint 46 adjacent-shell proxy

```text
rho_K = Rplus_(K+1)/(Rplus_K + epsilon)
```

with an observed-prefix packet transition audit on 3D truth snapshots.

## Output Contract

The NS diagnostic harness adds:

```text
--packet-lineage-audit
ns_packet_transition_table.csv
ns_packet_transition_summary.csv
ns_packet_transition_summary.json
```

The table emits child packet rows for K to K+1 transitions:

```text
time
K
packet_id
parent_packet_id
state_K
state_Kplus1
mass_K
mass_Kplus1
overlap_score
centroid_distance
direction_angle
BT_lane_id
braid_word_id_proxy
```

The summary emits shell-level transition terms:

```text
M_plus_plus
M_plus_zero
M_plus_minus
s_eff_K
2^(K/2) * s_eff_K
rho_packet_K
pass_persistence
route_status
```

## Diagnostic Construction

The first implementation uses coarse spatial packets:

```text
packet = active high-enstrophy voxels inside a coarse spatial lane
```

Packet labels use physical signed stretching:

```text
plus  : signed stretching mass > threshold
minus : signed stretching mass < -threshold
zero  : otherwise
```

Parent matching is conservative:

```text
same snapshot
same coarse lane
K -> K+1
```

Unmatched plus children count as new positive source.  True advected material
parents, true BT lanes, and braid words are not certified.

## Decision Rule

The target packet inequality is:

```text
Rplus_(K+1) <= M_plus_plus(K) * Rplus_K + s_eff_K
```

with:

```text
M_plus_plus < 1/sqrt(2)
sum_K 2^(K/2) * s_eff_K < infinity
```

This sprint can only test an observed prefix.  It cannot prove uniformity or
summability.

## Boundary

Sprint 47A is diagnostic only.  It does not prove packet parent confidence,
true BT eta, braid lineage, uniform physical bridge, stretch absorption,
no finite-time blowup, or Clay Navier-Stokes regularity.  All promotion flags
remain false.
