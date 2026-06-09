# Clay Sprint Sixty One CFM Direction-Coherence Route

Sprint 61 records the post-Sprint-60 route change for the Navier-Stokes lane.

Precision update: `ClaySprintSixtyOnePressureHessianQAntiTwistGate.md`
supersedes the primary observable in this work order.  Direction coherence and
direction-change remain supporting evidence; the load-bearing observable is
now packet-local `Q_P = e2 dot Htf e1`.

## Sprint 60 Diagnosis

Sprint 60 compared three raw-action shell assignments:

```text
sigma_euclidean      = -0.0232
sigma_smoothed       = -0.0226
sigma_bt_ultrametric = -0.0312
```

The three values are indistinguishable at the current noise level, and raw
action is conserved across the reassignment.  This cleanly falsifies the
hypothesis that the flat raw-action cascade is an artifact of Euclidean shell
assignment.  The BT-ultrametric reassignment was a valid diagnostic, but it
does not rescue the source-budget route at the current N32/N64 resolution.

## Route Change

The current NS lane should not keep trying to close the same source-budget
summability estimate by changing shell labels.  The live route is now the
Constantin-Fefferman-Majda direction-coherence channel:

```text
large raw positive action in a packet region
+ vorticity direction coherence / Lipschitz control
=> no dangerous concentration
```

This matches the post-Sprint-56 evidence:

```text
redirection_without_overwhelm_count = 790
red_packet_count                    = 641
direction_change_integral_total     = 38406.84183964504
```

The packet action route found real red packets, but Sprint 60 shows their
flat cascade is not a shell bookkeeping artifact.  Sprint 61 therefore asks
whether those packets are geometrically depleted: high raw stretching is
present, but the vorticity direction field remains controlled enough to
prevent concentration.

## Sprint 61 Test

For each of the 641 red packets, compute:

- packet-local direction-change integral;
- adjacent time-step direction-mask Hamming distance;
- a packet-local lower bound/proxy for direction coherence;
- whether the packet region satisfies the CFM Lipschitz/coherence condition
  throughout its observed lifetime.

The target lemma is deliberately non-promoting until locally proved:

```text
AngularRedirectionWithoutStretchHarmless :
  HighRawRedAction P ->
  DirectionCoherence P >= delta ->
  NoDangerousConcentration P
```

## Governance

Sprint 61 is a route ledger and work order.  It records Sprint 60 as closing
the shell-reassignment/source-budget diagnostic path at current resolution and
opening the CFM direction-coherence path.  It does not prove the CFM bridge,
geometric depletion, BKM no-concentration transfer, no finite-time blowup, or
Clay/NS promotion.
