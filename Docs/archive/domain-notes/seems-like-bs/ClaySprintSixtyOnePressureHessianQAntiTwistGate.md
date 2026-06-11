# Clay Sprint Sixty One Pressure-Hessian Q Anti-Twist Gate

This is the precision update to the Sprint 61 CFM route.  The earlier
direction-coherence framing remains useful, but it is not the primary
observable.

## Load-Bearing Observable

Sprint 61 must measure the packet-local pressure-Hessian projection:

```text
Q_P = e2 dot Htf e1
```

where `Htf` is the trace-free pressure Hessian and `e1`, `e2` are strain-frame
eigenvectors at the packet core.  The live NS question is:

```text
mean(Q_P) < 0
```

on the `641` high-raw-red packets.

Direction-change remains evidence, but it is now a proxy.  The Sprint 56
quantity

```text
direction_change_integral_total = 38406.84183964504
```

and the `790` redirection-without-overwhelm packets motivate the route, but
they do not decide it.  The deciding sign is `Q_P`.

## Two-Condition Gate

The Sprint 61 output surface must include:

- `Q_P` for each high-raw-red packet;
- `Q_P_mean` on the high-raw-red packet set;
- `fraction_lambda2_nonpositive`;
- packet-local `omega_theta_bar_sign` as the anti-twist proxy;
- direction-change and mask-Hamming diagnostics as supporting context.

The two critical conditions are:

```text
Q_P_mean < 0
fraction_lambda2_nonpositive is large enough for the biaxial strain gate
```

If `Q_P_mean < 0` fails, the pressure-Hessian depletion route fails at the
load-bearing sign.  If `lambda2 <= 0` fails on most high-red packets, the
secondary strain channel remains open and the route needs additional argument.

## Kleis/Anti-Twist Bridge

The Kleis-facing interpretation is:

```text
Hypothesis D: averaged depletion        -> Q_P_mean < 0
Hypothesis G: eigenvalue gap control    -> gap does not collapse on red packets
Hypothesis S: sub-dominant regeneration -> no sustained positive regeneration cycle
```

The anti-twist-facing interpretation is:

```text
omega_theta_bar < 0
```

near the packet core is the spatial manifestation of the same depletion
mechanism.  It is not a separate proof object; it is a physical proxy for the
negative pressure-Hessian projection.

## DASHI Boundary

Existing no-2-cycle and ultrametric fixed-point vocabulary may support
Hypothesis S and reduced-ODE intuition.  They do not by themselves prove the
full PDE result.  The repo still needs:

- packet-local `Q_P` measurement;
- negative mean `Q_P` on the high-red set;
- eigenvalue gap control;
- anti-twist sign dominance;
- a formal Kleis-to-CFM/BKM bridge;
- no finite-time blowup.

No NS/Clay promotion follows from this ledger.
