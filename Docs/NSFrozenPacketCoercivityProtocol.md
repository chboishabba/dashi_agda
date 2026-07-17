# Frozen-Packet Coercivity Comparison Protocol

Status: finite-Galerkin, candidate-only, non-promoting. This protocol is an
evidence and identifiability boundary; it is not a Navier--Stokes theorem.

## Frozen comparison panel

Before further candidate selection, compare exactly these state-anchored
profiles under identical solver/backend, timestep, critical mass, packet
radius, checkpoint grid, and parabolic window:

1. saved positive-chi baseline;
2. radial perturbation `-0.04`;
3. phase perturbation `+0.04`;
4. coherence perturbation `+0.04`.

Every production invocation must emit a workspace-visible JSON receipt, stdout,
stderr, status JSON, and SHA-256 checksum. The runner writes and validates a
same-filesystem partial receipt before atomically promoting it. A transient
stdout result, elevated-only file, or unchecksummed JSON is not comparison
evidence.

The status sidecar is written first with `state: "running"`. It is replaced
only by `state: "promoted"` after JSON validation and checksum generation, or
by `state: "failed"` after a child exit or caught runner exception. A remaining
`running` status with partial artifacts is an incomplete attempt, not a result.

## Primary event rule

The authority packet is frozen at its initial shell window. Let

\[
\Gamma(t)=\frac{[N(t)]_+}{2\nu D(t)}.
\]

The sampled packet peak is \(t_P\). The primary downcrossing is the first
adjacent trapezoid window beginning at or after \(t_P\) whose positive-input
to viscous-loss ratio is at most one. Instantaneous sampled Gamma crossings
are retained as supporting telemetry, not substituted for this event rule.

## Exact finite factorization

The audit stores an internally exact factorization consistent with its rate
convention:

\[
\Gamma_+=F_{\rm forcing}F_{\rm geometry}F_{\rm align},
\]

where the receipt contains the direct value, product value, and residual at
each checkpoint. The protocol records the first post-peak time each factor is
at most 80% of its pre-peak maximum. The 80% threshold is fixed before panel
comparison and is not fitted from one trajectory.

## Interpretation boundary

Radial width and angular concentration are secondary explanatory observables.
The panel may identify a repeated temporal ordering, but cannot establish
causality or a profile-uniform coercivity bound. Coarse interaction turnover is
endpoint-only telemetry and cannot be used as a fine-time trigger.
