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

## Oriented convolution-atom refinement

The packet-level alignment factor sees the already-summed forcing. When the
same fixed panel is replayed with `--triad-coherence-samples-per-output`, the
audit additionally samples oriented finite convolution atoms

\[
N_k=\sum_p N_{k,p},\qquad q=k-p.
\]

Its sampled unsigned denominators, paired with the exact resultant forcing and
packet pairing, distinguish inter-atom cancellation from rotation of the
already-summed resultant:

\[
C_{\mathrm{vec}}=
\frac{\|\sum_{k,p}N_{k,p}\|_w}{\sum_{k,p}\|N_{k,p}\|_w},
\qquad
C_\phi=
\frac{|\sum_{k,p}\langle u_k,N_{k,p}\rangle_w|}
{\sum_{k,p}|\langle u_k,N_{k,p}\rangle_w|}.
\]

The convention is ordered convolution atoms rather than canonical unordered
triads: their finite sum reconstructs the nonlinear RHS exactly and permits
uniform input sampling. The normal-approximation intervals cover only
within-output Monte-Carlo sampling; they are not certified enclosures.

This is a post-processing replay of the four state-anchored profiles. It does
not select new profiles, alter the admissible slice, or turn temporal ordering
into a causal or continuum claim.

## Canonical reality-orbit reaggregation

Ordered atoms are a computational basis, not the physical interaction unit.
The follow-up replay therefore maps the triad behind every sampled atom to its
unordered Fourier triple and identifies it with its reality partner. Before an
absolute value is taken, it sums all retained packet-output legs and both
input orders in that orbit. For a frozen packet weight this gives the finite
orbit contribution (T^K_Delta), and the telemetry estimates

\[
C^K_{\rm triad}=
\frac{|\sum_\Delta T^K_\Delta|}{\sum_\Delta|T^K_\Delta|},
\qquad
C_{\rm internal}=
\frac{\sum_\Delta|T^K_\Delta|}
{\sum_a|t_a|}.
\]

The first quantity is the canonical real-transfer coherence relevant to the
packet-energy balance; the second records cancellation introduced *inside*
the ordered-atom representation. The packet pairing in the numerator remains
exact. Both unsigned envelopes are Monte-Carlo estimates, so this supplies a
finite algebraic audit—not a certified inequality or a continuum triad
dephasing theorem.

## Interpretation boundary

Radial width and angular concentration are secondary explanatory observables.
The panel may identify a repeated temporal ordering, but cannot establish
causality or a profile-uniform coercivity bound. Coarse interaction turnover is
endpoint-only telemetry and cannot be used as a fine-time trigger.
