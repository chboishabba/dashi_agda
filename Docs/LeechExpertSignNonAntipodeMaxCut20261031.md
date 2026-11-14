# Expert sign is a geometric chart, not semantic opposition — max-cut

## Original owner and model integration

Consumes the **existing**
`DASHI/Core/ArgumentResponseNonGeometricOppositeBidiExact.agda`
(denial, evidence challenge, rule challenge, context and qualification)
rather than inventing a new meaning for 'negative'.
The existing Sophontic/LILA semantic intervention work is in
DASHI PR #1094/#1095, with Dust/Noise paired probes in #1265.
The Leech signed-history formalism belongs to PR #1442; runtime
implementation is LeechTransformer PR #4.

The new `LeechExpertSignNonAntipodeBoundaryExact.agda` explicitly
separates:
  * response kind (argument-level objection),
  * geometric action (identity or antipodal),
  * outcome annotation (acceptable, unacceptable, not evaluated),
  * learned expert identity and state transition.
It proves the finite involution and gives two example records with
**the same** semantic evidence challenge but **different** geometric
actions. These witnesses show the response category does not uniquely
determine the geometric action; they do not establish that either
action is a representation of a real learned semantic intervention.

LeechTransformer `tests/test_expert_sign_non_antipode.py` constructs
a concrete learned routing counterexample: when the router scores an
expert-specific history coordinate, jointly inverting activation and
history reverses which expert wins. Thus individual expert conjugation
does NOT imply global mixture equivariance. The test also keeps
argument annotations outside the router call, showing semantic
disagreement does not automatically trigger a sign flip.

## Necessary full-MoE mathematical condition

Let z=(activation,H_0,...,H_E), I_z the specified involution,
r(z) a learned top-k selected set, w_e(z) normalized selected weights,
and F_e the learned stateful expert. For a *strict* global action
commuting square, need an expert-index permutation pi compatible
with selected identities, plus:
  r(I_z z) = pi(r(z)),
  w_(pi(e))(I_z z) = w_e(z),
  F_(pi(e))(I_z z) = I_y(F_e(z)),
  U_(pi(e))(I_z z) = I_H(U_e(z))
for all selected expert transitions, including treatment of
unselected histories. If any condition fails, preserve an exact
correction or reconstruct/recompute the complete source state before
the consumer. These are **obligations**, not established properties
of the current learned router.

GELU exact parity (odd linear x/2, even nonlinear) remains useful
within the actual expert but does not establish these routing,
weighting, state, semantic or safety relationships.

## Federated optimisation implication

Do not deduplicate remote requests based solely on a shared ± sign
or an argument being a counterargument. A *network-saving* quotient
needs both consumer-side semantic action fit and exact state transport
or corrective bytes; otherwise the remote expert may be different and
the computation different. The 1/10 Gbit/s arithmetic remains an
ideal serialization bound. Locality/RTT dominates token-sized remote
calls; state/caching and real learned action reuse can provide larger
network gains than small codec improvements.

Verification: source-written Agda + Python tests; no Agda kernel run,
no executed tests and no measured semantic fitting or WAN benefit.
No ESD modification. Do not attribute this model-specific boundary
to the original Sophontic authors or original Leech-LILA architect.
