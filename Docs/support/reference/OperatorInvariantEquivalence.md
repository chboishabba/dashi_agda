# Operator Invariant Equivalence

`DASHI.Reasoning.OperatorInvariantEquivalence` records the thread delta that
cross-domain situations may instantiate the same abstract operator/topology
class only under an explicit invariant family.

The surface includes the canonical domains:

- debate;
- redox;
- market;
- immune;
- war;
- predator-prey;
- signal amplification;
- renderer transport.

It also records invariant-family vocabulary for transfer, gradient,
stabilization, escalation, equilibrium, catalytic amplification, and
repair/synthesis.  Equivalence strength is typed as exact, partial,
misleading, or blocked.

## Debate / Redox Toy Surface

The canonical toy inhabitants stage debate/redox in two ways:

- `toyDebateRedoxPartialInstantiation` says the domains share a selected
  transfer/gradient/stabilization operator-topology class only partially.
- `toyDebateRedoxExactUnderReceiptInstantiation` is exact only under the same
  selected invariant family and only when paired with
  `toyDebateRedoxReceiptGatedExactness`.

The receipt-gated exactness witness prevents the partial toy analogy from
silently becoming untyped exact equivalence.

## Non-Claims

The canonical non-promotion boundary sets these claims to `false` with `refl`
witnesses:

- global ontology;
- substance identity;
- untyped exact equivalence;
- universal reducibility.

The module is therefore a typed analogy/equivalence boundary, not a claim that
all domains are the same thing or that every domain reduces to one universal
operator class.
