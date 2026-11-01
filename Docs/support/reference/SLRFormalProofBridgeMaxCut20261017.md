# SLR External Formal-Proof Bridge Max-Cut

Date: 2026-10-17

This note is the runtime interoperability companion to `DA51ProofRouterMaxCut20261017.md`.

## Ownership

`dashi-repo` does not own SLR semantic state. SLR remains the production owner for PNF revisions, propositions, residuals, proof obligations, payment, recurrence, and Matter state. The repository product stores only the opaque identity join needed to route formal work:

```text
demand_ref
external_obligation_ref
statement_digest
route_id
optional DA51 address
```

No SLR PNF graph, proposition payload, residual payload, review decision, or payment state is mirrored into `.dashi/repository.sqlite3`.

## External route

```text
SLR FormalProofDemand
  -> dashi-repo semantic discovery / dedupe / history
  -> fail-closed absence protocol
  -> proof-debt classification
  -> agda2lean capability when relevant
  -> repository reuse | Aristotle | Agda | Lean
  -> FormalProofRouteReceipt
```

`external_route_id` hashes the base route identity together with `demand_ref`, `external_obligation_ref`, and `statement_digest`. Therefore a changed formal statement cannot silently reuse the old external route/payment identity.

Exact/equivalent live repository owners still suppress generation and route to `repository-reuse-review`. Similar/history matches remain search evidence only. Incomplete repository coverage still blocks novel generation.

## Evidence lookup

Formal evidence is indexed by the exact triple:

```text
demand_ref + external_obligation_ref + statement_digest
```

A DA51 address, symbol name, artifact family, or old route ID cannot substitute for this exact payment key.

The repository stores the evidence join as `evidence-only`; it deliberately records `establishes_proof = 0`. SLR decides whether independently checked evidence satisfies its own formal-obligation contract.

## CLI

```sh
dashi-repo prove route-external-obligation \
  "formal statement/search query" \
  --demand-ref formal-demand:... \
  --obligation-ref proof-obligation:... \
  --statement-digest sha256:... \
  --target-prover lean \
  --da51 0xDA51...

dashi-repo prove evidence-for-obligation \
  --demand-ref formal-demand:... \
  --obligation-ref proof-obligation:... \
  --statement-digest sha256:...
```

## MCP / service

Read-oriented additive surfaces:

```text
proof_route_for_obligation
formal_evidence_for_obligation
```

They sit beside existing `proof_route`, `proof_route_history`, `da51_resolve`, `da51_evidence`, and `da51_frontier`.

## Authority firewalls

```text
external route != proof
repository match != theorem equivalence unless independently established
agda2lean capability != proof
Aristotle candidate != kernel certification
DA51 status/address != proof
formal evidence index row != SLR payment
```

The bridge is scheduling/provenance infrastructure only. Certification remains with the actual Lean/Agda checker; SLR retains authority over whether that certified result pays a particular runtime proof obligation.
