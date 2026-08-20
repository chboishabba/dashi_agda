# Typed eventually-consistent fibre scheduling

`DASHI.Cognition.PNF.TypedEventuallyConsistentFibreSystemExact` formalizes the
scheduler boundary exposed by the SensibLaw strict-runtime profile.

The model has three pairwise interaction modes:

```text
commute  exact local advances may be reordered
join     local observations reconcile through an idempotent/commutative/
         associative merge
braid    ordering/provenance remains observable and an explicit directional
         residual must be reconciled
```

A `CertifiedCommutingBatch` is only a physical batching certificate.  It retains
individual fibre identity and proves the exact pairwise commutation law needed to
reorder members.  It does not identify the batch with one semantic object.

`BraidObligation` carries source fibre, target fibre, state, residual and the
proof that the pair is genuinely in `braidMode`.  No theorem silently converts a
braid into a commutative join.

`FairConvergenceCertificate` keeps global eventual consistency honest.  Local
commute/join laws do not automatically prove convergence; a concrete schedule
evaluator, fairness predicate, locally stable target and theorem that every fair
schedule reaches that target are separate fields.

The physical-economy surface records semantic fibre count separately from claim,
lifecycle and transaction counts.  A batching optimization is therefore valid
only when semantic-fibre work is unchanged and physical orchestration is
non-worsening.

The immediate SensibLaw specialization deliberately uses only the weakest safe
consequence: bounded set-wise lease acquisition.  Sentence and adjacent fibres
retain their existing per-fibre execution/failure transactions.  Stronger
set-wise completion or shared execution requires additional parity/commutation
proofs before promotion.
