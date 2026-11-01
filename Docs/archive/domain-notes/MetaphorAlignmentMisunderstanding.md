# Metaphor Alignment and Misunderstanding

`DASHI.Reasoning.MetaphorAlignmentMisunderstanding` records a theorem-thin
surface for communication as observer-relative alignment.

The module treats metaphor and simile correctness as partial operator-equivalence
alignment: a source slice and target slice are acceptable only when the declared
operator action preserves the intended shared invariant on the aligned slice.
This makes analogy correctness local and receipt-bound, not a claim that the
source and target domains are globally isomorphic.

Communicative succinctness is represented in an MDL style.  A message is
succinct only relative to an audience context, a cost baseline, and receipts
showing that the intended invariants are preserved under that context.
The module includes `toySuccinctCommunication` as the canonical inhabited
context-receipted witness for aggregate discharge.

Interpersonal misunderstanding is represented as failed manifold/invariant
alignment across observer quotients.  The canonical failure catalogue is:

- vocabulary mismatch
- ontology mismatch
- context mismatch
- emotional-state mismatch
- scope mismatch
- intent/projection mismatch

The non-claim guards are explicit:

- no guaranteed perfect understanding
- no qualia recovery
- no universal exact translation
- no communication optimality without audience/context receipts

The safe reading is therefore:

```text
speaker quotient + listener quotient + audience context
  -> partial analogy/operator alignment, if receipts exist
  -> MDL-style succinctness, if intended invariants survive decoding
  -> misunderstanding witness, if manifold or invariant alignment fails
```

This document and Agda surface are self-contained and do not depend on parallel
worker changes.
