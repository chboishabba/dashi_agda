# Residual-Bound Acquisition Compatibility

Date: 2026-09-09

This branch represents unresolved scientific-reference identity as an exact consumer-side residual plus a producer derived from the missing coordinate.

Current chain:

`ScientificReferenceResidual -> ScientificReferenceAcquisitionDemand -> retrieval/source work -> later same-object/source admission -> residual recomputation`

The branch intentionally does **not** import an unmerged PR #823 branch. Doing so would create a hidden cross-branch compile dependency.

PR #823 now owns the generic repository-wide contract in `DASHI.Core.BoundAcquisitionDemandExact`, with `DASHI.Interop.IntrospectiveProofLoopExact` as a consumer-relative specialization. Once that generic owner is available from this branch's declared base, the intended weld is therefore:

`ScientificReferenceAcquisitionDemand residual -> BoundAcquisitionDemand alignment selected residual`

with dependent equalities proving:

- the selected requirement denotes this exact scientific-reference residual;
- the acquisition is indexed by this exact residual;
- the acquisition producer equals `producerForReferenceCoordinate (missingCoordinate residual)`.

For the concrete Robert V. Kohn residual, a generic name/QID lookup is therefore insufficient. The bound acquisition must preserve the consumer-specific same-object requirement: the candidate is the Robert V. Kohn who coauthored the cited CKN paper. Tadeusz Bałaban remains a distinct residual tied to the lattice-gauge-theory source consumer; payment of either residual cannot close the other.

This is the same work shape now carried by the Nat runtime/formal lane:

`live residual -> bound demand -> shared/reused physical acquisition where admissible -> residual-local observation/admission -> recompute exact residual -> paid | still open`.

Physical lookup work may be coalesced when producer and source surfaces permit it. Residual identity and payment never coalesce merely because the retrieval call was shared.

Firewalls preserved:

- retrieval result != residual payment;
- candidate QID != same-person proof;
- payment of another residual != payment of this residual;
- shared retrieval != shared semantic payment;
- lookup demand != theorem/source/promotion authority.
