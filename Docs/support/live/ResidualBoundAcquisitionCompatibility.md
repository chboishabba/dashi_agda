# Residual-Bound Acquisition Compatibility

Date: 2026-09-08

This branch now represents unresolved scientific-reference identity as an exact consumer-side residual plus a producer derived from the missing coordinate.

Current chain:

`ScientificReferenceResidual -> ScientificReferenceAcquisitionDemand -> retrieval/source work -> later same-object/source admission -> residual recomputation`

The branch intentionally does **not** import `DASHI.Interop.IntrospectiveProofLoopExact` or `ConsumerDefectSourceDemand` while PR #823 remains unmerged. Doing so would create a hidden cross-branch compile dependency.

After #823 lands, the intended weld is:

`ScientificReferenceAcquisitionDemand(residual) -> ConsumerDefectSourceDemand(liveResidual)`

with dependent equalities proving that the source reopening pays the exact scheduled missing coordinate and uses the scheduled producer.

Firewalls preserved now:

- retrieval result != residual payment;
- candidate QID != same-person proof;
- payment of another residual != payment of this residual;
- lookup demand != theorem/source/promotion authority.
