# Kant introspective residual contracts

This document records the narrow formalisation added after applying the existing
DASHI introspective proof-loop method to the current Kant discussion.

## Source / permission boundary

James Michael DuPont explicitly authorised help formalising the discussed Kant
work in the 8 Sep 2026 project conversation (`if you want to help formalize go
head`).  That statement is treated as scoped permission to collaborate on the
formalisation discussed there.  It is **not** treated as blanket permission to
relicense or republish every JMD artifact.

Repository visibility and technical provenance are also kept separate from
rights.  A public repository or fetchable page is not, by that fact alone,
classified as redistributable.

## Existing owner reused

`DASHI/Interop/IntrospectiveProofLoopExact.agda` already owns the repository-wide
method:

`live implementation -> formal model -> visualization/review -> surviving
residual -> bound payment -> verification/recompute`.

The Kant work does not add a competing planner.  It specializes the surviving
residual surface exposed by JMD's review.

## Five live residuals

`DASHI/Interop/KantIntrospectiveResidualContractsExact.agda` owns exactly five
residuals:

1. specification vs deployed-runtime conformance;
2. relay integrity/self-certification vs confidentiality;
3. bearer invite possession vs revocation / forward secrecy;
4. cached/archive checkpoint vs verified/recomputed checkpoint;
5. public/fetchable artifact vs rights-authorised republication.

Each residual has a distinct payment type.  A payment for one residual cannot
construct a payment for another merely by adjacency.

## Runtime observation ABI

`DASHI/Interop/KantRuntimeObservationExact.agda` provides non-promoting runtime
observation carriers:

- revision-bound spec/runtime vector observations;
- a relay H0-H6 diagnostic ladder;
- storage collection / rights-gate / publication observations.

The ladder is intentionally non-collapsing:

- H0 worker reachability is not end-to-end relay success;
- integrity is not confidentiality;
- publication success is not evidence of publication rights;
- a runtime test observation is not a Lean theorem.

## Rights / WrongType-style same-object discipline

Rights evidence must bind the **exact artifact** being published.  Rights or a
license attached to a neighboring repository, parent project, dependency, or
similar artifact cannot silently transfer to another object.

The relevant firewall is therefore:

`public/fetchable != licensed != publication-authorised`.

Likewise:

`formalisation permission != blanket relicensing`.

## Current implementation boundary

The formal and runtime-observation contracts are implemented in `dashi_agda`.
The current connected GitHub identity has read-only access to
`meta-introspector/kant-zk-pastebin`, so this tranche deliberately does **not**
mutate JMD's runtime repository.

A future runtime change can satisfy these contracts by emitting the referenced
revision-bound observations without changing the formal architecture.

## Validation status

Source integration and aggregate export are present on the branch.  Kernel
certification must be reported separately from source integration; no Agda
kernel-success claim should be made unless the exact branch/head is actually
checked by the repository's Agda validation path.
