# Persistent Transport Motifs

This note documents:

```text
DASHI.Computation.PersistentTransportMotifs
```

The module packages the refreshed thread claim that many programs and machines
collapse at execution/component level into a small motif basis:

```text
load/fetch
transport
mix/transform
compare
mask/gate
branch
shuffle
accumulate/reduce
store/commit
synchronize
dispatch
```

## Surface

The core record is `PersistentTypedFibreFabric`. It treats execution as a
persistent typed fabric with:

- source artifacts;
- components;
- runtime states;
- typed fibres;
- local carriers;
- constraints;
- receipts;
- committed artifacts.

`MotifRewrite` represents one local constrained rewrite over that fabric.
`CPUInstructionAsLocalTransportRewrite` states the bounded reading:

```text
CPU instruction = one local transport rewrite inside a persistent typed fibre fabric
```

`PersistentTransportMotifSurface` then records component-collapse surfaces for:

- source-level programs;
- renderers;
- databases;
- codecs;
- physics engines;
- compilers;
- network stacks;
- spreadsheets.

## Non-Promotion Boundary

The module is deliberately non-promoting. `MotifNonPromotionCertificate` pins
the following claims to `false`:

```text
optimalCompilerClaim
semanticEquivalenceProofClaim
hardwareClosureClaim
wholeProgramRecoveryClaim
```

So the allowed claim is only:

```text
program and machine execution can be modeled as receipt-bounded transport motifs
over a persistent typed fibre fabric.
```

The forbidden claim is:

```text
this proves an optimal compiler, source-level semantic equivalence, hardware
closure, performance universality, or source identity recovery from traces.
```

## Integration

`DASHI.Interop.AggregateBidirectionalTranslationDischarge` imports the canonical
motif surface and certificate as the machine/renderer side of the broader
bidirectional ontology chain.  The computation lane therefore joins the same
transport discipline as Animalexic and renderer/light-codec surfaces without
promoting runtime optimization or semantic identity.
