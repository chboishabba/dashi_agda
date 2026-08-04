# SSP15 compression of FRACTRAN states and transitions

`DASHI/Combinatorics/SSP15FractranCompression.agda` treats the fifteen SSP labels as a compression alphabet for the existing `FractranCOL.EV5` state and transition semantics.

## Three distinct claims

The module separates three notions that must not be conflated.

### 1. Outcome-preserving quotient

A classifier

```text
encode : EV5 -> SSP
```

may identify many FRACTRAN states under one of fifteen labels when it supplies:

- one representative state per label;
- representative soundness under `FractranCOL.run`;
- completeness of equal labels for terminal outcome.

This is lossy state compression but semantically safe for terminal-result queries.

### 2. Lossless label-plus-residual codec

A bare fifteen-way label is not treated as a lossless encoding of arbitrary exponent vectors. Lossless compression therefore has the form

```text
EV5 <-> SSP × Residual
```

with a proved decode/encode round trip.

The SSP label carries the reusable basin/model component. The residual carries the information inside that basin that cannot be discarded.

### 3. Transition compression

A compressed transition

```text
compressedStep : SSP -> Maybe SSP
```

is valid only when the state classifier is a congruence for the existing `FractranCOL.step` operation:

```text
encode x = encode y
  -> map encode (step x) = map encode (step y)
```

This is the key condition that turns a static clustering into a dynamics-preserving quotient. The module proves that a sound compressed transition preserves both successful steps and halting.

## Whole-run compression

`SSP15RunCompression` adds a compressed terminal evaluator and requires:

```text
compressedRun (encode state) = encode (run state)
```

This is stronger than assigning an SSP label to a state. It says the fifteen-state quotient commutes with completed FRACTRAN execution.

## MDL promotion

`SSP15CompressionReceipt` charges four components:

- quotient/model description;
- label stream;
- residual stream;
- compressed transition description.

The SSP compression is promoted only when this total is no worse than the literal FRACTRAN representation and it carries outcome-or-lossless authority plus transition authority.

## Honest boundary

The current module provides the exact proof interfaces. It does not yet construct:

- the canonical `EV5 -> SSP` classifier;
- fifteen outcome-sound representatives;
- a minimal residual code;
- a step congruence proof;
- or a measured MDL win.

Those are now finite, named discharge obligations rather than an informal claim that SSP labels automatically compress FRACTRAN computation.
