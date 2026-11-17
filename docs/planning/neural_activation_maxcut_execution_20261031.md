# Neural activation transport: local test evidence and remaining max-cut (2026-10-31)

Branch: `proof/neural-activation-state-codec-20261031`.
Discussion-origin architecture: Johl Brown. Original video-codec owner retained:
`DASHI/Combinatorics/TriadicVideoCodecObservationQuotient.agda`.
No ESD sources edited.

## Proof constructions
- `NeuralActivationStateTransportExact`: for any length-indexed vector
  and shared predictor context, XOR residual decoding reconstructs the exact
  original bits.
- `NeuralActivationStreamRegressionExact`: one-step acknowledged state,
  two-step roundtrip, raw predictor fallback, consumer congruence.
- `NeuralActivationDAGTransportExact`: sequential edge substitution,
  two-edge composition and parallel fork/join substitution.
- `DASHI/Unified/NeuralActivationTransportTOEExact`: focused TOE adapter.

The golden modules use safe mode, no explicit postulates, and no unsolved
metas intentionally. **Agda kernel typechecking has not been performed**;
central TOE import graph not modified pending that check.

## Local executable Python reference (not a cryptographic protocol)

A stateful reference at the conversation artifact
`neural_codec/state_codec.py` uses fixed-size schema-known byte vectors,
sequence and state commitments, raw/deflate/delta-deflate adaptive selection,
and strict fail-closed decode. Test file
`neural_codec/test_state_codec.py` exercised four test families under Python
3.13.5: all passed. Cases cover 256 first bytes times 5 second bytes,
1/16/512/7168/14336-byte payloads, replay, wrong schema, incorrect prior
state, and malformed length. This is local execution, not Agda or ZK proof.
A cryptographic hash *binds* a claimed previous state (subject to collision
resistance); it does not prove neural arithmetic or authenticate an
untrusted checkpoint.

Two-frame illustrative lengths with 7168-byte canonical tensors and
45-byte header:
- all-zero then constant-one: 99, 100 bytes.
- independent pseudorandom: 7213, 7213 bytes (raw fallback).
- identical pseudorandom buffer twice: 7213, 99 bytes.
The third case merely tests delta encoding mechanics; it is NOT evidence
that true neural activations repeat. No actual K3 activation trace has been
collected.

## Unclosed concrete proofs and empirical obligations

1. Agda 2.9 safe kernel check of modules and dependency versions; repair
   compilation errors if any, then attach the reviewed import bridge to TOE.
2. Full canonical FP16/BF16/FP32 byte/bit layout, endian handling, NaN
   payloads, signed zero, scale metadata and shape/stride contracts.
3. A full stream state-machine theorem including authenticated resync
   checkpoints under loss/reorder/duplicate, rather than two-frame roundtrip.
4. Verified roundtrip of concrete raw/entropy wire encoding in Agda.
5. Full finite arbitrary-DAG induction (current module establishes a
   sequential 2-edge and fork/join basis, not all DAGs).
6. Real model activation measurements; conditional entropy against actual
   causal predictors and header amortisation, codec timing/power.
7. Miner/worker nesting, network-cut flow, per-expert/shard throughput,
   local load versus offload and Pareto-optimal finite placement.
8. Cryptographic ZK/verifiable computation soundness for the approved
   model execution, independent of hashes; replay/double-spend settlement.
9. Demand-backed economic viability, prices, depreciation and federation
   margin under realistic utilisation. Reuse existing AI financing and
   terminal-payer owner modules.

No part of this pass establishes a K3-capable global mining federation,
actual compression savings on real activations, a cryptographic proof system,
or a profitable deployed network.
