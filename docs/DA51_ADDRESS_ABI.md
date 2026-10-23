# DA51 address ABI mirror

`dashi_agda` mirrors the canonical DA51 wire ABI whose normative formal owner is `dashi_lean4/DA51/Core.lean`.

```text
[prefix:16][type:4][data:44]
prefix = 0xDA51
```

Historical type codes 0-7 remain frozen. Type 8 (`atlasEntry`) uses:

```text
[level:4][biome:4][status:4][serial:12][reserved:20]
```

The mirror is implemented in `DASHI/DA51/Core.agda` and `DASHI/DA51/Atlas.agda`. `DASHI/DA51/Provenance.agda` keeps producer/artifact provenance separate from the 64-bit address.

At the HME boundary, `AddressedTrace` carries an `EvidenceRef` plus a `TraceWitness`. Possessing the evidence reference does not prove witness admissibility or any theorem.

`fixtures/da51_v1.json` is the shared cross-language contract: all 23 atlas addresses, decoded vectors, malformed examples, maximum serial coverage and the explicit identity/provenance/authority separation invariants.

Existing DA51 trace/shard identities remain valid and are not automatically reinterpreted as atlas coordinates.
