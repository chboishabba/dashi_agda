# Semantic Naming Policy

DASHI active theorem and source surfaces use term-appropriate names rather
than chronological worker labels. `RoundNNN`, `roundNNN`, and `RNNN` are not
active module or declaration names unless the token is an actual external
source identifier such as `CMP119` or `R278`.

Historical round numbers remain recoverable in
`config/semantic-name-registry.json` and explicitly archival documentation.
The registry distinguishes a historical name from the current semantic name;
it is provenance, not a compatibility-alias surface.

Renames are applied only through `scripts/semantic_round_rename.py`. The tool
requires explicit registry entries, rejects module collisions, updates Agda
paths and declarations, and can update Lean/generated text consumers. A
collision must receive a curated semantic name before its family is migrated.

The naming hierarchy is:

1. mathematical object or source object;
2. operation, relation, or theorem role;
3. status/consumer qualifier such as `Exact`, `Validation`, or `Compiler`;
4. historical provenance in the registry, not in the active identifier.

`literal` is retained only when it changes the semantic distinction between a
source-written object and a DASHI-derived theorem. When it merely records the
worker's historical packaging, it is removed from the active name.
