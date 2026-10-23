# Vendored source notice: meta-introspector/aok

These files are verbatim external source snapshots from Mike Dupont / meta-introspector's
`meta-introspector/aok` repository. They remain under the upstream GNU Affero General Public
License v3 (AGPL-3.0). DASHI does not claim authorship of these files.

## Construction snapshot

Upstream commit: `c168223e96f7acc6179044f2a365a92db2e350c3`

- `Goldbach29/Program.lean`
  - upstream path: `d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Program.lean`
  - Git blob: `ff3f10a3e4c72771ac415a7f4bfb70a209478025`
- `Goldbach30/Program.lean`
  - upstream path: `1fcb5ebe-bbab-4c12-bc38-4f1cd4739c1b/code/Cryptids/Goldbach30/Program.lean`
  - Git blob: `ff748e1d68bf01d19e0c0998f6ac8d3a1c73e2f3`

The vendored Program blobs are byte-for-byte identical to the upstream Git objects: recreating
them in the DASHI repository returned the same content-addressed blob identifiers. Both files
contain their own upstream `fstep_enc` theorem connecting FRACTRAN stepping to their explicit
abstract `astep` machine.

## Goldbach29 semantic snapshot

Upstream revision: `428e2366045cb0b728115777df8bef14318a3bcf`

- `Goldbach29/Main.lean`
- `Goldbach29/Loops.lean`

At that revision **Main.lean and Loops.lean are the same upstream blob**:
`782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b`. The blob contains theorem text
`goldbachProg_halts_iff` but also begins by importing `Cryptids.Goldbach29.Loops`; therefore
DASHI preserves the source snapshot exactly and records the duplicate/self-import anomaly
instead of silently repairing it or promoting it to verified formal-theorem authority.

Git history shows the sequence `Create Loops.lean` -> `Rename Loops.lean to Main.lean` ->
`Create Loops.lean`, with the final Main/Loops entries resolving to the same blob at the pinned
revision.

## License and attribution boundary

The upstream repository declares AGPL-3.0. `LICENSE.AGPL-3.0` in this directory is an explicit
license/provenance notice which records the canonical upstream LICENSE Git blob
`0ad25db4bd1d86c452db3f9602ccdbe172438f52` and source location. DASHI does **not** claim that
the local license-notice file is byte-identical to that upstream LICENSE object.

Vendored source remains attributable to Mike Dupont / meta-introspector. DASHI-native Agda
modules, receipts, observer translations and independent replay code are separate
project-authored work and must not be represented as upstream authorship.

No vendored upstream source snapshot in this directory has been modified.
