# James Michael DuPont / Aristotle Wikidata Lean snapshot

This directory records the source snapshot supplied for Aristotle request `ae06ae06-2580-422a-8fc3-92aeaaca8762`.

Whole supplied archive SHA-256:

`d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88`

Combined sorted `RequestProject/*.lean` source SHA-256:

`f5f0d6235e3bbf4fc881316900031f340accac75bb3825f10ed8d064f7c8ffda`

The final archive contains 39 `RequestProject/*.lean` modules and 13,187 Lean source lines. `SOURCE_MANIFEST.tsv` records every module's SHA-256, source-line count, declaration count, and direct imports. `DASHI/Ontology/LeanWikidataFullSourceManifest.agda` mirrors that inventory and maps every module to existing DASHI integration surfaces.

The supplied archive contains no license file. This repository therefore records provenance and source hashes without asserting or changing licensing terms.

The bridge does not claim that Agda kernel-checks Lean proofs. James's Lean development remains proof authority for its encoded propositions; DASHI imports source-matched theorem/checker results as provenance-bearing evidence with explicit non-promotion of truth/edit authority.

## Local theorem-execution receipt producer

`scripts/produce_james_wikidata_execution_receipt.py` closes the previously manual Lean-kernel seam without vendoring the unlicensed source archive. It requires the user-supplied source tree locally and, before writing a receipt:

1. verifies every `RequestProject/*.lean` file against `SOURCE_MANIFEST.tsv`;
2. verifies the exact `(module, theorem, polarity)` against `BRIDGE_CONTRACTS.tsv`;
3. generates a temporary Lean runner importing `RequestProject.<module>` and `#check`ing the fully-qualified theorem;
4. invokes local Lean (`lake env lean` when available, or `--lean-command`);
5. binds the canonical graph SHA-256 into the `dashi.james_wikidata_execution.v1` receipt.

Example for the existing artist/union worked fixture, assuming the supplied Lean development has been unpacked at `/path/to/james-source`:

```text
python scripts/produce_james_wikidata_execution_receipt.py \
  --source-root /path/to/james-source \
  --module ClassAlgebra \
  --theorem Wikidata.ClassAlgebraExample.artistKB_unionOk \
  --verdict certified_holds \
  --graph third_party/jmdupont_wikidata_lean/fixtures/artistKB.canonical.tsv \
  --output /tmp/artistKB_unionOk.execution.json

python scripts/verify_james_wikidata_execution_receipt.py \
  /tmp/artistKB_unionOk.execution.json \
  third_party/jmdupont_wikidata_lean/fixtures/artistKB.canonical.tsv
```

Boundary: the current producer proves that the pinned theorem elaborates in the hash-verified supplied Lean source tree and content-addresses the reviewed canonical graph. It does **not** yet parse an arbitrary external TSV into James's `KB` and run a checker over that runtime object. The existing graph↔source-example association therefore remains a reviewed bridge mapping. A future executable graph loader can strengthen this without changing the receipt contract.
