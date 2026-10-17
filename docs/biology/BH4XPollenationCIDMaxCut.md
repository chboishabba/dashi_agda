# BH4 xPollenation / CID max-cut — 2026-10-17

## Scope

This tranche composes existing owners rather than inventing another biochemical or transport model:

```text
BH4 finite Rhea matrix
+ exact UniProt panel
+ SABIO adjudication
+ PDBe/SIFTS mappings
+ optional exact-P352 Wikimedia identity receipts
        ↓
dashi.xpollenation-neighbourhood/v1
        ↓
ITIR shared-shard-artifact/v1
        ↓
file / HF / IPFS objectRefs
        ↓
artifact-resolution-receipt/v1
        ↓
dashi-repo authority-neutral xPollenation join
        ↓
existing BH4 four-gate kinetic adjudication
```

The scientific consumer remains `BH4FluxCandidateRankingExact` / `BH4FluxPaymentPreparationExact`. xPollenation only makes the candidate neighbourhood explicit, typed, replayable and content-addressable.

## Executable producer

`build_bh4_xpollenation.py` emits one neighbourhood for every reaction in the executed finite matrix. For the current panel this is 12 neighbourhoods.

Edge families currently emitted:

- `Rhea -> UniProt`: `catalysed-by`, from the executed exact panel crosswalk;
- `Rhea -> ChEBI`: `reaction-participant`, from Rhea RDF participant receipts;
- `Rhea -> SABIO`: `kinetic-parameter-for`, candidate-only;
- `UniProt -> PDB`: `protein-structure-of`, only when bounded SIFTS segments match;
- `UniProt -> Wikidata QID`: `curated-cross-reference`, only for independently verified exact P352 matches.

The phase runner now emits:

```text
artifacts/biology/bh4-xpollenation.json
artifacts/biology/xpollenation-neighbourhoods/RHEA-*.json
```

If an already-pinned Wikimedia panel receipt is available, pass it explicitly:

```bash
python3 scripts/run_bh4_phase4_maxcut.py \
  --wikimedia artifacts/biology/bh4-wikimedia-panel.json
```

No new Wikimedia crawl is silently initiated by the Phase-4 runner.

Focused executable regression:

```bash
python3 scripts/check_bh4_xpollenation.py
```

## ITIR/IPFS projection

Each reaction neighbourhood can be projected without changing its meaning:

```bash
python -m itir_jmd_bridge emit-xpollenation-artifact \
  --input artifacts/biology/xpollenation-neighbourhoods/RHEA-19897.json \
  --artifact-id xpollenation:bh4:RHEA-19897 \
  --output artifacts/biology/RHEA-19897.shared-shard.json
```

Existing ITIR publishing can then attach `file://`, `hf://` or `ipfs://CID` refs and emit the existing artifact-resolution receipt.

## DA51

No new DA51 type or reaction-address semantics are invented in this tranche. The repository store accepts an optional canonical DA51 join when an address has been allocated by the existing DA51 owner. A Rhea identifier, QID, CID or numerical match cannot manufacture a DA51 address.

## Scientific firewall

```text
Rhea identity != in-vivo flux identity
same Rhea column != same NOS isoform/context
ChEBI cross-reference != compartment identity
UniProt identity != enzyme abundance/state
PDB/SIFTS mapping != catalytic mechanism
SABIO mapping != kinetic payment
QID exact identity != assay applicability
CID != kinetic admissibility
OEIS numerical match != biochemical identity
xPollenation neighbourhood != flux interval
```

The existing four gates remain independently required:

1. same-assay reaction identity;
2. same-object / compartment / time translation;
3. normalized solver flux units;
4. justified kinetic-parameter-to-network-flux translation.

## Cross-domain extension

The generic owner `DASHI.Core.XPollenationExact` includes namespaces/relations for QID, ChEBI, Rhea, UniProt, PDB, SABIO, PubMed, DOI, PubChem and OEIS. OEIS is intended for numerical-feature/sequence edges and remains behind the same non-equivalence firewall; it is not automatically traversed from biochemical identifiers.
