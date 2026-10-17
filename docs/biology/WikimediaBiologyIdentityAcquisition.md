# Wikimedia biological identity acquisition

## Purpose

This lane cross-pollinates the exact UniProt/BH4 panel with the repository's
existing Wikimedia external-identity machinery.  It is an identity/provenance
lane, not a new biological-evidence authority.

The canonical path is deliberately typed:

```text
gene QID --P688 encodes--> protein QID --P352 UniProt protein ID--> accession
         <--P702 encoded by--
                              |
                              +-- optional enwiki sitelink -> page id/revision
```

Gene and protein QIDs must not be interchanged.  A Wikipedia article may also
cover a gene, protein, pathway or blended topic, so its title is not itself a
same-object witness.

## Acquisition

The BH4 panel is imported directly from `scripts/acquire_uniprot_bio_certificate.py`
so the Wikimedia and UniProt lanes share one accession owner.

```bash
python3 scripts/acquire_wikimedia_bio_identity.py --kitzerow-bh4-panel \
  -o artifacts/biology/wikimedia-kitzerow-bh4-identity.json
```

For one protein:

```bash
python3 scripts/acquire_wikimedia_bio_identity.py P09417 --symbol QDPR
```

Resolution uses an exact Wikidata Query Service lookup for `wdt:P352` followed
by `wbgetentities` verification of the returned item's P352 claim.  Text search
is recorded only as diagnostic provenance and never establishes identity.

For each exact protein item the certificate records:

- Wikidata QID and current entity revision;
- SHA-256 of the entity API response;
- all P352 values and the exact-match bit;
- P702 `encoded by` gene QIDs;
- P703 taxon QIDs and a human-Q5 check;
- reciprocal P688 `encodes` checks on each gene item;
- English-Wikipedia sitelink, page id and revision when present;
- enwiki pageprops QID round-trip check;
- SHA-256 of the enwiki metadata response;
- explicit non-promotion boundaries.

Ambiguous P352 matches remain `ambiguous`; no match remains `unresolved`; API
failure remains `acquisition-error`.  None is silently rewritten as biological
absence.

## Inspected 2026-10-17 seeds

The formal owner records only coordinates that were directly inspected before
this pass, while the executable resolver owns complete-panel refresh:

| symbol | UniProt | inspected Wikidata coordinate | role |
|---|---|---|---|
| GCH1 | P30793 | Q1487359 | protein item |
| SPR | P35270 | Q409532 | protein item |
| PAH | P00439 | Q420604 | protein item |
| TH | P07101 | Q420766 | protein item |
| MTOR | P42345 | Q21115057 | protein item |
| QDPR | P09417 | Q14884995 | **gene** item; not promoted to protein QID |
| PCBD1 | P61457 | Q18030367 | **gene** item; not promoted to protein QID |
| NOS1 | P29475 | Q18030177 | **gene** item; not promoted to protein QID |

The gene examples are intentionally retained because they demonstrate the
wrong-type failure mode that a symbol/search-based resolver would otherwise
hide.

## Formal boundaries

`DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact` reuses
`SnowballExternalIdentityAvailabilityExact`.  It states that:

- QID resolution is supplemental identity/provenance, not semantic authority;
- a gene QID cannot stand in for a protein QID without the P688/P702 relation;
- even an exact P352 match does not prove sequence equality independently of the
  UniProt sequence receipt;
- Wikidata statements do not become primary biochemical evidence;
- Wikipedia narrative does not become mechanistic evidence;
- Wikimedia coverage does not confirm the Kitzerow whole graph;
- unresolved QID does not imply protein nonexistence.

Focused validation:

```bash
python3 scripts/check_bh4_wikimedia_identity.py
```
