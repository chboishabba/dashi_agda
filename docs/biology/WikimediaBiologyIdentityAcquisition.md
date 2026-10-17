# Wikimedia biological identity acquisition

## Purpose

This lane cross-pollinates the exact UniProt/BH4 panel with the repository's
existing Wikimedia external-identity machinery. It is an identity/provenance
lane, not a new biological-evidence authority.

```text
gene QID --P688 encodes--> protein QID --P352 UniProt protein ID--> accession
         <--P702 encoded by--
                              |
                              +-- optional enwiki sitelink -> page id/revision
```

Gene and protein QIDs must not be interchanged. A Wikipedia article may cover a
gene, protein, pathway or blended topic, so its title is not itself a same-object
witness.

## Acquisition

The BH4 panel is imported directly from `scripts/acquire_uniprot_bio_certificate.py`
so the Wikimedia and UniProt lanes share one accession owner.

```bash
python3 scripts/acquire_wikimedia_bio_identity.py --kitzerow-bh4-panel \
  -o artifacts/biology/wikimedia-kitzerow-bh4-identity.json
```

Resolution uses exact WDQS `wdt:P352` lookup followed by `wbgetentities`
verification. The acquirer uses a Wikimedia-compliant identifying User-Agent,
429 exponential backoff, paced panel polling and live progress reporting. Text
search is retained only as diagnostic provenance.

## Executed panel, 2026-10-17

The completed acquisition returned 15 unique exact protein-QID resolutions, one
true ambiguity, zero unresolved members and zero acquisition errors. All 16
protein/gene relations paid the reciprocal P702/P688 witness. Seven of 16
proteins have a direct English-Wikipedia protein-level sitelink.

| symbol | UniProt | protein QID(s) | encoding gene QID | protein enwiki |
|---|---|---|---|---|
| GCH1 | P30793 | Q1487359 | Q14916168 | GTP cyclohydrolase I |
| GCHFR | P30047 | Q21101579 | Q18025609 | none |
| PTS | Q03393 | Q21106788 | Q7121042 | none |
| SPR | P35270 | Q409532 | Q15331000 | Sepiapterin reductase |
| PCBD1 | P61457 | Q21204380 | Q18030367 | none |
| QDPR | P09417 | **Q21145902, Q7265406** | Q14884995 | none |
| NOS1 | P29475 | Q21121716 | Q18030177 | none |
| NOS2 | P35228 | Q21114547 | Q18030178 | none |
| NOS3 | P29474 | Q408853 | Q15328584 | Endothelial NOS |
| PAH | P00439 | Q420604 | Q14851781 | Phenylalanine hydroxylase |
| TH | P07101 | Q420766 | Q18254977 | Tyrosine hydroxylase |
| TPH1 | P17752 | Q21125451 | Q18032077 | none |
| TPH2 | Q8IWU9 | Q21125466 | Q18049432 | none |
| AGMO | Q6ZNB7 | Q22680132 | Q18057391 | none |
| TSC2 | P49815 | Q21109261 | Q18032199 | TSC2 |
| MTOR | P42345 | **Q285613** | Q14876086 | MTOR |

The executable acquisition supersedes preliminary hand-seeded coordinates where
they disagree. In particular, the earlier MTOR seed Q21115057 is not retained as
the exact P352=P42345 protein identity; the acquired exact coordinate is Q285613.

### QDPR ambiguity

QDPR is not unresolved. Wikidata contains two distinct items carrying exact
`P352 = P09417`, Q21145902 and Q7265406. The QDPR gene item Q14884995 has P688
links back to both. DASHI therefore records `ambiguousExact` and refuses to
choose or merge the two without a stronger same-object/adjudication witness.

This is the only live QID-uniqueness residual in the 16-member panel.

### Wikipedia coverage

Only seven proteins have direct protein-level English-Wikipedia sitelinks. The
other nine are coverage gaps, not protein-identity failures. Gene items may have
public narrative coverage independently, preserving the firewall

```text
gene QID != protein QID != enwiki page identity.
```

## Formal owner

`DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact` now contains the executed
16-member receipt surface, the 15/1/0/0 summary, the QDPR ambiguity pair, all
encoding-gene QIDs, reciprocal relation bits and the 7/16 Wikipedia-coverage
summary.

Its Wikimedia-only live residuals are:

1. adjudicate the two QDPR exact-P352 items if a unique public QID is required;
2. inspect the nine missing protein-level enwiki sitelinks if narrative coverage
   is useful.

Neither blocks the byte-pinned UniProt panel or the biochemical proof graph.

The formal firewalls state that QIDs do not create sequence identity, Wikidata
does not create biological truth, Wikipedia narrative does not create mechanism,
reciprocal P688/P702 does not create mechanistic support, missing enwiki coverage
does not mean protein absence, and duplicate exact-P352 items may not be silently
collapsed.

Focused validation:

```bash
python3 scripts/check_bh4_wikimedia_identity.py
python3 scripts/check_kitzerow_bh4_priority.py
```
