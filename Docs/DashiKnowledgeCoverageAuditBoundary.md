# DASHI knowledge-coverage audit boundary

## Current conclusions from the repository-wide Dewey projection

The Dewey projection gives **full mechanical parent-cluster classification coverage**:

- 15,796 / 15,796 Agda modules classified;
- 3,696 modules contain observed DOI text;
- 1,179 distinct DOI strings are indexed.

Therefore the repository is strong in **classification coverage**, but DOI-bearing module density is only about **23.4%**.  This does not mean the remaining modules have no source; it means no DOI string was observed in those modules by that scanner.

The largest known parent clusters are currently:

| Dewey | Cluster | Modules | What this establishes |
|---|---|---:|---|
| `532.051` | Navier-Stokes closure | 5,218 | very strong formal-volume concentration |
| `530.144` | Yang-Mills | 2,589 | very strong formal-volume concentration |
| `153.420` | PNF cognition | 622 | substantial formal-volume concentration |
| `570.000` | General biology | 531 | substantial formal-volume concentration |
| `340.000` | Law | 217 | smaller but established domain cluster |
| `004.650` | Interoperability | 201 | smaller but established cross-domain cluster |

These counts alone do **not** establish which of these clusters has stronger DOI or QID coverage.

## QID status

`DASHI.Wikimedia.ScientificReferenceEntityAtlasExact` already provides targeted verified/unresolved QID identities and explicitly keeps QIDs below theorem/source authority.

Repository-wide QID density is a separate measurement.  `scripts/build_qid_coverage_index.py` now scans every Agda module for observed QID tokens and, when the Dewey module catalogue is present, emits:

- `Docs/DashiQidModuleCatalog.tsv`;
- `Docs/DashiQidParentClusterCoverage.tsv`.

`scripts/build_dewey_qid_coverage_report.py` consumes that cluster table and emits the ranked strong/weak audit.  The rank keeps four coordinates separate:

1. module volume;
2. DOI module density;
3. QID module density;
4. joint DOI+QID module density.

The report intentionally does not average these into theorem status.

## Wikipedia first-link graph

The relevant English-network paper is:

Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds, **Connecting every bit of knowledge: The structure of Wikipedia's First Link Network**, *Journal of Computational Science* 19 (2017), 21-30, DOI `10.1016/j.jocs.2016.12.001`.

It built the first-link directed graph from roughly 4.7 million English Wikipedia articles.  Philosophy directed more paths than any other article by two orders of magnitude.  The paper also explicitly limits the result to one language, one Wikipedia snapshot, and one first-link selection rule.

The multilingual comparison is:

Maxime Gabella, **Cultural Structures of Knowledge from Wikipedia Networks of First Links**, *IEEE Transactions on Network Science and Engineering* 6(3) (2019), 249-252, DOI `10.1109/TNSE.2018.2812788`.

It finds culturally different first-link cores: Philosophy/Science-like central concepts in European-language editions and Human/Earth-like concepts in East-Asian editions.

`DASHI.Wikimedia.WikipediaFirstLinkNetworkExact` therefore indexes first-link observations by language, snapshot/revision, link-selection rule and parser policy.  First-link reachability is navigation topology, not theorem authority, source truth or semantic dependence.

## Highest-alpha enrichment order

Once the joined coverage table is generated on the exact Dewey checkout, enrichment should be prioritized by **large module count + low joint DOI/QID density**.  This targets the largest graph-addressability holes first instead of spending cycles perfecting tiny clusters.

The expected workflow is:

```text
build_dewey_cluster_index.py
        -> DashiDeweyModuleCatalog.tsv
build_qid_coverage_index.py
        -> DashiQidParentClusterCoverage.tsv
build_dewey_qid_coverage_report.py
        -> DashiKnowledgeCoverageAudit.md
```

The generated report, not this boundary note, is the authority for per-cluster strong/weak metadata rankings.
