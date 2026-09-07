# Scientific reference QID atlas

Date: `2026-09-08`
Status: source-identity enrichment; QIDs are metadata, not theorem/source authority.

## Identity rule

For scientific publications, the DOI/arXiv/official-source locator remains the primary bibliographic identity. Wikidata QIDs bind related people, projects, concepts, institutions, or a publication only when an exact publication item is independently verified.

`QID != DOI != theorem identity != source authority != proof payment`.

Name equality is insufficient to resolve an ambiguous or missing QID.

## Yang--Mills / constructive QFT

| Reference | Primary source identity | Related entities | Status |
| --- | --- | --- | --- |
| Jaffe--Witten Clay Yang--Mills problem | official CMI problem statement | Arthur Jaffe `Q370094`; Edward Witten `Q201513`; Millennium Prize Problems `Q727000` | verified related identities |
| Faddeev--Popov 1967 | DOI `10.1016/0370-2693(67)90067-6` | Ludvig Faddeev `Q1030228`; Victor Popov `Q462638`; gauge fixing `Q832289` | verified related identities; no article QID asserted |
| Federbush, Phase Cell IV | DOI `10.1007/BF01225039` | Paul G. Federbush `Q102115681` | verified person; no article QID asserted |
| Osterwalder--Schrader 1973/1975 | exact bibliography entries remain primary | Konrad Osterwalder `Q125728`; Robert Schrader unresolved | mixed |
| Gross--Wilczek 1973 | exact bibliography entry remains primary | David Gross `Q40262`; Frank Wilczek `Q107450` | verified people |
| Politzer 1973 | exact bibliography entry remains primary | Hugh David Politzer `Q107407` | verified person |
| Seiler 1982 | exact bibliography entry remains primary | Erhard Seiler `Q74323177` | verified person |
| Bałaban 1987/1988 family | DOI/bibliography remains primary per consuming module | Tadeusz Bałaban unresolved | intentionally unresolved |

## Navier--Stokes

| Reference | Primary source identity | Related entities | Status |
| --- | --- | --- | --- |
| Caffarelli--Kohn--Nirenberg | DOI `10.1002/cpa.3160350604` | Luis Caffarelli `Q1076636`; Robert V. Kohn unresolved; Louis Nirenberg `Q596590`; Navier--Stokes equations `Q201321` | mixed |
| Leray--Hopf | exact bibliography/source family | Jean Leray `Q441143`; Eberhard Hopf `Q86070`; Navier--Stokes equations `Q201321` | verified related identities |
| Beale--Kato--Majda | exact criterion publication remains primary | James Thomas Beale unresolved; Tosio Kato `Q1335673`; Andrew Majda `Q506133` | mixed |
| Coifman--Meyer | exact bibliography/source family | Ronald Coifman `Q2165588`; Yves Meyer `Q574597` | verified people |
| Lei--Ren--Tian 2025 | exact bibliography entry remains primary | Zhen Lei unresolved; Xiao Ren unresolved; Gang Tian `Q942908` | mixed |
| Escauriaza--Seregin--Šverák 2003 | exact bibliography entry remains primary | Luis Escauriaza unresolved; Gregory Seregin unresolved; Vladimír Šverák `Q1593578` | mixed |

### Citation drift found

Three current NS modules label DOI `10.1080/03605308208820218` as Caffarelli--Kohn--Nirenberg. Publisher metadata identifies that DOI as Fabes--Kenig--Serapioni, *The local regularity of solutions of degenerate elliptic equations*. The canonical CKN DOI is `10.1002/cpa.3160350604`.

Affected comments:

- `DASHI/Physics/Closure/NSTriadKNYuFiniteLocalizationAbsorptionExact.agda`
- `DASHI/Physics/Closure/NSTriadKNYuLocalizationTailCriterionExact.agda`
- `DASHI/Physics/Closure/NSTriadKNYuLocalizationCaccioppoliTailExact.agda`

This is recorded formally in `NavierStokesCitationIdentityAuditExact.agda`. QID alignment does not repair a wrong DOI.

## Riemann hypothesis / de Bruijn--Newman

| Reference | Primary source identity | Related entities | Status |
| --- | --- | --- | --- |
| Riemann 1859 | original 1859 paper | Bernhard Riemann `Q42299`; Riemann hypothesis `Q205966` | verified related identities |
| Polymath 2019 | DOI `10.1007/s40687-019-0193-1`; arXiv `1904.12438` | Polymath Project `Q2000812`; Riemann hypothesis `Q205966`; de Bruijn `Q1078285`; Newman `Q5080476` | verified related identities; no article QID asserted |
| Platt--Trudgian 2021 | DOI `10.1112/blms.12460` | Timothy Trudgian `Q132064015`; Dave Platt unresolved; Riemann hypothesis `Q205966` | mixed |
| Gomila 2026 candidate audit | public GitHub audit repository | Jude Gomila unresolved; Riemann hypothesis `Q205966` | candidate provenance only |
| Bombieri CMI RH exposition | official CMI problem description | Enrico Bombieri `Q333538`; Millennium Prize Problems `Q727000`; Riemann hypothesis `Q205966` | verified related identities |
| Alpöge--Furman simple-zero source | exact bibliography entry remains primary | Levent Alpöge `Q102078476`; Ralph Furman unresolved | mixed |
| Weil explicit-formula family | exact consuming bibliography remains primary | André Weil `Q323232` | verified person |
| Borcherds moonshine cross-context | DOI `10.1007/BF01232032` | Richard Borcherds `Q334010` | verified person |

## Formal owners

- `DASHI/Wikimedia/ScientificReferenceEntityAtlasExact.agda`
- `DASHI/Wikimedia/ScientificCitationQidBindingsExact.agda`
- `DASHI/Physics/YangMills/SourceEntityQidBindingsExact.agda`
- `DASHI/Physics/Closure/NavierStokesSourceEntityQidBindingsExact.agda`
- `DASHI/Physics/Closure/NavierStokesCitationIdentityAuditExact.agda`
- `DASHI/Analysis/RiemannSourceEntityQidBindingsExact.agda`
- `DASHI/Analysis/RiemannExtendedSourceEntityQidBindingsExact.agda`
- `DASHI/Wikimedia/ScientificReferenceQidValidation.agda`
- `DASHI/EverythingScientificReferenceQidAtlas.agda`

## Next expansion

Continue the same process for GR, QFT, Monster/Moonshine, spectral theory, and cross-domain source owners. Prefer exact DOI/arXiv/title identity first, then attach verified QIDs for related entities. Publication-level QIDs should be added only when the exact publication item is independently matched to its bibliographic identifier.
