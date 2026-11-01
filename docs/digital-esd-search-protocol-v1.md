# Digital-ESD structured-search protocol v1

**Protocol version:** `digital-esd-search-v1-2026-09-16`

**Status:** planned and frozen before database execution. This appendix defines the platform-neutral concept blocks and query families. It does **not** claim that Scopus, Web of Science, ERIC, ACM Digital Library or IEEE Xplore translations have been executed. At execution, the exact platform-specific query, interface, date, result count and export must be retained verbatim.

## Concept blocks

### A — Digital education / educational technology

`("digital education" OR "digital learning" OR "educational technology" OR edtech OR "online learning" OR "blended learning" OR "digital learning platform*" OR "generative AI" OR GenAI OR "artificial intelligence")`

### B — Education for Sustainable Development / sustainability education

`("education for sustainable development" OR ESD OR "sustainable development education" OR "sustainability education" OR "environmental education" OR "sustainable education")`

Environmental education is retained as a related search family, not treated as definitionally identical to ESD.

### C — Educational transformation / institutional change

`(transform* OR "system change" OR institutional* OR "institutional change" OR "whole institution" OR curriculum OR pedagogy OR competenc* OR "learning environment*")`

### D — Sustainability of digital technology / lifecycle / circularity

`("life cycle assessment" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR "e-waste" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR "service life")`

### E — Participant agency / voice / governance

`("student voice" OR "learner voice" OR "learner agency" OR "student agency" OR participatory OR "participatory research" OR co-design OR codesign OR governance OR "public accountability")`

### F — Longitudinal / durability / institutionalisation

`(longitudinal OR long-term OR durability OR sustainab* OR institutionalisation OR institutionalization OR persistence OR retention OR follow-up OR "follow up")`

### G — Open/interoperable/repairable infrastructure

`(interoperab* OR "open standard*" OR "open source" OR OER OR "open educational resource*" OR portability OR migration OR export* OR "vendor lock-in" OR repairab* OR "right to repair")`

## Planned query families

| ID | Platform-neutral expression | Research purpose |
|---|---|---|
| Q1 | `A AND B` | Digital education/technology used in or for ESD and sustainability education |
| Q2 | `A AND B AND C` | Conditions linking digital education and ESD to pedagogical, curricular, institutional or system transformation |
| Q3 | `A AND D` | Environmental/material/lifecycle consequences and sustainability constraints on digital education itself |
| Q4 | `A AND B AND E` | Participant agency, student voice, co-design and governance in digital education and/or ESD |
| Q5 | `A AND B AND F` | Longitudinal, persistent and institutionalised effects or conditions in digital-ESD and adjacent evidence |
| Q6 | `A AND G` | Openness, interoperability, portability, vendor lock-in, repairability and infrastructure durability |

## Translation and execution rule

Each database translation is a distinct future receipt. The platform-neutral protocol must be translated using the database's current field syntax, controlled vocabulary, proximity operators, phrase rules, wildcard behaviour and filters. Any change required by a platform must be retained in the execution receipt rather than silently normalised after retrieval.

The execution record for each database must retain at minimum:

- protocol version;
- database/platform and interface;
- exact translated query or query set;
- execution date;
- applied fields/filters/limits;
- result count; and
- exported result-set reference.

A planned query is not an execution receipt. A successful search is not an included corpus. Search-term presence is not sufficient for eligibility. The dependent chain remains:

`database execution → retained export → deduplication → screening → structured extraction → source/scope synthesis`.
