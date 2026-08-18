# Wikidata working-group handoff: BFO entity scope, mapping licences, and higher-order context

This note records the ontology-facing consequences of the broader DASHI fibre/PNF work. It is intentionally smaller than the governance/369 research surface, but it preserves the full distinctions needed by the current Wikidata/BFO discussion.

## 1. `entity` is not enough to identify ontology scope

The current discussion distinguishes:

- `Q35120` — the broad Wikidata/OWL-root-facing `entity` item;
- `Q136433660` — the BFO `Entity`-facing item (`BFO_0000001`).

Both can present the English label `entity`. DASHI therefore treats label equality as a projection collision, not as ontology identity.

The formal regression proves that no function from the public label alone can simultaneously reconstruct both declared root scopes.

Operationally the useful carrier is:

`BFO-applicable entities ⊆ broad Wikidata entity carrier`, 

without claiming that this inclusion settles the metaphysics of existence or the final interpretation of every fictional, imagined, mathematical, or informational object.

## 2. Keep BFO mapping mechanisms typed — and query-indexed

The current Wikidata BFO project surface exposes several distinct mapping mechanisms:

- `P12602` — BFO class ID (external identifier);
- `P2888` — exact match;
- `P1709` — equivalent class;
- `P279` — Wikidata subclass relation.

The key boundary is:

`identifier correspondence != exact semantic match != equivalent class != subclass relation`.

The implementation goes further than merely assigning four labels. It gives each property a query-specific inference profile. In the deliberately narrow working-group contract:

- `P12602` licenses identifier lookup;
- `P2888` supplies semantic-interchange evidence;
- `P1709` supplies class-equivalence evidence;
- `P279` supplies subclass reasoning.

This means there is no single scalar “mapping strength” ordering. For example, `P2888` and `P1709` are incomparable when the query language distinguishes semantic interchange from class equivalence: each licenses a query that the other does not.

No one listed property type by itself licenses transport of a disjointness theorem. Disjointness transport remains a separate proof obligation over source class algebra, correspondence/alignment, and target class algebra.

## 3. The Q35120 / BFO_0000001 situation is a diagnostic packet, not something to normalize away

Current surfaces expose both:

- a `P12602` documentation/example history associating `Q35120` with BFO identifier `0000001`;
- a distinct BFO-facing item `Q136433660`, modelled below `Q35120`, with the BFO continuant/occurrent partition attached locally to the BFO root.

DASHI therefore represents both as candidate observations. A packet with both candidates is not allowed to self-promote to one unique semantic root.

The layered diagnostic separates:

- source ontology status;
- Wikidata transcription/property-documentation status;
- cross-ontology alignment status;
- target graph status.

The canonical bounded result is:

`source verified / transcription ambiguous / alignment unresolved / target graph verified / final unresolved`.

The important non-collapse rule is:

`transcription ambiguity != BFO contradiction != Wikidata contradiction`.

This is exactly the provenance-local attribution discipline used elsewhere in the repository.

## 4. “fictional second-order class” factors into more than two readings

Wikidata defines second-order class by order of predication: its instances are first-order classes. That coordinate does not determine fictional status.

At least three semantically different readings can share the phrase `fictional second-order class`:

1. **editorial/metamodel class about fiction** — a real modelling class whose members are classes used to organise fictional material;
2. **in-world second-order class** — a higher-order class interpreted as existing according to a fictional world;
3. **class of classes whose instances are fictional individuals** — the metaclass itself need not be an in-world fictional entity; rather its member classes classify fictional individuals.

The DASHI carrier therefore separates:

- class order;
- narrative/domain status;
- current inspection applicability;
- provenance.

Three countermodel states can have the same public label `fictional second-order class` and the same `secondOrder` coordinate while differing on narrative semantics. Two can be applicable at the current comparison level while another requires recharting. Thus neither the label nor class order alone can determine narrative semantics or the appropriate inspection decision.

The live Wikidata calibration is deliberately kept separate from the theorem semantics. `Q17305127` (`fictional profession`) is currently typed as `class of fictional entities`, `fictional metaclass`, and `fictional second-order class`; the generated higher-order problem reports also contain fictional metaclass/fixed-order patterns. These are useful test cases, not proof that one interpretation of the phrase is canonically correct.

## 5. Binary truth is not the right carrier for ontology applicability

The implementation does **not** claim that OWL or Wikidata uses a ternary DASHI logic. The narrower theorem is:

`not known true != known false`.

Once ontology applicability is included, the current inspection can distinguish:

- supported yes;
- supported no;
- not established;
- outside the currently committed ontology scope;
- conflicting derivations.

The safe polarity view therefore permits:

- `supported yes` → positive only;
- `supported no` → negative only;
- `not established` → neither;
- `outside scope` → neither at the current level;
- `conflicting derivations` → both.

So neither `not established` nor `outside scope` can be silently converted into falsehood, and conflict cannot be collapsed into ordinary uncertainty.

## 6. Frodo-style example: preserve the referent while changing inspection level

The formal example deliberately avoids asserting a final BFO classification for Frodo. Instead it uses one unchanged referent through a ladder of questions:

`Frodo @ Wikidata-entity level`

→ `Frodo @ BFO-Entity level`

→ `Frodo @ BFO continuant/occurrent-partition level`.

The example assigns different local evaluation states to those questions while proving that the referent and provenance survive the level transports exactly.

This is the ontology instance of the existing PNF rule:

`NO_TYPED_MEET / outside-scope / collapsed-required-coordinate != global falsity`.

The whole claim can remain in the fibre and be re-inspected at another ontology level rather than being destroyed or converted into a Boolean answer merely because the current level cannot decide it.

## 7. Source calibration

Current project/documentation surfaces used for this tranche:

- Wikidata WikiProject Ontology, **Mapping Wikidata To BFO** — community project documentation; no DOI.
- Wikidata, **Property:P2888 — exact match** — property documentation; no DOI.
- Wikidata, **Property talk:P12602 — BFO class ID** — property documentation; no DOI.
- Wikidata WikiProject Ontology, **Class Order** and `Q24017414` second-order class — community ontology documentation; no DOI.
- Wikidata, `Q35120`, `Q136433660`, and `Talk:Q136433660` — live data/discussion surfaces; no DOI.
- Wikidata, `Q17305127` and generated higher-order problem reports — live modelling/regression surfaces; no DOI.

These sources calibrate the current Wikidata modelling surface. The factorisation, non-reconstruction, applicability, and query-indexed inference theorems are DASHI-local constructions; they are not attributed to the editors of those pages.

## 8. Focused Agda surface

- `DASHI.Ontology.WikidataBFOEntityScopeExact`
- `DASHI.Ontology.WikidataBFOMappingInferenceLatticeExact`
- `DASHI.Ontology.WikidataBFOApplicabilityFibreExact`
- `DASHI.Ontology.WikidataBFOEntityRootMappingDiagnosticExact`
- `DASHI.Ontology.WikidataHigherOrderFictionContextExact`
- `DASHI.Ontology.WikidataWorkingGroupEntityScopeRegression`
- `DASHI.Ontology.WikidataWorkingGroupEverything`

The last module also imports the existing `LeanWikidataEverything` JMD theorem-contract surface, so the working-group handoff does not need to import the full justice/governance stack.
