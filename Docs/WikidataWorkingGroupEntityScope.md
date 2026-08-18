# Wikidata working-group handoff: BFO entity scope and higher-order class context

This note records the narrow ontology-facing consequences of the broader DASHI fibre/PNF work.  It is intentionally smaller than the governance/369 research surface.

## 1. `entity` is not enough to identify ontology scope

The current discussion distinguishes:

- `Q35120` — the broad Wikidata/OWL-root-facing `entity` item;
- `Q136433660` — the BFO `Entity`-facing item (`BFO_0000001`).

Both can present the English label `entity`.  DASHI therefore treats label equality as a projection collision, not as ontology identity.

The formal regression proves that no function from the public label alone can simultaneously reconstruct both declared root scopes.

## 2. Keep BFO mapping mechanisms typed

The current Wikidata BFO project query exposes three distinct mapping surfaces:

- `P12602` — BFO class ID (external identifier);
- `P2888` — exact match;
- `P1709` — equivalent class.

The implementation additionally keeps `P279` subclassing distinct.

The key boundary is:

`identifier correspondence != exact semantic match != equivalent class != subclass relation`.

No one of those property types, by itself, licenses transport of a disjointness theorem.  Disjointness transport remains a separate proof obligation over the mapping and the source/target class algebra.

## 3. “fictional second-order class” factors into independent coordinates

Wikidata defines second-order class by order of predication: its instances are first-order classes.  That does not determine fictional status.

The DASHI carrier therefore separates:

- class order;
- narrative/domain status;
- current inspection applicability;
- provenance.

Two countermodel states can have the same public label `fictional second-order class` and the same second-order coordinate while differing between:

- an editorial/metamodel class *about* fictional classes;
- an in-world fictional higher-order interpretation.

One can be applicable at the current comparison level while the other must be recharted.  Thus neither the label nor class order alone can determine narrative semantics or the appropriate inspection decision.

This is the ontology instance of the existing PNF rule:

`NO_TYPED_MEET / outside-scope / collapsed-required-coordinate != global falsity`.

The whole argument and its provenance can remain in the fibre and be inspected at another level.

## 4. Source calibration

Current project/documentation surfaces used for this tranche:

- Wikidata WikiProject Ontology, **Mapping Wikidata To BFO** — community project documentation; no DOI.
- Wikidata, **Property talk:P12602 — BFO class ID** — property documentation; no DOI.
- Wikidata WikiProject Ontology, **Class Order** and `Q24017414` second-order class — community ontology documentation; no DOI.
- Wikidata, `Q35120`, `Q136433660`, and `Talk:Q136433660` — live data/discussion surfaces; no DOI.

These sources calibrate the current Wikidata modelling surface.  The factorisation and non-reconstruction theorems are DASHI-local constructions; they are not attributed to the editors of those pages.

## 5. Focused Agda surface

- `DASHI.Ontology.WikidataBFOEntityScopeExact`
- `DASHI.Ontology.WikidataHigherOrderFictionContextExact`
- `DASHI.Ontology.WikidataWorkingGroupEntityScopeRegression`
- `DASHI.Ontology.WikidataWorkingGroupEverything`

The last module also imports the existing `LeanWikidataEverything` JMD theorem-contract surface, so the working-group handoff does not need to import the full justice/governance stack.
