# Situated Mole, Attribution, and Controlled Disclosure

## Scope

This tranche extends the focused cuisine formalism from a sensory and identity
kernel into an attributed, process-sensitive, socially situated knowledge
ecology.

The formal spine is:

```text
attributed sources
  -> order-sensitive material process
  -> situated ecological / labour / commensal world
  -> controlled-success and publicity boundary
  -> preservation archive
  -> governed public projection
```

The archive/publication distinction is deliberate:

```text
preserve reconstructible meaning != publish every preserved field
```

The repository contains only public candidate material. The controlled archive
surface is a reusable formal interface for future governed content; it does not
claim that restricted cultural knowledge has been acquired, copied, encrypted,
or authorised for storage.

## Reused repository structures

The implementation imports and bounds existing structures rather than creating
parallel theories:

- `DASHI.Core.GenericReceipt` for fail-closed receipts;
- `DASHI.Interop.SweetgrassCarrierSpine` for the explicitly attributed Robin
  Wall Kimmerer braid/fabric vocabulary;
- `DASHI.Culture.KnotWeaveTopologyCultureBridge` for bounded structural
  comparison without cultural-equivalence promotion;
- `DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge` for an explicit
  power-axis atlas and no-erasure gluing boundary;
- the existing `DASHI.Culture.Cuisine` sensory, provenance, identity, lineage,
  movement, and promotion surfaces.

`Sand Talk` remains an attributed historical entry point for PatternMind, but
PatternMind is treated as a comparison lens rather than a universal Indigenous
ontology.

## Reusable attribution

`DASHI.Core.AttributedSourceCore` centralises:

- author or institutional author;
- exact title;
- publication context and year;
- DOI state;
- canonical URL;
- source kind;
- bounded relationship to the formalisation;
- attribution visibility.

A citation imports neither a theorem nor authority. Domain atlases can reuse
this object without redeclaring bibliographic record types.

## Mole process architecture

`MoleProcessArchitecture` records:

- noncommuting process order through different indexed endpoints;
- ash as an irreversible process route, not an unhistoried ingredient;
- ingredient persistence after integration;
- a candidate multiphase state with service stability weaker than permanence;
- embodied observations as control inputs;
- explicit empirical, safety, regional-authenticity, and rheology residuals.

The finite coordinates are fixtures, not laboratory measurements.

## Situated world

`SituatedMoleWorld` keeps the plate connected to:

- milpa and wider food-system stages;
- seed, soil, water, seasonal, exchange, and ritual relations;
- knowledge transmission and adaptation;
- labour, compensation, ownership, attribution, decision power, and prestige;
- commercialisation and extraction risks;
- commensal allocation and reciprocity;
- Afro-Mexican memory alongside Indigenous, colonial, trade, household,
  regional, national, and diaspora lanes;
- intersectional food-power axes;
- representation authority indexed by actor, community, occasion, and time.

The formal boundary rejects any complete inverse from a finished plate back to
that world.

## Controlled success

`ControlledSuccessCore` combines four precedents without equating them:

- geographical-indication and collective-designation governance;
- multidimensional carrying capacity;
- burst-demand and visibility exposure;
- governed disclosure and no-contact protection.

Physical room is not enough: labour, ecological, social, ritual, and epistemic
capacity can each be the binding constraint. High or unknown publication risk
fails closed to `abstain`; controlled risk yields a limited projection.

Huitlacoche is retained as a candidate revalorisation case in which higher
market value may produce producer benefit or may produce gourmet capture,
standardisation, local-access loss, or prestige extraction. No outcome is
promoted without evidence.

## Preservation and publication

`ControlledDisclosureCore` supplies only the compact reusable objects needed
now:

- `FullArchive`;
- `ProjectionPolicy`;
- `PublicArtifact`;
- `PublicationReceipt`;
- typed disclosure actions and levels.

`CuisineKnowledgeEcology` constructs a small public example showing that an
attributed public view can be generated reproducibly from a declared policy.
It does not claim cryptographic custody, complete non-leakage, community
consent, or secure restricted-content handling.

### Current implementation boundary

The current repository closes the semantic and attribution interface only.
Future confidential deployment may add encryption, threshold custody, clean
export builds, metadata scrubbing, and recovery exercises behind the same
`FullArchive` and `ProjectionPolicy` boundary. None of those mechanisms is a
precondition for ordinary public-domain cuisine formalisation, and domain
modules do not need to reproduce their boilerplate.

## Attributed source atlas

`CuisineKnowledgeSourceAtlas` records twenty-two bounded sources spanning:

- Eric Phanngavong's practitioner chapter, *The Architecture of Ash*;
- Maria del Carmen Castillo Cisneros, *En mi mero mole*, DOI
  `10.31644/ED.V8.N1.2021.A07`;
- Renata E. Hryciuk, *Alquimista de los Sabores*, DOI
  `10.36551/2081-1160.2019.24.75-100`;
- Lilia Hernandez Albarran on food culture and ethnophagy;
- Giobanna Buenahora on silenced Afro-Mexican culinary experience;
- Jeffrey M. Pilcher's mole digital history chapter, DOI
  `10.1093/9780190622138.003.0014`;
- Sarah Bak-Geller and Grecia Cuevas on food sovereignty;
- Robin Wall Kimmerer and Tyson Yunkaporta;
- UNESCO, INAH, CONABIO, geographical-indication, Champagne, visitor-capacity,
  and voluntary-isolation sources;
- food-fluid mechanics and suspension-rheology sources;
- batch-arrival queueing analysis.

A missing DOI is atlas-local only. Inclusion does not imply agreement,
endorsement, exhaustive coverage, or authority promotion.

## Validation

Focused validation consists of:

```text
python3 scripts/check_situated_mole_preservation.py
agda -i . DASHI/Culture/Cuisine/Everything.agda
```

`DASHI.EverythingCuisineExtension` provides a lightweight compatibility bridge
between the repository aggregate and the focused cuisine aggregate without
requiring this tranche to rewrite the very large root import file.
