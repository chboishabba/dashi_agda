# Cabarlah–Palestine Provenance Formalism

## Purpose

This tranche formalises the corrected Cabarlah discussion while preventing the earlier speculative synthesis from being promoted to history.

The central separation is:

```text
World War II:
  alleged Brisbane Line / Japanese invasion / Cabarlah latitude coincidence

Postwar Cold War:
  Borneo Barracks and Cabarlah signals intelligence / communist and other regional forces

Settler-colonial comparison:
  Palestine–Amalek rhetoric / Indigenous dispossession / logic of elimination

Contemporary intelligence protest:
  Pine Gap on Arrernte Country / land return / Palestine solidarity

Toponymy:
  unknown Indigenous spoken form / lossy colonial transcription / conventional Cabarlah spelling
```

No theorem identifies these layers.  Their exact interaction is a typed palimpsest with explicit evidence status and non-collapse proofs.

## Claim-status algebra

`CabarlahClaimStatusExact.agda` defines:

```text
EvidenceStatus =
  documented | conventional | derived | contested | underdetermined | refuted
```

and assigns status to the central claims.  In particular:

```text
Capbarlah as a historical spelling                    = refuted
Cabarlah as a communist territorial concession line  = refuted
exact Indigenous source pronunciation                 = underdetermined
fixed official Brisbane surrender line                = contested
postwar Cabarlah signals-intelligence role            = documented
Pine Gap protest coupling land return and Palestine   = documented
```

The correction is machine-visible rather than left as prose.

## Corrected historical layers

`CabarlahHistoricalLayerExact.agda` proves exact integer arithmetic for the approximate latitude comparison:

```text
274261 + 444 = 274705
111 * 444 = 49284
```

The second equality corresponds to `4.9284 km` when the coordinate unit is one ten-thousandth of a degree and the declared approximation is `111 km/degree`.

This is a coordinate calibration only.  It does not prove that an official line passed through Cabarlah.

The module then distinguishes:

```text
worldWarTwoTrainingPeriod -> imperialJapan
postwarSignalsPeriod      -> coldWarCommunistForces
```

and proves the periods and enemies are not equal.  The alleged Brisbane Line claim carries `contested` status; the communist-Cabarlah territorial claim carries `refuted` status.

## Lossy toponym transcription

`CabarlahToponymTranscriptionExact.agda` treats the conventional spelling as a lossy observation.

Four orthography-based hypotheses are retained:

```text
/kabala/  /kabarla/  /gabala/  /gabarla/
```

They are explicitly not certified Jarowair or Wakka lexical forms.  All four map to the conventional English spelling `Cabarlah`, and the map is proved non-injective.

```text
source sound candidate -> colonial rendering
```

therefore has no unique inverse in the finite model.

The representation chain is:

```text
Country
-> unknown spoken source
-> conventional English name
-> military institutional address
```

with proofs that Country, spoken source, and conventional name are distinct carriers.

## Enemy abstraction and Amalek

`SettlerEnemyAbstractionExact.agda` models the information loss created by an absolute-enemy category.  In the declared rhetorical model:

```text
Hamas actor + Palestinian civilian population -> Amalek category
Malayan communist forces + heterogeneous anti-colonial movements
  -> global communism category
```

The module proves the compression is non-injective.  This is a theorem about the danger of the rhetoric, not an endorsement of either classification.

It also distinguishes:

```text
explicit lexical use
!=
structural homology only
```

The Palestine/Amalek lane is represented as explicit political-theological rhetoric.  The Indigenous-Australian comparison is structural only: the repository does not claim that settlers at Cabarlah literally used the word `Amalek`.

The finite eliminatory framing is:

```text
prior sovereignty
-> constituted as obstacle
-> represented as removable
```

It describes the settler frame and supplies no justification for it.

## Pine Gap and Borneo Barracks

`IndigenousMilitaryIntelligenceCircuitExact.agda` proves:

```text
Pine Gap != Borneo Barracks
joint global strategic intelligence != Australian regional EW/SIGINT
Arrernte Country != Cabarlah underlying Country
```

while retaining the shared abstract circuit:

```text
Indigenous Country
-> military installation
-> remote conflict made legible
```

The exact Pine Gap protest demand list contains both:

```text
return Arrernte land
end Palestine complicity
```

The open-source operational status remains `protestAllegationAndStructuralConcern`, not `publiclyVerifiedSpecificStrikeLink`.

## Frontier paradox and permanent enemy effect

`FrontierEnemyPersistenceExact.agda` salvages the valid generic mathematics from the superseded terminal-concession draft.

The frontier paradox is represented exactly by:

```text
includedInProtectedCore = false
requiredForCoreSecurity = true
```

The permanent-enemy effect distinguishes a concrete actor from an abstract recurring category.  Two different concrete epochs can map to the same abstract category, so defeating one actor does not definitionally dissolve the category.

```text
abstract enemy
-> permanent frontier
-> permanent surveillance
-> permanent mobilisation
```

is implemented as a finite transition system.  No concrete historical instance follows automatically from this generic carrier.

## Provenance

`CabarlahPalestineSourceAtlas.agda` records nine bounded sources with authors, titles, venues, years, identifiers, imported roles, and excluded promotions.

DOIs are attached where assigned:

- Patrick Wolfe, *Settler Colonialism and the Elimination of the Native*, DOI `10.1080/14623520601056240`;
- Abed Azzam, *Blot Out the Memory of Amalek from Under Heaven: The Gaza Genocide and the Political Theological Legacy of the Biblical Amalek*, DOI `10.1515/auk-2025-2018`;
- Suzanne Kite and S. A. Wurm, *The Duungidjawu Language of Southeast Queensland: Grammar, Texts and Vocabulary*, DOI `10.15144/PL-553`.

Government, library, database, and journalism sources carry explicit no-DOI markers rather than fabricated identifiers.

## Integrated authority boundary

`CabarlahPalestineBoundary.agda` assembles the exact results and blocks the following promotions:

```text
Capbarlah typo -> semantic etymology
latitude coincidence -> official military line
postwar SIGINT role -> communist territorial concession
conventional name -> preserved Indigenous authority
structural analogy -> identical histories
protest concern -> verified strike-level intelligence chain
```

The corrected coalescence is therefore:

```text
Cabarlah
=
  Indigenous-derived conventional name
  + WWII military locality near the Brisbane parallel
  + postwar SIGINT/EW institution
  + settler-colonial palimpsest
```

where `+` means layered coexistence, not equality of histories or causal mechanisms.

## Validation

The focused checker is:

```bash
AGDA_JOBS=1 bash scripts/check_cabarlah_palestine_formalism.sh
```

It cascades through the complete Round Five checker, rejects holes, top-level postulates, unsafe options, unsolved metas, and placeholder right-hand sides, then checks the regression and aggregate foundations roots with the pinned Agda 2.9 toolchain.
