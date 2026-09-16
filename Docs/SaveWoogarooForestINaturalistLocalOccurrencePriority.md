# Save Woogaroo Forest — iNaturalist local occurrence priority audit

## Corpus basis

This note uses the observer-supplied saved iNaturalist pages for `johl1`. Native observation IDs were deduplicated across the three saved pages.

Current corpus:

- 114 unique observations total;
- 76 observations whose saved locality label contains Brookwater, Springfield, Springfield Central, Spring Mountain, Augustine Heights or Bellbird Park;
- 25 of those 76 are Research Grade;
- 51 are Needs ID or Casual.

These counts are repository reconstruction from the saved HTML, not an iNaturalist-issued statistical report.

## Priority rule

The legally/ecologically useful ordering is not simply `Research Grade > Needs ID > Casual`.

Use:

1. potentially listed / conservation-significant taxa with source-paid identification and location;
2. exact same-creek / same-corridor observations with coordinates and accuracy;
3. Research Grade local native species as ecological-context evidence;
4. unresolved media as acquisition edges when date/location are recoverable;
5. common, introduced, planted, or spatially remote records as low immediate legal value.

Research Grade improves confidence in a taxon identification. It does not itself establish protected status, critical habitat, significant impact or project intersection.

## Refined high-value records visible in the saved pages

### Observation 357433327 — `Zanda`

The saved page records this as Needs ID at `Brookwater Dr at Greg Norman Circuit`, observed 2 May 2026 at about 4:36 pm. The saved card shows both photo and audio media and identifies the taxon only to `Zanda` / the yellow-tailed and white-tailed black-cockatoo genus grouping.

This is now treated as an **ecological-context/species-resolution edge**, not a threatened-species legal candidate. Do **not** assign species-level conservation status at genus level.

Highest-alpha next action: recover current individual-observation identifications and exact coordinate/accuracy.

### Observations 321370246 and 374519427 — unknown audio-bearing observations

The saved pages show both records as Unknown/Casual with sound media, but crucially they also show:

```text
Missing Date
Missing Location
```

So these are **not presently local Woogaroo occurrence receipts**. They are retained as non-spatial identification Snowball edges only.

For each, recover:

- individual observation page;
- audio;
- date/time, if it exists outside the saved list carrier;
- exact/obscured coordinate and accuracy, if available;
- current community identifications;
- any later expert identification.

Do not infer that either observation belongs to Brookwater merely because it appears in the same saved user corpus.

### Observation 388681275 — `Calomela juncta`

Research Grade, Brookwater Dr / Greg Norman Circuit, observed 6 August 2026 at about 4:17 pm. Useful as local biodiversity-context evidence, but no threatened-species legal proposition is currently paid from this record.

### Observation 364188331 — Scarlet Honeyeater (`Myzomela sanguinolenta`)

Research Grade, Brookwater, observed 23 May 2026 at about 3:16 pm. Useful native-bird occurrence in the broader landscape. Exact coordinates are still required before any same-project or same-corridor claim.

### Observation 331651806 — Australian King Parrot (`Alisterus scapularis`)

Research Grade at Grand Ave / Applecross Cct, Spring Mountain, observed 24 November 2025. Useful as southern local-landscape avifauna context, not presently a threatened-species legal atom.

### Observation 324838582 — Red-necked Wallaby (`Notamacropus rufogriseus`)

Research Grade, Springfield, observed 4 November 2025. Useful as terrestrial-fauna context in the broader Springfield landscape, subject to exact coordinates before corridor or project use.

## FrogID remains the stronger conservation lead

The separate FrogID capture 948283 remains the strongest current observer-supplied conservation lead because the selected taxon is `Adelotus brevis` / Tusked Frog, which Queensland material classifies as Vulnerable. The visible FrogID state remains pending validation, so the safe chain is:

```text
observer-selected Tusked Frog
!= FrogID expert validation
!= agency occurrence finding
```

The observer-confirmed recording location is `-27.649945, 152.898928`, supported by a supplied Google Maps coordinate display and first-person confirmation. Native FrogID coordinates remain to be acquired.

## Spatial join needed

For the 76 local iNaturalist records, the next material step is a coordinate/accuracy extraction and exact join against:

- Opossum Creek;
- the SHG 675 ha Scenic/Peninsula contiguous-landscape carrier;
- official Queensland biodiversity-corridor geometry;
- Scenic / Peninsula / Springview polygons;
- approved operational-works / clearing polygons where available.

Saved locality labels such as `Brookwater Dr at Greg Norman Circuit` are useful acquisition coordinates but are not project intersections.

## Attribution / WrongType boundaries

```text
observer record != agency survey
Research Grade != statutory protected status
locality label != exact GIS intersection
genus identification != species identification
missing location != local occurrence
species occurrence != critical habitat
local biodiversity != significant detrimental effect
```

Unknown observations are retained because later identification can pay new evidence edges; they are not promoted merely because they are acoustically interesting.
