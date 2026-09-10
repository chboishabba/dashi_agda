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

1. potentially listed / conservation-significant taxa or unresolved taxa that could become such after identification;
2. exact same-creek / same-corridor observations with coordinates and accuracy;
3. Research Grade local native species as ecological-context evidence;
4. common, introduced, planted, or spatially remote records as low immediate legal value.

Research Grade improves confidence in a taxon identification. It does not itself establish protected status, critical habitat, significant impact or project intersection.

## Highest-alpha records already visible in the saved pages

### Observation 357433327 — `Zanda`

Saved as Needs ID at Brookwater Dr / Greg Norman Circuit and identified only to the genus grouping covering yellow-tailed and white-tailed black cockatoos.

Do **not** assign species conservation status at genus level. The useful action is to resolve the species-level identification first.

### Observations 321370246 and 374519427 — unknown audio-bearing observations

The saved pages show these as Unknown/Casual with sound media. They are worth retaining as active Snowball acquisition edges rather than discarding because the current taxon is unresolved.

For each, recover:

- individual observation page;
- audio;
- date/time;
- exact/obscured coordinate and accuracy;
- current community identifications;
- any later expert identification.

### Observation 388681275 — `Calomela juncta`

Research Grade, Brookwater Dr / Greg Norman Circuit. Useful as local biodiversity-context evidence, but no threatened-species legal proposition is currently paid from this record.

### Observation 364188331 — Scarlet Honeyeater (`Myzomela sanguinolenta`)

Research Grade, Brookwater. Useful native-bird occurrence in the broader landscape. Exact coordinates are still required before any same-project or same-corridor claim.

## FrogID remains the stronger conservation lead

The separate FrogID capture 948283 remains the strongest current observer-supplied conservation lead because the selected taxon is `Adelotus brevis` / Tusked Frog, which Queensland's current environmental-offset policy lists with NCA class V (Vulnerable). The visible FrogID state remains pending validation, so the safe chain is:

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
species occurrence != critical habitat
local biodiversity != significant detrimental effect
```

Unknown observations are retained because later identification can pay new evidence edges; they are not promoted merely because they are acoustically or spatially interesting.
