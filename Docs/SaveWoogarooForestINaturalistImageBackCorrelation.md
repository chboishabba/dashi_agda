# Save Woogaroo Forest — iNaturalist image back-correlation addendum

## Purpose

This note uses the observer-supplied iNaturalist profile-map screenshot together with the supplied FrogID/Google Maps/satellite screenshots to recover a bounded spatial tier between a coarse saved locality and an exact native observation coordinate.

The rule is:

```text
saved locality + visually matching neighbourhood
-> image-backed same-neighbourhood proposition
!= exact native observation pin
!= survey-grade coordinate
!= project/corridor GIS intersection
```

## Image anchors

The supplied iNaturalist profile map shows a dense cluster of observations through Brookwater immediately west of Springfield, with additional observations south through Springfield / Springfield Central / Spring Mountain.

Separate supplied satellite imagery identifies the northern golf-course / wooded Opossum Creek interface. A supplied Google Maps share displays `-27.649945, 152.898928`, and the observer states that they personally confirm this as the point where they were standing for the FrogID recordings.

These image carriers can therefore back-correlate records with narrow saved Brookwater locality labels, while remaining weaker than an observation-specific native coordinate.

## Observation 357433327 — `Zanda`

Saved iNaturalist carrier:

- taxon: genus `Zanda` / Yellow-tailed and White-tailed Black Cockatoos;
- quality: Needs ID;
- date: 2 May 2026;
- locality: `Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300`;
- photo and audio media are visible in the saved page.

Because the profile map shows a dense Brookwater cluster and the satellite images independently anchor the Opossum/golf-course neighbourhood, this record can be upgraded from `localityLabelOnly` to:

```text
imageBackCorrelatedNeighbourhood
```

Safe reading: same Brookwater/Opossum-corridor neighbourhood.

Unsafe reading: the visible profile-map pin at any particular screen coordinate is observation 357433327.

Species-level conservation status also remains unresolved because the record is genus-level.

## Observation 388681275 — `Calomela juncta`

Saved carrier:

- Research Grade;
- 6 August 2026;
- locality `Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300`.

This receives the same image-backed neighbourhood tier. Its Research Grade state improves taxon confidence but does not improve the spatial tier beyond what the map evidence supports.

## Observation 364188331 — Scarlet Honeyeater

Saved carrier:

- `Myzomela sanguinolenta` / Scarlet Honeyeater;
- Research Grade;
- 23 May 2026;
- locality `Brookwater QLD 4300`.

The locality is too broad to assign it to the Opossum/golf-course cluster from the profile screenshot alone. It remains broader Brookwater context until an observation-specific map or native coordinate is acquired.

## FrogID 948283

This remains the strongest observer-location carrier:

```text
-27.649945, 152.898928
```

The Google Maps share, satellite imagery, FrogID map screenshots and observer first-person confirmation mutually support the observer-location proposition at the northern golf-course / Opossum Creek wooded interface.

But preserve:

```text
observer-confirmed coordinate
!= native FrogID coordinate
!= FrogID expert taxon validation
!= survey-grade point
!= statutory GIS intersection
```

## Spatial evidence ladder

```text
localityLabelOnly
< imageBackCorrelatedNeighbourhood
< observerConfirmedCoordinate
< nativePlatformCoordinate
< exactGISIntersection
```

This avoids throwing away useful visual evidence while also avoiding false precision.

## Highest-alpha next join

Use native coordinates/accuracy when obtainable for the narrow-locality iNaturalist observations, then compare them with:

1. Opossum Creek geometry;
2. SHG's 675 ha Scenic/Peninsula contiguous-landscape carrier;
3. official Queensland biodiversity-corridor geometry;
4. Scenic / Peninsula / Springview project polygons;
5. approved operational-works / clearing polygons.

Until then, the image-backed records pay neighbourhood-level ecological context, not exact project intersection.
