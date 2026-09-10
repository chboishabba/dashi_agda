# Save Woogaroo Forest — iNaturalist corpus addendum

## Purpose

This addendum records the observer-supplied saved iNaturalist pages as one deduplicated occurrence corpus. It supplements the FrogID occurrence lane and does not collapse citizen-science observations into agency findings or statutory conclusions.

## Corpus accounting

Three saved observation pages were supplied, with the third page recovered from the accompanying `Observations · iNaturalist.tar.xz` website archive.

Deduplicating by native iNaturalist observation id gives:

- **114 unique observations**;
- **36 Research Grade**;
- **46 Needs ID**;
- **32 Casual**.

The previously analysed second saved page contained 96 unique observations. The third saved page contains 19 unique ids, of which **18 are new** relative to the 96-observation page and one overlaps. The first saved page is a partial carrier whose ids are already subsumed by the later page.

Therefore:

```text
HTML cards / repeated links != independent observations
saved-page overlap != corroboration
114 unique native observation ids = current saved-profile corpus
```

## Local landscape subset

Using only the saved iNaturalist locality labels, 76 of the 114 observations fall in the local Brookwater / Springfield / Springfield Central / Spring Mountain / Augustine Heights / Bellbird Park cluster.

This is a locality-string reconstruction, not an exact GIS intersection. Individual observation coordinates and accuracy circles must be acquired before joining an occurrence to Opossum Creek, the SHG 675 ha contiguous landscape, official corridor geometry, or a development/clearing polygon.

## Third-page recovery

The third page contributes 18 older observations not present in the main 96-observation carrier. They include records from Brookwater as well as older observations in Chapel Hill, The Gap and other locations. These records should remain individual observation fibres; they do not become Woogaroo evidence merely because they belong to the same observer profile.

## Attribution and quality grade

The saved pages identify the collection as observations by `johl1` / Johl Brown. The corpus counts above are DASHI reconstructions from observer-supplied saved HTML, not statistics asserted by iNaturalist in a report.

Likewise:

```text
Research Grade != government agency finding
Needs ID != confirmed taxon
Casual != false observation
locality label != exact coordinate
observation count != legal element paid
```

Research Grade can materially strengthen a citizen-science occurrence receipt because it records iNaturalist community identification state, but every legally relevant proposition must still be routed through its own source, spatial and statutory consumers.

## Snowball priorities

The high-alpha next pass is per-observation rather than another corpus count. For each local observation, preserve:

```text
native observation id
-> taxon / taxonomic rank
-> quality grade
-> observed date/time
-> public/obscured geoprivacy
-> native coordinates + positional accuracy where available
-> media carrier
-> identifiers / identification count
-> exact landscape/project intersection
-> conservation-status source
-> statutory consumer / residual
```

The FrogID captures 948283/948284 remain separate platform records and should not be merged with an iNaturalist observation unless an explicit same-observation bridge is supplied.
