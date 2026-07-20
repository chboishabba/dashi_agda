# Spacetime-history world-tube bridge

## Status

Candidate-only geometry and empirical bridge. This tranche does not claim exact location recovery, a complete reconstruction of lived experience, or surveillance authority.

## Formal carrier

A personal mobility history is represented as a time-indexed sequence of uncertain spatial observations. The full history carrier corresponds to the graph of a trajectory in spatial position × time. A world-tube thickens each idealized point by an explicit radius carrying uncertainty, duration, or a separately supplied meaning weight.

The core module is:

- `DASHI.Geometry.SpacetimeHistoryWorldTube`

It provides:

- `SpatialSample` for projected east/north/altitude coordinates;
- `TimelineObservation` for time, place, uncertainty, motion mode, and provenance;
- `WorldTubeSection` for spatial radius, temporal thickness, and meaning weight;
- `SpacetimeHistory` for the complete typed collection;
- `PresentSlice` for the current spatial section without identifying it with the whole history;
- explicit contracts for spacetime-cube, long-exposure, calendrical-helix, semantic-braid, and moving-slice projections.

Every visualization is typed as a lossy projection. The geometry therefore preserves the distinction between the history carrier and any rendered map, tube, braid, helix, or long exposure.

## Existing DASHI integration

The empirical adapter is:

- `DASHI.Empirical.GoogleTimelineSpacetimeBridge`

It normalizes a Google Maps Timeline-style row into an uncertain `TimelineObservation`, then maps its time and place into the existing:

- `DASHI.Biology.IntersectionalLongitudinalResidualDynamics`

carrier. That existing carrier keeps body × time × place × relation × institution × axis-bundle explicit. The bridge therefore does not reduce a person to coordinates: mobility observations remain situated within embodied, relational, institutional, and axis-aware context.

The accuracy radius becomes world-tube thickness rather than false coordinate precision. Vendor activity labels remain provenance-bearing inferences rather than ground truth. Missing rows are acknowledged at dataset level.

## Projection family

The formal projection family distinguishes:

1. **Spacetime cube** — east/north geometry with time on the third display axis.
2. **Geographic long exposure** — time collapsed into density or brightness.
3. **Calendrical helix** — cyclic time phase combined with a longitudinal calendar axis.
4. **Semantic place braid** — coordinates quotiented into explicit place strands.
5. **Moving present slice** — a time-indexed section through the complete history.

This gives a typed version of the dimensional analogy: an observer ordinarily encounters a present section, while the accumulated archive can be rendered as a single worm-like or braided history object.

## Fail-closed boundaries

The tranche rejects by construction:

- exact-location recovery from uncertain samples;
- complete-life recovery from mobility data;
- identifying any projection with the underlying history;
- treating vendor inference as experience;
- promoting a personal archive into surveillance authority.

## Regression surface

`DASHI.Geometry.SpacetimeHistoryWorldTubeRegression` provides canonical witnesses that the candidate-only, uncertainty, missingness, non-completeness, present-slice, and non-authority flags reduce to their intended values.
