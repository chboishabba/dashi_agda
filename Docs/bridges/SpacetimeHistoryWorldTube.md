# Spacetime-history world-tube bridge

## Status

Candidate-only geometry and empirical bridge. This tranche does not claim exact location recovery, a complete reconstruction of lived experience, exact 3D reconstruction, lossless video recovery, identity inference, or surveillance authority.

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

## Stereo4D measurement and reconstruction layer

The dynamic visual reconstruction extension explicitly credits:

> Linyi Jin, Richard Tucker, Zhengqi Li, David Fouhey, Noah Snavely, and Aleksander Holynski. **Stereo4D: Learning How Things Move in 3D from Internet Stereo Videos.** arXiv:2412.09621v1, 2024.

The formal modules are:

- `DASHI.Vision.Stereo4DDynamicReconstructionBridge`
- `DASHI.Vision.Stereo4DDynamicReconstructionRegression`

Stereo4D contributes a measurement-and-reconstruction layer rather than another display projection. Its pipeline combines VR180 stereo frames, shot segmentation, camera-pose estimation, stereo calibration, disparity/depth estimation, long-range 2D tracks, world-frame lifting, ray-wise temporal correction, consistency filtering, and dynamic point-cloud construction.

The bridge types the paper's main distinctions:

- `StereoFrameReceipt` preserves the left/right frames, camera pose, rig calibration, and disparity provenance;
- `DynamicPointObservation` separates image coordinates from pseudo-metric world coordinates and carries depth, tracking, visibility, and confidence fields;
- `RayCorrectionReceipt` records correction along the camera ray together with static-consistency, dynamic-acceleration, and disparity-faithfulness terms;
- `ReconstructionFilterReceipt` records stereo, cycle, overlap, semantic-drift, cross-fade, and synthetic-overlay checks;
- `DynamicReconstruction` assembles a candidate-only pseudo-metric reconstruction;
- `QueryTimeMotionPrediction` types DynaDUSt3R-style pointmap and motion-map predictions at an intermediate query time;
- `HistoryEnrichmentReceipt` is the narrow seam into the personal world-tube carrier.

The integration is intentionally asymmetric. A Google Timeline observation supplies a coarse subject-level mobility trace. A Stereo4D-style reconstruction supplies local camera-relative and world-frame scene trajectories within a visual episode. The latter may enrich the former with local geometry or motion evidence, but cannot silently replace it.

In particular, the formalism keeps three roles distinct:

1. **camera-rig motion** — movement of the observing coordinate system;
2. **scene-point motion** — static or dynamic motion reconstructed in the world frame;
3. **candidate subject motion** — a separately justified association between a reconstructed track and the person whose longitudinal history is being represented.

This prevents the common category error in which every moving image feature is treated as movement of the timeline subject, or camera movement is mistaken for scene movement.

## GaussianVideo representation and compression layer

The efficient video-carrier extension explicitly credits:

> Inseo Lee, Youngyoon Choi, and Joonseok Lee. **GaussianVideo: Efficient Video Representation and Compression by Gaussian Splatting.** arXiv:2503.04333v1, 2025.

The formal modules are:

- `DASHI.Vision.GaussianVideoCompressionBridge`
- `DASHI.Vision.GaussianVideoCompressionRegression`

GaussianVideo contributes a representation/compression layer, not a world-space reconstruction layer. A shared set of 2D Gaussian seeds is deformed as a function of frame time. Each deformation may alter image-plane mean, colour, rotation, scale, and covariance-related appearance. The formal bridge represents this schematically as:

```text
G_i(t) = G_i + ΔG_i(t)
```

The time-conditioned deformation is produced from a factorised multi-plane feature carrier. For image coordinates `(x,y)` and time `t`, the paper uses spatial and spatiotemporal planes corresponding to `xy`, `xt`, and `yt`; their sampled features are combined by a Hadamard product before lightweight decoding:

```text
f(x,y,t) = F_xy(x,y) ⊙ F_xt(x,t) ⊙ F_yt(y,t)
```

The bridge types:

- `Gaussian2DSeed` for shared image-plane Gaussian parameters;
- `TimeConditionedDeformation` for predicted per-time attribute changes;
- `MultiPlaneFeatureReceipt` for `xy`, `xt`, and `yt` factorisation and multi-resolution sampling;
- `TemporalGradientReceipt` for cumulative adjacent-frame variation;
- `GaussianAllocationReceipt` for allocating more representational capacity to temporally variable regions;
- `GaussianVideoLossReceipt` for reconstruction and total-variation optimization terms;
- `GaussianVideoModelReceipt` for the candidate-only lossy compressed carrier;
- `GaussianVideoEpisodeBridge` for associating the video carrier with a longitudinal history and a separately typed Stereo4D reconstruction.

The integration keeps three levels distinct:

1. **source video** — the observed image sequence;
2. **GaussianVideo carrier** — a compressed model that renders approximations to frames;
3. **Stereo4D/world-tube carriers** — separately justified geometric and longitudinal interpretations.

Motion of a 2D Gaussian mean is therefore not automatically motion of an object in 3D, and neither is automatically movement of the timeline subject. GaussianVideo is useful here because it can make visual episodes compact and rapidly replayable while preserving an explicit boundary between efficient representation and geometric inference.

The paper reports strong efficiency gains relative to the compared NeRV-family baselines, including substantially faster training/rendering and lower memory use, while acknowledging a quality-efficiency tradeoff and per-video choices for plane resolution and multi-scale configuration. These are paper-reported empirical results, not theorems or reproduced DASHI benchmarks.

## Projection family

The formal projection family distinguishes:

1. **Spacetime cube** — east/north geometry with time on the third display axis.
2. **Geographic long exposure** — time collapsed into density or brightness.
3. **Calendrical helix** — cyclic time phase combined with a longitudinal calendar axis.
4. **Semantic place braid** — coordinates quotiented into explicit place strands.
5. **Moving present slice** — a time-indexed section through the complete history.

This gives a typed version of the dimensional analogy: an observer ordinarily encounters a present section, while the accumulated archive can be rendered as a single worm-like or braided history object.

Stereo4D-derived dynamic tracks and GaussianVideo-rendered episodes can be displayed inside one or more such sections, producing a nested structure:

- the personal world-tube records where the subject may have been over long time scales;
- each visual episode may have a compact GaussianVideo render carrier;
- a separately justified Stereo4D layer may contain a local dynamic 3D scene;
- each reconstructed scene contains point trajectories and confidence-bearing motion roles;
- the final display remains a projection of these carriers, not the carriers themselves.

## Fail-closed boundaries

The tranche rejects by construction:

- exact-location recovery from uncertain samples;
- complete-life recovery from mobility data;
- identifying any projection with the underlying history;
- treating vendor inference as experience;
- treating pseudo-metric reconstruction as exact metric ground truth;
- claiming that an image pair uniquely determines the real 3D world;
- identifying a reconstructed scene-point track with lived personal history;
- treating a compressed GaussianVideo model as a lossless source archive;
- treating image-plane Gaussian deformation as recovered 3D object motion;
- inferring identity or authority from a visual track or render carrier;
- promoting a personal archive into surveillance authority.

## Regression surfaces

`DASHI.Geometry.SpacetimeHistoryWorldTubeRegression` provides canonical witnesses that the candidate-only, uncertainty, missingness, non-completeness, present-slice, and non-authority flags reduce to their intended values.

`DASHI.Vision.Stereo4DDynamicReconstructionRegression` adds canonical witnesses for pseudo-metric/non-exact reconstruction, learned-prior/non-exact query-time motion, explicit camera/scene/subject role separation, and the rule that visual enrichment does not replace the longitudinal timeline.

`DASHI.Vision.GaussianVideoCompressionRegression` adds canonical witnesses for candidate-only and lossy status, non-recovery of geometry, multi-plane aggregation, temporal-gradient allocation, predicted deformation, and optimization-proxy loss status.
