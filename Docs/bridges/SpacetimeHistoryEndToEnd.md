# Spacetime-history end-to-end tranche

## Status

Candidate-only formal and executable scaffold. This tranche does not claim exact location, complete lived experience, exact 3D reconstruction, identity recovery, evidentiary authority, or reproduced paper benchmarks.

## Architecture

The carriers remain distinct:

`personal history -> visual episode -> dynamic scene -> point/Gaussian trajectory -> rendered projection`

The arrows are typed integration maps, not equivalences.

## Formal modules

- `DASHI.Geometry.SpacetimeHistoryTypedCore`
  - distinct timestamp, duration, metres, confidence, pixel-coordinate and world-coordinate carriers;
  - evidence-valued `ObservedBy`, `ProjectsTo`, `Enriches`, and `RendersAt` relations;
  - policy-gated partial interpolation and explicit unknown/conflicting/discontinuous intervals;
  - a non-replacement law preventing local enrichment from inheriting identity or semantics.
- `DASHI.Geometry.SpacetimeHistoryProjectionLaws`
  - executable cube, long-exposure, helix, braid, and present-slice projections;
  - explicit information-retention receipts, including time loss in long exposure.
- `DASHI.Geometry.SpacetimeHistoryScaleHierarchy`
  - point-track to scene, scene to episode, and episode to history maps;
  - approximate coarse-observable compatibility rather than equality of representations.
- `DASHI.Geometry.SpacetimeHistoryRegistrationAndClustering`
  - uncertainty-aware semantic place clusters;
  - time-and-coordinate video registration receipts;
  - paper integration boundaries.
- `DASHI.Vision.Stereo4DDynamicReconstructionBridge`
  - credits Jin et al., *Stereo4D: Learning How Things Move in 3D from Internet Stereo Videos*, arXiv:2412.09621v1 (2024);
  - separates camera, scene-point, and candidate subject motion;
  - records pseudo-metric/non-exact dynamic reconstruction and non-replacing history enrichment.
- `DASHI.Vision.GaussianVideoCompressionBridge`
  - credits Lee, Choi, and Lee, *GaussianVideo: Efficient Video Representation and Compression by Gaussian Splatting*, arXiv:2503.04333v1 (2025);
  - records shared 2D Gaussian seeds, time-conditioned deformation, xy/xt/yt factorisation, temporal-gradient allocation, and lossy/no-geometry/no-motion-authority boundaries.
- `DASHI.Geometry.SpacetimeHistoryEndToEndRegression`
  - canonical reduction witnesses across the tranche.

## Executable pipeline

Normalize a Google Timeline-style JSON export:

```bash
python scripts/import_google_timeline_worldtube.py Records.json build/worldtube.json
```

Generate a self-contained interactive renderer:

```bash
python scripts/render_worldtube_html.py build/worldtube.json build/worldtube.html
```

Open `build/worldtube.html` in a browser. The current demonstrator uses local ECEF displacement horizontally, normalized time vertically, reported accuracy for point radius, and a movable present slice.

Run importer tests:

```bash
python -m unittest tests.test_worldtube_pipeline
```

## Remaining implementation boundary

The importer intentionally accepts multiple historical JSON shapes through conservative recursive extraction. It is not a guarantee of support for every future Google export schema. Parquet output, geodesically accurate WGS84 ellipsoid conversion, segmented ENU atlases, production place clustering, and direct execution of Stereo4D/GaussianVideo checkpoints remain future integration work.
