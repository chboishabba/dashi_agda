# Earth embeddings × Woogaroo — research contract (2026-09-29)

## Source and observation boundary
- AlphaEarth: 64 bands per 10 m cell and annual interval. Google's current
  GCS documentation describes 2017–2025 data, signed 8-bit storage,
  dequantisation and unit-length vectors:
  https://developers.google.com/earth-engine/guides/aef_on_gcs_readme
- TESSERA v2: Matryoshka 16/32/64/128 prefixes; 16D performance is an
  empirical aggregate, **not** a theorem:
  https://arxiv.org/abs/2607.03949
- Ipswich City Council: Woogaroo incl. Opossum/Mountain creeks, 69 km²,
  Lower Brisbane River subcatchment:
  https://www.ipswich.qld.gov.au/About-Council/Initiatives/Environment/Waterways/Catchments-and-Plans/Brisbane-River-Catchment
- Council's 2020 waterway report states 65 km² *within Ipswich LGA*;
  these are **different denominators**, not a data contradiction.
  https://www.ipswich.qld.gov.au/files/assets/public/v/1/about-council/media-and-publications/corporate-publications/strategy-and-implementation-programs/waterway-health-strategy/documents/waterwayhealthstrategy2020-background-report_web.pdf

## Implementation mapping
- Agda: `DASHI/Geo/EarthEmbeddingWoogarooExact.agda`
- Lean: `EarthEmbeddingWoogaroo.lean`
- Existing Agda legal/LES owner:
  `DASHI/Law/SensibLawWoogarooLESCanopyLiDARInteropExact.agda`
- LES owns GIS, LiDAR and actual raster analytics. These modules only describe
  typed contracts and a downstream hydrologic graph.
- Do not promote a change score to a canopy/species/habitat assertion, nor
  to an EPBC conclusion, without calibrated field/remote-sensing evidence
  and an independent legal/source review.

## Empirical protocol (not yet run)
1. Pin exact 10-metre grid, CRS, model version, year and acquisition interval.
2. Obtain AlphaEarth annual pixels and TESSERA for co-registered cells.
3. Build baseline, AlphaEarth, TESSERA and fused feature experiments with
   otherwise identical supervised heads and training budgets.
4. Split by non-overlapping spatial catchment blocks and held-out year groups;
   maintain disjointness receipts and separate upstream/downstream boundaries.
5. Evaluate canopy/riparian change, runoff and sediment against independent
   measurements; report uncertainty/calibration, missing-data and regional
   failure modes. Sediment or nutrient concentration cannot be directly
   asserted from embeddings.
6. Join LES canopy/LiDAR data by explicit spatial/time keys only after
   calibration. Preserve evidence provenance into legal consumer boundaries.
7. Report all raw measurement provenance and model comparisons, including
   null effects and model failure. No performed experiment is claimed here.


## Implementation ledger — second tranche (2026-09-29)
- **G1** typed finite dimensionality: implemented in Agda and Lean.
- **G2** unit sphere: Lean `OnSphere` predicate; **NOT established for
  quantised released bytes**, needs per-product normalisation receipt.
- **G3** cosine / squared Euclidean identity: Lean finite-dimensional
  algebra source, plus distance-order equivalence; **kernel not checked**.
- **G4** Matryoshka prefix: Lean transitive prefix composition; Agda
  `takeAppend` for dependently sized vectors. No performance claim.
- **G5** temporal stability: Agda evidence type only; no observational run.
- **G6** local decoding: Lean `LocalDecoder`,
  `PhysicalDecoderValidation`; Agda `PhysicalDecoderEvidence`.
  No validation results or decoder weights supplied.
- **G7** common latent: Lean typed projections and squared alignment
  residual; Agda correspondence receipts. No fitted projections.
- **G8** quantisation: per-coordinate certificate and squared bound
  attempted at source level in Lean; Agda certificate schema.
  No aggregate norm-error/weighted aggregation theorem yet.
- **G9** geographic/time generalisation: Lean held-out partition
  disjointness contract, Agda receipt structure. Python four-arm CSV
  evaluator rejects duplicate keys and shared cells or years. It does not
  enforce a geographic buffer or certify source independence.
- **Geometry research**: distinct report types for ambient dimension,
  participation ratio, local dimension and physical-variable count.
  Lean includes a participation-ratio expression; a smooth surrogate
  requires explicitly supplied tangent maps and receipts. No true
  measure-theoretic pushforward-support theorem, eigen-analysis,
  neighbourhood tangent estimator or global-obstruction theorem yet.
- **Woogaroo**: hydrologic graph, LES/LiDAR reference and quality/provenance
  columns retained. No actual downloading, training or measurements.

### Python evaluation
```sh
python -m unittest discover -s tests -p test_evaluate_woogaroo_embeddings.py -v
python scripts/evaluate_woogaroo_embeddings.py observations.csv receipts.json
```
The input contains each row's *precomputed held-out predictions*, not raw
64D/128D vectors. A future geospatial extraction/training owner must create
these predictions without train/test contamination. The evaluator is not an
end-to-end experiment. The tests have been source-written but have not run
in the current environment.

### Added primary sources
- Rahman (Feb 2026): https://arxiv.org/abs/2602.10354.
  12.1 million **continental US** samples in 2017–2023. Reported physical
  interpretation results must not transfer automatically to Queensland.
- Rahman et al. (Apr 2026): https://arxiv.org/abs/2604.18715.
  Participation ratio ~13.3 and local intrinsic dimension ~10 are empirical
  estimator outputs, not equalities about the embedding's rank.
- Ou & Zheng (Apr 2026): https://doi.org/10.1029/2025GL121604.
  455 Australian catchments in 2017–2022. No claimed Woogaroo result.
- Liu et al. (Aug 2026): https://doi.org/10.1029/2026GL122814.
  531 CAMELS validation basins and 3434 global basins; transfer remains
  hydrologic-task and population dependent.
