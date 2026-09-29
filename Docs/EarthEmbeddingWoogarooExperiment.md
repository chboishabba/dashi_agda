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

## Third tranche: executable, source-oriented pipeline

The geometry owners were extended to `EarthEmbeddingAdvanced.lean` and
`DASHI/Geo/EarthEmbeddingAttributedSourcesExact.agda`. The latter reuses
`DASHI.Core.AttributedSourceCore` and distinguishes original-author claims
from independently written DASHI mathematics. Study figures cannot satisfy
formal theorem obligations by citation.

**Live source extraction (requires caller-controlled credentials and labels)**

`scripts/sample_woogaroo_embeddings.py` accepts an independent sampling
CSV with columns `lon,lat,year,label,label_source,baseline_*` and writes a
matched `.npz` containing AlphaEarth 64D and GeoTessera 128D samples, UTM
coordinates, cell/year keys and labels. It uses the documented Earth Engine
`GOOGLE/SATELLITE_EMBEDDING/V1/ANNUAL` collection and
`GeoTesseraZarr.sample_points` interface. No hidden fallback is permitted
for absent pixels, years, or public Cambridge coverage. An extracted sample
is *not* a Woogaroo-catchment mask: supply and verify the exact geometry.
The sample's land/edge/water-status, temporal precision and pixel-centre
co-registration still require documented site-level checks.

```sh
# External dependencies: earthengine-api, geotessera, pyproj, numpy.
# Authenticate the EE project outside this script.
python scripts/sample_woogaroo_embeddings.py observations.csv matched.npz \
  --ee-project YOUR_PROJECT --crs EPSG:32756 --tessera-version verified-v1.1
```

The default GeoTessera cloud interface may serve v1.1; its current
documentation says v2 distribution is limited. Calling a model `v2`
does not make v2 data available. Verify dataset identity/version at the
provider store before drawing conclusions.

**Same-fold four-arm evaluation**

`scripts/earth_embeddings_experiment.py` loads a strict versioned manifest
and numeric arrays and fits comparable Ridge heads to baseline-only,
baseline+AlphaEarth, baseline+TESSERA, and baseline+both. Standardisation,
PCA/effective-rank diagnostics and model fitting use training samples only.
Heldout cells and years are disjoint. Optionally exclude a projected-CRS
spatial buffer, and record unused boundary years/cells. This is a regression
prototype; classification and time-dependent hydrological process heads are
not implied by it.

```sh
python scripts/earth_embeddings_experiment.py matched.npz manifest.json \
    results.json --test-year 2024 --test-cell CELL_ID --buffer-metres 300
```

The manifest requires `alpha_source,alpha_version,tessera_source,
tessera_version,baseline_source,label_provenance,target,target_unit,crs,
pixel_size_metres,acquisition_qa,data_license,observation_window`.
That is a provenance minimum, not proof of independence or field calibration.
The script writes an SHA-256 of the input data and scores MAE/RMSE/R2.
The heldout-year/cell selection is a deliberate strict intersection;
intermediate samples are unused, not quietly assigned a fold.

**Geometry and source-specific quantisation**

`scripts/alphaearth_cog_quantization.py` implements Google's signed-int8
COG non-linear dequantisation `sign(x)*(x/127.5)^2`, vector sum followed
by norm-rescaling, an explicit rejection of cancellation, and a conditional
stability bound. Do not average the raw int8 band values; do not confuse
Google EE float embeddings with raw COG int8 storage.

`scripts/earth_embeddings_experiment.py` computes covariance
participation ratio `trace(C)^2/trace(C^2)` and local-PCA tangent rotation
probes. These are empirical *estimators*, not proof of a smooth manifold.
`scripts/cross_model_alignment.py` trains PCA projection and Procrustes
rotation on train-only matched 64D/128D vectors, and reports heldout
residual versus a deterministic shuffled control. There is no automatic
inference that co-location means identical environmental information.

**Local synthetic receipts**

The source-equivalent scripts and their synthetic test suite were run
locally in the tool container on 2026-09-29. Fifteen tests passed, covering
fold leakage, spatial buffers, 4-head outputs, covariance rank-one behavior,
local tangent estimates, signed-int8 nonlinearity, cancelling aggregates,
cross-model train-only alignment and metadata assembly. The four-head CLI
was additionally executed against generated synthetic arrays. Neither
synthetic result establishes an environmental effect or a Woogaroo result.

**Open physical obligations / no invented science**
- Collect licensed, independent, georeferenced Woogaroo habitat,
  sediment/runoff and canopy observations, with reliable calibration.
- Resolve exact approved 9281 clearing geometry with its source revision,
  and match spatial evidence through LES canopy/LiDAR owners.
- Validate provider-specific coverage, temporal windows, landmask,
  licensing, COG/EE interoperability and georegistration.
- Measure real-world uncertainty and external geographic/temporal transfer.
- Execute and kernel-check the Agda/Lean owners: local execution here had
  Python but no installed Lean or Agda compilers.
- To obtain a genuinely globally smooth manifold theorem would require
  explicit smoothness hypotheses and an actual validated atlas; a
  sample-based PCA estimate is insufficient.
- To validate a specific local field effect or legal finding requires
  observations and independent review; these have not been supplied.

**Primary source correction**: Google documentation gives individual
embedding channels no guaranteed physical meaning; Rahman's per-variable
interpretations apply to his sampled study, not to an unqualified A17
vegetation axis in every landscape. Source: 
https://developers.google.com/earth-engine/datasets/catalog/GOOGLE_SATELLITE_EMBEDDING_V1_ANNUAL

## Fourth tranche — learned-coordinate interpretability

**Agda:** `DASHI/Geo/EarthEmbeddingInterpretabilityExact.agda`.
**Lean:** `EarthEmbeddingInterpretability.lean`.
These own learned encoder checkpoints/preprocessing, independent physical
targets, local decoder and encoder derivative surfaces, composed candidate
sensor attribution, tangent-restricted attribution, strict held-out provenance
and invertible-coordinate non-identifiability. They do **not** label any
individual band `A00`…`A63` or TESSERA 0…127 as a fixed physical quantity.

The exact algebraic reparameterisation result says
`decode (undo (change (encode x))) = decode (encode x)` whenever
`undo ∘ change` is identity. Consequently the same overall
predictions can arise from multiple learned coordinate systems. This
non-identifiability does not exclude empirically stable directions under
a specified basis or locally valid concepts.

The Lean owner additionally declares genuine `HasFDerivAt` premises for
both differentiable maps and uses the Fréchet chain rule to compose them.
The Agda owner intentionally represents their derivatives as **candidates**:
it does not assert a chain rule in an arbitrary scalar set; a constructive
real derivative development remains necessary to promote those candidates
to mathematically validated derivatives.

For differentiable TESSERA checkpoints, estimate (a) decoder Jacobian,
(b) encoder Jacobian, and (c) their composition on genuine Sentinel-1/Sentinel-2
time-series and QA masks. Tangent restriction uses a locally fitted tangent
map rather than arbitrary off-manifold edits. Validate with independent
labels, observed time spans and spatial holdouts. Integrating gradients over
a baseline path requires an additional baseline, quadrature tolerance and
perturbation-validity receipt; such a numerical producer has **not** run.

The released Cambridge v2 student checkpoints are downloadable, and the
medium checkpoint is approximately 84 MB. The teacher checkpoint is a
separate 1024-dimensional representation, **not** a student 128-dimensional
Matryoshka vector: see the upstream README:
https://github.com/ucam-eo/tessera/blob/master/tessera_infer_v2/README.md

No public AlphaEarth encoder weights have been verified by this work. Black-box
probing of its published embeddings is available; white-box encoder backprop
is proposed only for checkpoints actually obtained and whose processing
pipeline is matched.

Reference:
- https://arxiv.org/abs/2602.10354 (Rahman, empirical physical probing)
- https://arxiv.org/abs/2604.18715 (Rahman et al., local geometry)
- https://arxiv.org/abs/2607.03949 (Feng et al., v2 Matryoshka)
- https://github.com/ucam-eo/tessera (original software/model provenance)

**Validation wall:** New modules are committed and included in targeted
Agda/Lean workflows, but neither local kernel check nor model-dependent
gradient experiment is claimed completed. The empirical pipeline needs
verified model checkpoints, Sentinel temporal inputs, Queensland field
labels, and end-to-end source/process version receipts.
