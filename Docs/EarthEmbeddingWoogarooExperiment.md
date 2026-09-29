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
