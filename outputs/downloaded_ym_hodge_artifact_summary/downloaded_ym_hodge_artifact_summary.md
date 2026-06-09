# Downloaded YM/Hodge Artifact Summary

- Schema: `dashi-downloaded-ym-hodge-artifact-summary-v1`
- Version: `1.0.0`
- Input dir: `temp-DOWNLOADED/new additions`
- Artifact count: `12`
- Claim boundary: downloaded-context only; no Clay/YM/Hodge promotion.

## Key Gates

| Gate | Value |
|---|---:|
| `q` | `0.231781894752627` |
| `eta4_q` | `0.927127579010509` |
| `eta6_q` | `1.39069136851576` |
| `eta8_q` | `1.85425515802102` |
| `eta_threshold` | `4.31440083388422` |
| `exp_minus_4` | `0.0183156388887342` |
| `su2_first_safe_k` | `9` |
| `su3_first_safe_k` | `11` |
| `su3_k11_row` | `0.0098876953125` |
| `su3_k11_delta` | `0.9901123046875` |
| `su3_k11_m0` | `4.61646419260685` |

- Route decision: `MASTER_WC3_SU3_CONSERVATIVE_CLOSES_AT_K11_CONDITIONALLY`
- Next unconditional gate: `TemporalTermAbsorbedNotResidualEvidence / residual-support proof`
- Next authority lane gate: `PolymerDefinedOnBlockedLattice -> KPEntropyAtBlockedScaleL2 already authority-conditional`

## Artifact Hashes

| Artifact | Kind | Size | SHA-256 |
|---|---|---:|---|
| `ym_sprint82_summary.json` | `json` | 768 | `0690ac4cc6551c4773b811a578fe5d92ea611327d51c5fd7a19aa5b52b7c10fe` |
| `ym_sprint82_eta_thresholds.csv` | `csv` | 254 | `86d90410a8746c448f1ae162e0ad941f9444523091c40c9048a2774b2034e3bb` |
| `ym_sprint82_assumption_a_oscillation.csv` | `csv` | 567 | `c29f0aa263aae67db7fa99b5798f14589ec7b8a5fd44123231ecd7781b88d4b6` |
| `ym_sprint93_summary.json` | `json` | 397 | `57354c08c3f7b566088cf64929dd71a3f848c57bb6a2b43c0400a4c7a4d7dbca` |
| `ym_sprint93_rows.json` | `json` | 2767 | `199ffed1cabb92bdff125fc2e429ab82a41cf4bcd198f0d306bbc02efa38b77f` |
| `ym_sprint93_master_wc3_calcs.py` | `python` | 1084 | `4f785f9976ba10f18b2cc1b866e63b6ec7531fdd35a9aedb4b41a11f7f2be808` |
| `sprint69_constants_table.csv` | `csv` | 794 | `d037c4896a95ee1ab5def78eeaf9929f4a72dfda8b05b9ac960e17def473bad9` |
| `sprint73_lemma_stack.csv` | `csv` | 1087 | `e7ceb114a8ccef5e043930e9a41e466a531dd2ce77fb6545dfb61455386f337f` |
| `ym_slab_geometry.csv` | `csv` | 392 | `ffb2f01a5c762fe63c07f4e102af3a1d012a1a89f5f34451bfa026463dd98330` |
| `ym_spatial_slab_entropy_count.csv` | `csv` | 477 | `fffe3a3f079aa1875850c0948aee7337ad65ec64ca1e422174f1a9c6ece92f84` |
| `ym_temporal_support_noncreation_table.csv` | `csv` | 608 | `2c531a56fc37b9113b851b67cbb8cb54a668b228246b6c43731c406d7e986b9b` |
| `YMSprint93ContinuumGapAttempt.agda` | `agda` | 6735 | `4aa9c2544cc4be4aa9bff6431e026e805fe316a3ec438e75fd302255d780d6d1` |

## Closed Or Packageable Lemmas

- `Generic 4D entropy fails`: Closed arithmetic (8q=1.854255>1)
- `Spatial entropy closes`: Closed arithmetic (4q=0.927128<1)
- `MixedPlaquettes=FaceAction`: Closed Sprint72 (Λ=1 exactly)
- `10% Residual fallback`: Packageable (KP=0.9949<1)
- `LinkVariableDisjointness`: Packageable (r_K=1 < L=2)
- `TemporalMeasureFactor Λ=1`: Packageable (Λ=1 exact)

## Open Or Key-Gate Lemmas

- `BalabanTransferCompatibility`: KEY GATE (open) (η=4 justified)
- `TemporalQuotientEntropyHalving`: Follows from above (Factor 2 from L=2)
- `AllDiameterWeightedKP`: Open (—)
- `SmallFieldBoundsSurviveAniso`: Open (C_uni exists)
- `LatticeMassGapFromAnisotropicKP`: Open (—)
- `ContinuumMassGapTransfer`: Open (—)
- `OSWightmanReconstruction`: Open (—)
- `Clay YM`: Open (—)

## Agda Continuum Gap Surface

- Records: `14`
- Functions: `6`
- Hard wall terms present: `ContinuumLimitMassGap`=True, `noSpectralPollutionUnderContinuumLimit`=True, `positiveContinuumMassGap`=True, `OSWightmanReconstruction`=True, `ClayYangMillsCandidate`=True

## Promotion

- `clay_yang_mills_promoted = false`
- `continuum_mass_gap_promoted = false`
- `hodge_field_equations_promoted = false`
