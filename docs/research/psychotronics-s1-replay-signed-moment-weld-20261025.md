# S1 Field Loom: deterministic sensor-stream replay and signed magnet covariance

**Date: 25 October 2026. Scope:** PR #1242, authored engineering software and a reproducible synthetic measurement-evidence protocol. **Not** a physical experiment, gravity result, verified original instrument stream or independent provenance certification.

## Highest-value unpaid software gate, now implemented

Previous code checked SHA-256 identities for an analyst-provided pair JSON and a separately listed sensor-stream file. That did **not** entail that the pairs were *actually computed* from the stream. It also let nominal user-provided factorial settings stand in for instrument-observed currents. These are important distinctions under the existing `AmyEskridgeAntigravityMeasurementObservationWeldExact`, `AntigravityCalibratedExecutionBridgeExact` and source attribution rules: matching names and hashes are weaker than a same-object transformation.

**Source-written implementation:**
- [`psychotronics_field_loom_reducer.py`](../../scripts/psychotronics_field_loom_reducer.py): versioned `S1-CSV-v1` deterministic stream→pair transformation. Explicit signed SI fields, full pair/session/current/time/polarity controls, calibrated moment and uncertainties, monotone timestamps, bounded row count and time gap. The physical magnet's *shared magnitude* uncertainty is keyed independently of its positive or negative orientation.
- [`psychotronics_field_loom_source_join.py`](../../scripts/psychotronics_field_loom_source_join.py): original raw-pairs/calibration/stream files and SHA-256 are checked; if this reducer is declared, regenerated pairs must match exact source rows, and the factorial settings are derived only from the replayed source stream. Older/unknown reducers leave `raw_stream_replayed_to_pairs = false`; their file-byte identity is not an accepted reduction.
- [`psychotronics_field_loom_metrology.py`](../../scripts/psychotronics_field_loom_metrology.py): the physical-arm rank comes solely from `factorial_settings_from_source`. A caller-supplied independent `factorial_settings` value cannot override the source replay. A self-declared Boolean `raw_to_pairs_reducer_verified` is **insufficient**. Real independent reducer review remains an additional obligation.
- [`psychotronics_field_loom_covariance.py`](../../scripts/psychotronics_field_loom_covariance.py): two opposed polarities of *the same magnet* share magnitude calibration uncertainty; its sensitivity carries sign. The original pos/neg moment calibration IDs can differ while `moment_covariance_group_id` remains identical. This is a covariance *hypothesis documented by calibration identity*, not proof of measurement independence or laboratory authenticity.
- [`test_psychotronics_field_loom_reducer.py`](../../scripts/test_psychotronics_field_loom_reducer.py): original synthetic CSV input, valid six-arm/two-session pattern, malformed numeric/time/condition/polarity/identity rejection, plus committed end-to-end source/hash/GLS design-rank/tamper regression.

## Exact schema and computation

The original instrument CSV has **exactly this header** and uses decimal SI coordinates:

```csv
pair_id,session_id,condition,time_ns,coil_current_a,dipole_sign,force_n,gradient_t_m,moment_calibration_id
p0,s0,sham,10,0,1,0,0,pos
p0,s0,active,15,1,1,-0.0001,-0.01,pos
p1,s0,sham,20,0,1,0,0,pos
p1,s0,active,25,-1,1,0.0001,0.01,pos
p2,s1,sham,30,0,-1,0,0,neg
p2,s1,active,35,1,-1,0.0001,-0.01,neg
p3,s1,sham,40,0,-1,0,0,neg
p3,s1,active,45,-1,-1,-0.0001,0.01,neg
```

Those eight rows are **synthetic examples**, with arbitrary `time_ns` labels, not a reported physical experiment. Positive/negative dipole rows could be the same magnet reversed: the signed calibration rows must explicitly share one physical magnet key. They must not be represented as two independently calibrated magnets.

The calibration JSON (same `apparatus_id`, `configuration_revision` and `instrument_serial` as both source-envelope JSON and input metadata) must include:

```json
{
  "calibration_revision":"cal-v1",
  "moment_calibration_groups": {
    "pos":{"moment_am2":0.01,"moment_std_am2":0.001,"shared_magnitude_id":"magnet-A"},
    "neg":{"moment_am2":-0.01,"moment_std_am2":0.001,"shared_magnitude_id":"magnet-A"}
  },
  "force_readout_std_n":0.000001,
  "gradient_readout_std_t_m":0.0001,
  "common_force_offset_std_n":0.000002,
  "gradient_calibration_fractional_std":0.02,
  "coil_sham_max_abs_a":0.002,
  "coil_active_min_abs_a":0.1,
  "max_pair_gap_ns":1000
}
```

These numbers are **illustrative assertions**, not verified calibrations, power statements, accuracy guarantees or real-world experiment tolerances. The original source-envelope JSON contains `pair_to_stream_reducer: "S1-CSV-v1"`, `stream_unit_convention: "SI"`, actual stream path and `instrument_source_stream_sha256`, and the deterministic `pairs` equal to replay output. The input metadata separately hashes **both the original source-envelope bytes and calibration-file bytes**. Shared-magnitude ID establishes a proposed physical covariance group across polarity, and GLS rejects inconsistent absolute moment magnitudes or uncertainties within that ID.

**Derived records:** for each complete active/sham pair sharing session/calibrated moment, compute `delta force = F_active - F_sham`, `delta gradient = g_active - g_sham`, ordinary fixed-point-dipole prediction `m * delta gradient`, signed residual and explicitly correlated GLS error. All labelled `moment_covariance_group_id` fields originate from the calibration record, not from user-supplied invented trial labels. Factorial rank uses **replayed** signed currents (thresholded to -1,0,+1), dipole sign, interaction and squared-current proxy. Six independent *settings* give rank five for this particular linear model; they cannot independently identify every possible nonlinear/thermal/biological mechanism.

**Why the opposite-polarity covariance matters:** if the physical magnitude error of one magnet is `δm`, errors are `δF_i = s_i g_i δm` with orientation `s_i = ±1`. Thus `Cov(δF_i,δF_j) = s_i s_j g_i g_j u_m²`, which can be **negative** for reversed moment relative to identical gradients; a symmetric pair can cancel that one common nuisance by design. Blindly making positive and negative signs different *independent* calibration IDs underestimates or misreports this covariance. Independent local NumPy 2×2 check with gradient `0.01 T/m`, moment uncertainty `0.001 A·m²` and readout noise `10⁻⁶ N` produces covariance off-diagonal `−10⁻¹⁰ N²` and common-moment cancellation under equal weights, leaving `7.071×10⁻⁷ N` random standard uncertainty. **This is mathematics, not an observed effect.**

### Standards and attribution

- Classical field and force: Biot–Savart (Biot and Savart, 1820), Maxwell electromagnetic theory, magnetic dipole force in a field gradient; *separate* from nonconventional gravity and any proposed psychotronic mechanisms. Existing [Fourier/filament reuse audit](psychotronics-biot-savart-prior-art-weld-20261025.md) retains DASHI's exact `NSTriadKNFourierBiotSavartExact` and its Maxwell bridge as the correct formal owners. **Do not reimplement either law or infer Fourier/finite-filament proof from this CSV transformation.**
- Correlated uncertainty: **JCGM 100:2008**, *Evaluation of measurement data—Guide to the expression of uncertainty in measurement*, issued by Joint Committee for Guides in Metrology; [BIPM DOI](https://www.bipm.org/en/doi/10.59161/jcgm100-2008e) specifies treatment of correlated inputs. **NIST Technical Note 1297, §5**, [official reference](https://www.nist.gov/pml/nist-technical-note-1297/nist-tn-1297-5-combined-standard-uncertainty), explicitly combines uncertainty with covariance where appropriate. DASHI authors the particular GLS and CSV transport implementation; do not attribute it to a specific original scientist from the investigation solely because their work is technically related.
- **Egely & Vértesy**, `psychotronics-egely-vertesy-primary-magnetic-anomaly-audit-20261025.md`: their author-reported **VSM hysteresis/susceptibility material changes** are separate experimental claims. They are **not** measurements of our S1 permanent-dipole fixed-moment law. A proper VSM experiment requires its own sample state/handling/hysteresis/contamination/time/independent-mount protocol and magnetic constitutive model. Their paper, scan, transcription, and later press are different *carriers*, not multiple independent modern replications.
- Amy Eskridge historical HAL5 slides, Li & Torr superconducting models, NASA R. H. Eskridge POAMS study and historical Pavlita author reports remain attributed independently. No dataset in this PR establishes an anomalous gravitational interaction, medical effect, a shared covert programme or a connection between persons' life events.

## Validation ledger and remaining work

**Locally executed in this continuation:** five isolated reducer-regression test groups passed on the exact locally authored module: four complete trial pairs, two sessions, six rank-capable signed arms, incomplete/duplicate/mislabelled/invalid-numeric/time/calibration rejection; also an independent NumPy test of the signed-magnitude shared covariance. This is **not** a test of an actual physical sensor or an Agda kernel result. A fuller end-to-end regression was additionally source-written into the GitHub branch, but the current runtime cannot fetch its actual GitHub source into a local checkout; do not claim the committed end-to-end source has run or that GitHub CI passed.

**Still unpaid / do not promote:** external instrument identity, trustworthy source timestamps, laboratory calibration, independent operator, actual measured field/current/force/timebase, independent reduction review and numerical pass of GitHub-resident full suite, constitutive errors/thermal/vibration/EHD, real VSM sample results, source-specific gravitational observation, replication. `submission_ready_for_independent_metrology_review` remains a **self-declared structural dossier** flag and `gravitational_result_admissible` remains hard false. A source hash or a metadata Boolean cannot discharge these producer obligations.

**Next Pareto decision:** acquire *one real controlled* pair source with truly independent calibrated current, 3-axis field and force-balance data and a timestamped polarity/sham protocol. The software is now capable of deterministic source-pair replay and documented failure, but without real apparatus data further ideal coil codes have rapidly diminishing physics value.
