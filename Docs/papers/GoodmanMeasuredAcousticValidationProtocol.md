# Real measured acoustics: inverse uncertainty and held-out benchmark protocol

Status: **specified from primary dataset documentation; NOT data-downloaded, fitted, benchmarked, or kernel-verified** (2026-10-28). This is an empirical acquisition lane, distinct from the T1–T10 synthetic Agda results.

## Primary data and owner attribution

1. Adam Kujawski, Art J. R. Pelling, Ennes Sarradj, *MIRACLE—a microphone array impulse response dataset for acoustic learning*, EURASIP Journal on Audio, Speech, and Music Processing (2024), DOI [10.1186/s13636-024-00352-8](https://doi.org/10.1186/s13636-024-00352-8). Current version 4 published data [10.14279/depositonce-20837](https://doi.org/10.14279/depositonce-20837), CC BY-NC-SA 4.0. The previously cited [10.14279/depositonce-20106](https://doi.org/10.14279/depositonce-20106) is a superseded version (3); never mix archive hashes or scenario files across these two versions. **Original authors** own measurements, source positions, calibration analysis, deconvolution method, original results. 856,128 measured single-channel room impulse responses (RIRs), 64-channel array, four source/medium scenarios; three anechoic and one specular reflective. Acquisition sampling 51.2 kHz; RIR post-processing uses resampling to 32 kHz; source location uncertainty assessed statistically with scenario-dependent millimetre-scale intervals. Authors acquired two background and two excitation measurements per source location using a loopback. Published final RIR files are not necessarily full raw replicate recordings; check actual files and metadata before claiming sample-level noise covariance.
2. Hendrik W. Löllmann, Christine Evers, et al., *LOCATA Challenge Data Corpus*, IEEE SAM (2018); Christine Evers et al., *The LOCATA Challenge: Acoustic Source Localization and Tracking*, IEEE/ACM TASLP 28 (2020), DOI [10.1109/TASLP.2020.2990485](https://doi.org/10.1109/TASLP.2020.2990485). [Official dataset and evaluator](https://www.locata.lms.tf.fau.de/datasets/). Multiple recorded arrays with independent OptiTrack source/sensor coordinates and source voice activity; appropriate for direction-of-arrival / tracking external validity; **not proof of absolute pressure calibration**. Follow the supplied Open Data Commons licence notice and source-paper attribution.
3. James Eaton, Nikolay D. Gaubitch, Alastair H. Moore, Patrick A. Naylor, *Estimation of Room Acoustic Parameters: The ACE Challenge*, IEEE/ACM TASLP 24 (2016), 1681–1693. [Official dataset](https://www.imperial.ac.uk/speech-audio-processing/projects/ace-challenge/). Measured RIRs and ambient/fan/babble recordings in seven rooms; measured T60 and DRR targets. Registration required; CC BY-ND 4.0 restrictions; do not redistribute modified corpus data.
4. Jacques Hadamard (well-posedness), A. N. Tikhonov (regularisation) and primary source authors retain mathematical/empirical priority. Steve Goodman (2009, DOI 10.7551/mitpress/7999.001.0001) remains the cultural source, not author of an acoustics instrument or dataset. Existing DASHI inverse/rational/provenance owners own their original proofs; this protocol is not a kernel theorem. Preserve Ibrahim Monster 3B ownership and proof non-promotion.

## T8 measured two-channel uncertainty contract

Let source-state pair be (x,y), measured channels (a,b) = (x+alpha, x+q*y+beta), and recovery parameter r with independently justified calibration r*q=1. Then recovered-state error vector is

    delta = [alpha, r*(beta-alpha)]^T.

Write mean measurement bias mu=(mu_alpha,mu_beta)^T and joint **measured** covariance

    Sigma = [[s_alpha^2, c_ab], [c_ab, s_beta^2]].

Use Jacobian J = [[1,0],[-r,r]]. Exact linear covariance propagation:

    Cov(delta) = J Sigma J^T
               = [[s_alpha^2, r*(c_ab-s_alpha^2)],
                  [r*(c_ab-s_alpha^2), r^2*(s_alpha^2+s_beta^2-2*c_ab)]].

Expected error is J*mu. The mean-square error for each coordinate is its variance plus squared bias. For a common-mode measured noise c_ab=s_alpha*s_beta with s_alpha=s_beta, the second-coordinate *variance* cancels under perfect shared noise, but the first coordinate remains noisy. The covariance matrix must be positive semidefinite and estimated on held-out-safe calibration recordings. The linear formula is **conditional on fixed known q and r**. To include uncertain gain/geometry, separately propagate Jacobians with respect to them, include cross-covariances, or use grouped bootstrap/Monte Carlo drawing from an empirically justified joint model. Do not silently set the cross-covariance to zero.

For T9 ridge, rho*(q^2+lambda)=1 and z=rho*q*(b-a). At a fixed latent y and zero-mean channel errors, let D = s_alpha^2+s_beta^2-2*c_ab. Then

    bias(z) = -rho*lambda*y,
    Var(z) = (rho*q)^2*D,
    MSE(z) = (rho*lambda*y)^2 + (rho*q)^2*D.

With nonzero error mean, add rho*q*(mu_beta-mu_alpha) to bias. These are algebraic formulas for **synthetic triangular observations**, not a claim that MIRACLE's transfer function equals that matrix. Physical propagation requires a separately validated frequency-domain/spatial forward operator H(f,geometry,medium) and calibrated sensor gains; the measured RIRs can be used to estimate/validate H. Source-position uncertainty (mm) is NOT microphone amplitude calibration (Pa / dB SPL).

## Executable validation design (predeclare before outcome inspection)

**Data acquisition and provenance**: cite primary DOI, version/date, licence, file URLs, and SHA-256 per downloaded archive. Enumerate source positions, array channel geometry, scenario IDs, temperature, sampling rate, impulse units, impulse-response deconvolution, directivity metadata, and availability of raw noise/repeat signals. Stop on absent units, corrupt channels, missing registration rights, or misaligned coordinate frames. Do not backfill absent metadata from plausible values.

**Training**: group all 64 channels, excitation repeats and derived features for a source position into one indivisible spatial group. Select 60% of separated source-position spatial blocks for training; reserve 20% for validation and 20% for **sealed** held-out test using a fixed seeded spatial-block partition, with a physical spacing buffer appropriate to interpolation/reverberation scale. Do not split individual time windows from the same RIR between partitions or randomly split source channels (data leakage). Train on one set of A1/A2/D1 configurations with noise-aware tuning only on validation. Keep reflected R2 as an additional untouched *environmental-shift* test if the research question is generalisation to a reflector. This single reflective scenario cannot establish universal medium generalisation.

**Baselines**: geometrical delay-and-sum/beamformer under documented propagation assumptions; unregularised least squares/pseudoinverse; ridge/Tikhonov with lambda tuned using validation only. Report oracle use of independently known geometry separately from genuinely inferred geometry. No future/test recording may be used to choose preprocessing, filters, q/r/lambda, waveform windows or noise thresholds.

**Primary metrics**: source-position Euclidean error (m), angular DOA error (degrees) when task supports it, complex RIR/transfer prediction error per frequency (with explicit normalization and phase alignment), and out-of-sample reconstruction error. For ACE report T60 and DRR error, never substitute them for source-position accuracy. Stratify by source distance, frequency band, channel pair, geometry, measurement SNR and reflective versus anechoic scenario. Include failure rates and unusable samples, not only means.

**Uncertainty validity**: fit covariance using recorded independent background/repeat segments if the released files include them; otherwise clearly report lack of raw noise replicate support and use separate ACE noise measurements only as *external noise-domain challenge*, not as MIRACLE-measured covariance. Use block-bootstrap by independent source-position or session groups (not by correlated waveform samples); report interval coverage against ground-truth positions, empirical residual calibration, within-group correlations, and bias. Assess stability/conditioning on measured transfer operators with uncertainty bands; the T6 rational family is an analogy, not a substitute.

**Decision rule**: report metrics on sealed test once, compare to a preregistered baseline, and distinguish improved prediction from calibration quality and from causal effects. If neither raw noise nor measured absolute gain calibration is available, state exactly which validation claims remain unmet. These data do not validate Sonic Warfare's social/psychological/historical claims, clinical outcomes, new force, or any Monster same-object theorem.

## Explicit work status / next executable gate

Literature and official dataset pages located and read. **No dataset files have been downloaded, no MIRACLE/LOCATA/ACE sample has been evaluated, no measured Sigma or calibration curve estimated, and no held-out performance score exists in this PR.** The exact formulae above follow conditionally from the already source-written T8/T9 model and can be checked symbolically. The next empirical action is acquire the **versioned MIRACLE dataset** and its real metadata; do not invent numeric uncertainty values. A true measured benchmark requires bytes in the runtime and a validated parser.

## Executable fail-closed intake

`scripts/check_goodman_measured_acoustics_manifest.py` is the newly committed evidence acquisition gate. It checks a **version-4** manifest against DOI `10.14279/depositonce-20837`, CC BY-NC-SA 4.0, archive SHA-256 values and all four original scenario filenames (`A1.h5`, `A2.h5`, `D1.h5`, `R2.h5`). It rejects missing or mismatched files before producing a split receipt.

It accepts *separately supplied and validated source-position metadata* with `scenario`, `position_id`, and `spatial_block`. It groups all microphone channels from the same position, then allocates entire hashed blocks into train/validation/test; scenario R2 is reserved for external-environment evaluation. The algorithm itself does not derive physical block adjacency or enforce a geometric buffer. **It must not be treated as spatial leak-free until source coordinates and block adjacency have been separately validated.** Its nominal 60/20/20 split is hash probability, not guaranteed exact sample counts; inspect the resulting partition sizes and distances.

The `correlated_error_budget` function computes a sample covariance from at least three *independent paired error measurements* and the conditional Jacobian transformation. It does **not** find such measurements inside the MIRACLE HDF5 files. The manifest/split command intentionally emits `measurement_results: null` until a real model and an actual sealed test have run.

Example manifest (replace hashes only after checking actual downloaded files):

```json
{
  "dataset_doi": "10.14279/depositonce-20837",
  "license": "CC BY-NC-SA 4.0",
  "scenarios": [
    {"id": "A1", "sha256": "INSERT_ACTUAL_SHA256"},
    {"id": "A2", "sha256": "INSERT_ACTUAL_SHA256"},
    {"id": "D1", "sha256": "INSERT_ACTUAL_SHA256"},
    {"id": "R2", "sha256": "INSERT_ACTUAL_SHA256"}
  ]
}
```

No dataset archive was obtained or hashed in this execution environment. The command makes that absence a hard failure instead of a fabricated measured validation receipt. The original authors' data copyright/CC obligations, field calibration uncertainty, sample covariance requirements and Agda kernel-verification requirements remain unchanged.

**Updated spatial gate:** The intake command now requires `--min-separation-m` and an `xyz_m` three-coordinate metric list for each source position. It rejects inconsistent coordinates and cross-partition source pairs closer than the declared threshold. This is a conservative pairwise check within each acquisition scenario; it does not prove independence of acoustic responses at larger distances or guarantee exact split proportions. The nested-pair implementation is intended as a correctness-first check and may need spatial indexing for the full 13k-position dataset.

## Read-only measured-HDF5 schema adapter (2026-10-28)

New `scripts/inspect_goodman_miracle_hdf5.py` uses the **published MIRACLE HDF5 file schema**, from the dataset authors' preprint, and requires `h5py`. It opens the four pinned scenario files without materialising their multi-gigabyte response tensors. Required paths: `/data/impulse_response`, `/location/source`, `/location/receiver`, `/metadata/sampling_rate`, `/metadata/c0`, and `/metadata/temperature`. It checks expected source counts **A1 4,096; A2 4,096; D1 1,089; R2 4,096**, 64 microphone channels, coordinate shapes, finite coordinates, physical sampling rate and environmental-vector lengths. It extracts 13,377 position IDs, source coordinates and deterministic metric spatial block IDs for the existing manifest/split gate.

This is a **read-only parser and shape contract**, not a calibration proof. Input archive hashes must be checked separately by `check_goodman_measured_acoustics_manifest.py`. The declared source-coordinate units require dataset-document verification. The HDF5 locations do not establish absolute SPL sensor gains, unmodified microphone response or raw independent noise replicates. If an actual archive's structure differs, the inspector fails rather than substituting guessed measurements.

Execution order once archives are accessible: acquire and hash-pin exact version-4 files; run this schema inspector with a declared `--block-size-m`; run the manifest splitter with `--min-separation-m`, checking nonempty partitions and separation; only then specify a waveform baseline, real calibration samples and a frozen held-out evaluation. **No actual HDF5 archive had been read at the time this note was committed.**

Primary sources: original authors Kujawski, Pelling and Sarradj, journal DOI `10.1186/s13636-024-00352-8`, DepositOnce version 4 `10.14279/depositonce-20837`, and public dataset preprint's Appendix B HDF5 map. The AcouPipe wrapper is independent programmatic prior art, not the owner of our parser or of the original experimental observations.
