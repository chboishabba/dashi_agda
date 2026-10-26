# DMT newly uploaded source files — integrity, event replay and oversized ZIP gate (27 Oct 2026)

## Original owners, independent source and scope

The original human studies and deposited content belong to **Niedernhuber et al.** (Journal of Psychopharmacology 2026, DOI `10.1177/02698811261481062`; Zenodo version DOI `10.5281/zenodo.18850897`) and **D'Amelio et al.**, original bioRxiv preprint 4 May 2026 DOI `10.64898/2026.04.30.721872`, Zenodo version `10.5281/zenodo.19893951`, with the separate Lewis-Healey original EEG analysis sharing a source acquisition lineage. Original source code and Tait/Zhang +microstate statistics remain their respective original authors' work. DASHI source-specific formalisation/verification is under Johl Brown research direction with ChatGPT assistance. This is **not** a new human-cohort finding or external-agent experiment.

## Current user Drive source root (read-only)

The user explicitly reports completed uploads into their own `tmp_dmt_lol` folder. Direct connector listing on **27 October 2026** shows **26 entries**, including `original.zip` **1,080,998,726 bytes**, `derivatives.zip` **2,653,877,134 bytes**, **eight `.set` files and eight `.fdt` files**. All existing files were preserved and no raw EEG files were committed to GitHub.

New metadata (.set) files present for **1002, 1004, 1009, 1021 and 1031**. Both source halves are in the folder for 1001, 1002, 1004, 1009, 1021, 1031 and 1041; **1006_equalised.set** and **1023_equalised.fdt** remain the only partner omissions among the eight uploaded EEG prefixes. File pairs are deliberately keyed by identical pseudonymous four-digit prefix, not positional list order.

## Actual executed byte and epoch integrity: new five pairs

Using the user-uploaded original Zenodo 18850897 API-shaped JSON (not an authenticated live API call), local Python `hashlib.md5` compared every byte of the **five new pairs (10 files, 88,999,736 bytes total)** with the depositor-identified `name→size/md5` metadata; **10/10 exact matches**. SciPy independently parsed each genuine `.set` and checked the associated `.fdt` payload has the expected size `64×128×epochs×4` bytes. The corresponding genuine `<f4` 32-bit recordings were inspected for non-finite values: **20,742,144 float32 values, all finite**; numeric samples were not used to infer clinical effects or fit microstates.

| Source prefix | Recorded source epochs | DMT arm | Harmine arm | Placebo arm | Original explicit visit ids DMT/harmine/placebo |
|---|---:|---:|---:|---:|---|
| 1002 | 498 | 166 | 166 | 166 | 2/3/1 |
| 1004 | 348 | 116 | 116 | 116 | 1/3/2 |
| 1009 | 564 | 188 | 188 | 188 | 2/3/1 |
| 1021 | 567 | 189 | 189 | 189 | 3/2/1 |
| 1031 | 555 | 185 | 185 | 185 | 2/1/3 |
| **Total** | **2,532** | **844** | **844** | **844** | Participant-specific |

Each original `.set` contains a small number of `X_DMT`/`X_harmine`/`X_placebo` **arm-only boundary epochs**, with **no explicit visit id** for the boundary epoch itself. Audit owner `scripts/audit_dmt_eeg_recording_epochs.py` has been corrected to count the arm-only boundary epochs in its **total arm** rather than accidentally undercount by one, and now reports separately counts carrying explicit visit metadata. The count-vs-visit distinction is a source fidelity requirement: one cannot claim explicit per-epoch visit mapping from `X_arm` alone. These labels correspond to the original DMT+harmine/harmine/placebo protocol; label `DMT` is not standalone DMT ontology.

**Aggregate checkpoint:** prior user-upload verification covered **11 EEG files**, of which 2 were `.set/.fdt` pairs and one an unpaired `.set`; five new `.set` files were added and their five previously-verified `.fdt` partners rechecked here. Current verified **seven complete original byte-checked pairs** and one unpaired `.set` (1023) plus one unpaired `.fdt` (1006). This is enough for partial source metadata replay only, not original plusmicrostate clustering, G1, or a significance estimate.

The exact new local **aggregate-only** integrity receipt is `dmt_new_eeg_pair_integrity_20261027.json`, SHA-256 `adfa6ccf1e595a544a4d9bb3afb471cc5eec8116ff8ab54504b7c65bf6732c0c`; it contains no raw signal values. The local direct byte tests were executed. **No blanket claim that new repository source files have passed a full test suite or Agda kernel check is made.**

## Both original ZIPs arrived — access vs verification

The Drive connector's `fetch(download_raw_file=true,include_base64=false)` refused **both** 1.08GB and 2.65GB uploads with HTTP **413**, reporting a **268,435,456-byte download limit**. A second path using connected Google Drive's Library `files.materialize` also returned **413**. A local direct HTTPS probe for the public Zenodo archive endpoint failed DNS resolution in this runtime; the public web text tool could not retrieve the original Zenodo record API response. Thus **neither ZIP's original SHA-256 has been computed here, their central-directory member inventories were not read, and no original D'Amelio 15-dimensional TET traces were loaded**. Mere Google Drive presence proves neither full integrity nor n17/n18 TET inclusion.

The user-uploaded `sha256sums.txt` already provides original `original.zip` SHA-256 **`365e6dcf7088e0bf35fb152ba73da9ab05dd36722a2b98db56e621ca699c32b1`** and `derivatives.zip` SHA-256 **`abd34cd04feab38c6c2fdc3b2acf200e2df1a47bb503acabe4c3beea789170d5`**. Their validation remains open, not silently paid.

**Smallest possible source-access payment:** committed [source-SHA-gated, traversal-rejecting TET-only extractor](../../scripts/extract_dmt_tet_source_subset.py) and [seven synthetic archive tests](../../tests/test_extract_dmt_tet_source_subset.py). When invoked **on a machine that possesses the entire original.zip**, this checks the full archive's SHA-256 against `sha256sums.txt`, selects only original `reports/resampled/*.mat` at paths below that prefix, screens member paths, duplicates, symlinks, sizes and total uncompressed bytes, and optionally emits a **new non-overwriting <=250MiB TET-only ZIP**. The script requires a source `original.zip` file to verify; it does not fetch archives, run without data, or attest privacy/ethics from a code label. The 7 extractor tests and 7 synthetic MATLAB event tests were **run locally at the exact GitHub blob contents** with all **14/14 PASS in 0.026 seconds**. Git blob identities: extractor `35b7c92aaa219c70466ff8b9412f9fe1064e35aa`, extractor tests `f71d2ca52b2db7188e948639f4d669b807c028a2`; EEGLAB event audit `72e149cc406407e47a7e218f6b5da712845fd26f`, event tests `22c97082298790c2693e49ec0d2dfbd4be14604f`. This is **focused Python regression execution, not an Agda kernel check or full repository suite**. The full `derivatives.zip` remains blocked unless split/transferred by another supported path; it is not required to settle the retrospective TET n17/n18 source matrix count first.

Suggested local command (from a checkout of this branch, no source ZIP committed):

```bash
python scripts/extract_dmt_tet_source_subset.py /path/to/original.zip /path/to/sha256sums.txt --output /path/to/tet-only.zip
```

Then a user may place `tet-only.zip` into `tmp_dmt_lol` (if the archive is below the connector's 256MiB cap). **The author's full original archive and our current research are not thereby redistributed into GitHub.**

## Pareto/source admission and next discriminator

1. Pay the full ZIP hash once original.zip is accessible, then inspect the exact original `n_bins×15` TET matrices and reconcile **17 rows flagged `included_tet`** in uploaded participants.tsv versus **18 TET cases** in source narrative, including any session-specific missingness. Leave both facts visible until same-source reconciliation.
2. Complete the only missing partner EEG files for 1006 and 1023 if desired; then replay the original `getconds` source plus +microstate G1, which the current source labels and float finiteness do not establish.
3. Use original M0/M1a/M1b/M2 model cards and whole-participant split. Retrospective TET next-point prediction remains a statement about reconstructed reports, not a demonstrated future forecast or a test detecting a physically independent conscious entity.
