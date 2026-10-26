# Niedernhuber Zenodo checksum provenance correction — 2026-10-27

## Source object and priority

Original human study: Niedernhuber, Suay, Lenggenhager, Müller, Scheidegger, Dornbierer and Aicher (2026), DOI 10.1177/02698811261481062. Original Zenodo version DOI 10.5281/zenodo.18850897. Original software is marianiedernhuber/DMT_microstates at commit c5c064d109563e97127403a8fbb340009ba1e88b; source G1 from Tait and Zhang's +microstate implementation. These are the original authors' findings, data, code and statistical lineage.

The earlier DASHI manifest listed 25 file pairs (50 file names) and manually transcribed 50 purported MD5 values. A previous source-authentication claim was **too strong**: a subset of copied strings was manually repaired to syntactically valid 32-character hexadecimal strings, but was NOT rechecked against the original Zenodo metadata. Even valid MD5 syntax and a pinned Git blob hash of our own transcription cannot certify that each value equals the original depositor's checksum. This is not a finding that the original deposited files were altered, or that the original experiment was invalid.

## Corrective changes actually committed

- `Docs/receipts/DMTNiedernhuberZenodoListing20261025.json` now explicitly classifies the checksum map `unverified_manual_transcription_not_source_authentication`, and `authoritative_zenodo_md5_listing_verified=false`, while retaining documentary cohort source and file names.
- `scripts/audit_dmt_niedernhuber_zenodo.py` has a repinned Git blob identifier and **fails closed if a purported participant dataset is supplied for checking against the copied MD5s**, even if a textual external review receipt is supplied. Directly supplied synthetic expected digests can still be checked through a distinct low-level hash helper, not promoted as source reproduction.
- `tests/test_dmt_niedernhuber_zenodo.py` replaces a hard-coded assertion of one unverified digest with a syntax-only assertion plus an explicit **not-authenticated** indicator. Tests reject false promotion of the checksum status; synthetic digest tests retain their finite checking value.
- Original checksum integrity remains unverified until a version-locked authoritative `zenodo.org/api/records/18850897` manifest is obtained, each of the 50 `name→checksum` joins is checked, and data-use authorization is reviewed. No new original EEG files were downloaded, modified, or processed.

This is an epistemic/evidence-integrity repair, not a completed original-record checksum payment. Python test source was committed and blob read back; no full or exact-head local suite execution was performed in this turn. No Agda kernel or original human EEG experiment replay claimed.

## Latest cross-PR and source search

GitHub PR #1243 checked against latest updated sibling PRs including #1272 (Fourier-pixel measurement discriminators), #1271 (PDE source-bound acceptance), #1268 (original-root source claims) and #1266 (consumer-specific observation sufficiency). Those are **methodological donors** only, not separately imported or proven by this cut. Current DMT source-world/motif model cards and the participant-heldout synthetic TET path remain existing owners.

Web searches for D'Amelio's versioned Zenodo source **10.5281/zenodo.19893951** did not produce an authoritative file list; direct access to Zenodo version URL and API returned inaccessible. The original public author code and prior source-linked schedule still ground a 19-person **design** crosswalk, not measured subject ratings. The source's `entity` is a retrospective perceived-presence rating, not an independently confirmed external agent.

## Pareto and Ibrahim stop

Highest downstream gain is from the **same-source object**, not multiplying derived summaries: original version-locked Zenodo D'Amelio participant/source objects and Niedernhuber's authoritative 50-file checksums, rights and executed crosswalk. They would unlock valid source-admission checks and empirically grounded model contrast. Neither source's unavailable bytes, consent/ethics status, nor experimental measurement can be replaced by a synthetic fixture or self-reported receipt.

User-approved temporary Google Drive staging folder was created solely for this turn (`TEMP_DASHI_DMT_maxcut_2026-10-27_delete_after`) but received **no files**; folder deletion subsequently returned success. No user pre-existing Drive file was changed. All lasting implementation belongs in the GitHub PR, not in the temporary staging location.
