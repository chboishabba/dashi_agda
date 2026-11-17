# Local exact-GitHub-source Python verification — 25 Oct 2026

This receipt applies **only to two Python scripts and the attached SRT**. It does not certify Agda compilation, authentic DOJ PDF pages, heritage damage, clinical/psi findings, or future-to-past signalling.

## Environment and byte equivalence
- Runtime: Python 3.13.5, standard library only.
- Exact source `scripts/zorro_tsfv_source_temporal_audit.py`: 9,037 bytes. Local `git hash-object` = GitHub exact branch blob **`d78350b67dc08de1730f82d277188d1bbca3c7f1`**; local SHA256 `7fbb65041dfbf6e248d7b5d821703840c562c3ad88198add7726d1cca9780d8f`.
- Exact source `scripts/zorro_tsfv_qubit_abl_exact.py`: 3,505 bytes. Local `git hash-object` = GitHub exact branch blob **`b056b8e38eafb9d1904a92e760a43aacf7894aab`**; local SHA256 `4ba1d48c246fc054a7231d006ff080583f0f552af93b24a2047fe402cf8fe383`.
- Source SRT: `transcript-2026-10-24 (4).srt`; observed SHA256 = expected `7811bb6f538dace90a7febace011c61569d31d2efd1300acfc8b5e960a7887ab`. The script with `--transcript` accepted it.

## Actually executed
```sh
python3 zorro_tsfv_source_temporal_audit.py --self-test --transcript 'transcript-2026-10-24 (4).srt' --json
# Ran 12 tests in 0.001s — OK

python3 zorro_tsfv_qubit_abl_exact.py
# Ran 7 tests in 0.001s — OK
```

The first script checks root deduplication, duplicate-ID refusal, same-email-lineage root, same NMDOJ institutional root, exact classical `(1,1)` preselection vs later-filtered `(1,0)/(0,1)`, normalization and nonpromotion. 11 records reduce to **7 declared source roots**, not 7 independent empirical observations.

The second script is a genuine **exact rational 2-dimensional projective qubit** `|+>` and intermediate/final Z measurement example. Its bare amplitude table is `[[1,0],[0,1]]`, where the common physical ket factor `1/sqrt(2)` is restored in each joint probability. The joint probability table is `[[1/2,0],[0,1/2]]`. ABL postselected earlier-Z probabilities are `(1,0)` given final-Z=0 and `(0,1)` given final-Z=1, while marginalizing *over all final outcomes* recovers the original Born `(1/2,1/2)`. This concretely pays the ABL conditional/marginal example under a normal Hilbert-space interpretation without asserting that the later measurement outcome can be set at will.

The original formula's source is **Aharonov, Bergmann & Lebowitz (1964), Physical Review 134 B1410**, DOI `10.1103/PhysRev.134.B1410`; these calculations are this repository's finite test, not a new discovery of ABL.

## Still explicitly unverified
Agda exact-branch kernel typechecking and integration; original DOJ PDF original-byte/page verification; whether any stone was polished; rock/artifact identification or legal findings; whether a WingMakers-Zorro association exists; real anomalous information access; any physical backwards-in-time intervention.

This local result is not CI and not a whole-repository test.
