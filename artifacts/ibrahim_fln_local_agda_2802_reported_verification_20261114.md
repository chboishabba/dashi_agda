# External local verification report — Ibrahim FLN / PR #1505

**Status:** USER-SUPPLIED LOCAL EXECUTION SUMMARY. This is a second-hand transcription of the run commands and outcome reported in the 2026-11-14 conversation, **not** a machine-generated Agda kernel transcript independently collected by the repository authoring environment. No full Agda stdout/stderr hashes were supplied. Do not present it as a clean, exact-head CI receipt.

## Source / attribution

- Scientific source / historical method: Mark Ibrahim, Christopher M. Danforth and Peter Sheridan Dodds, *Connecting every bit of knowledge: The structure of Wikipedia's First Link Network*, *Journal of Computational Science* 19 (2017), pp. 21–30, DOI **10.1016/j.jocs.2016.12.001**. This report is **DASHI proof-environment verification metadata**; no new original scientific findings or original producer attribution are claimed.
- PR: https://github.com/chboishabba/dashi_agda/pull/1505
- Starting checked-out PR head **4f3599bd6e47f911390d88f2d476231446b355a2** (from user's local checkout report).
- Compiler: **Agda 2.8.0.2**, invoked with `--safe -i . -l standard-library`; not Agda 2.9.0.
- Python: repository `tests/test_ibrahim_fln_reference_analysis.py`, **9/9 passed**; reported local runtime 0.148 seconds.

## Local environment repairs **before** success

1. Several root `.agda-lib` wrapper files conflicted in Agda 2.8+ library auto-discovery. A **temporary worktree** was used to mask/remove redundant root wrappers locally. Do **not** delete or alter canonical repository vendor/library wrappers as a supposed theorem fix.
2. `DASHI/Cognition/PNF/BinaryBalancedTernaryAggregateLossExact.agda`, `countAggregateIsManyToOne` (~line 83), needed an explicit `BinaryComparison4` equality-carrier annotation for Agda's pair-equality type inference. This change **was not in starting PR head 4f3599bd**. It was subsequently committed to the same PR at **5d8d1bd6eaaf7a7694019231d227e8a56fe82b20** so the dependency patch is no longer hidden.
3. The user's local checkout also included **unrelated and apparently broken** uncommitted integration work from commit `7718b4b8` involving an out-of-scope universe level `ℓ` in four DASHI/Core files. Those files were reverted to the clean definitions in the disposable worktree. These unrelated changes are **not** part of PR #1505 and must not be silently included merely to make a test pass.

## Reported tool outcomes

| Run | User-reported outcome | Exact acceptance scope |
| --- | --- | --- |
| Python unit tests | **9/9 pass** | Independent local reproduction of Python reference tests; same-object Python blob match separately documented in `ibrahim_fln_exact_python_test_receipt_20261114.json` |
| Five isolated Agda source modules | **All five passed** after local fixes | Local Agda 2.8.0.2 typechecking with explicit binary equality annotation and clean dependency files; do not claim *unmodified* PR `4f3599bd` passed |
| `DASHI/Wikimedia/Everything.agda` | **exit 42** reported | Aggregate check **NOT accepted** |
| Direct `scripts/check_ibrahim_fln_maxcut.sh` invocation | **exit 126** | Script-executable permission/invocation issue, not proof result; invocation with `bash scripts/check_ibrahim_fln_maxcut.sh` was attempted |
| `bash scripts/check_ibrahim_fln_maxcut.sh` | User reports checks succeeded but only task-polling lines were supplied, not a complete log/exit code | Treat as reported local success; **no machine-verifiable combined exit receipt** |

The isolated pass concerns:

- `DASHI/Wikimedia/IbrahimFiniteOrbitRevisionWeldExact.agda`
- `DASHI/Wikimedia/IbrahimMultilingualHyperfabricWeldExact.agda`
- `DASHI/Wikimedia/IbrahimPublishedSevenNodeFunnelExact.agda`
- `DASHI/Wikimedia/IbrahimFiniteFigureBasinCertificateExact.agda`
- `DASHI/Wikimedia/IbrahimITIRConsumerRepairExact.agda`

## Reproduction / resolution prerequisites

- Re-run the **committed** PR head including `5d8d1bd6` from an isolated clean worktree; verify the exact SHA and absence of the unrelated `7718b4b8` changes. Temporarily mask redundant root wrappers **only within that disposable worktree** when needed.
- Record pinned standard-library/library resolution, `agda --version`, all five complete exit codes, hashes of source files and any modified local dependency files, and command transcript. Use `bash scripts/check_ibrahim_fln_maxcut.sh` unless the file mode is made executable in Git.
- Independently replay Agda 2.9 if that is the chosen pinned golden compiler. A successful 2.8.0.2 run is valid for its own toolchain but not a 2.9 receipt.
- Keep `Wikimedia/Everything.agda` **OPEN** until its exit 42 is diagnosed and a clean aggregate pass is observed.
- Do **not** confuse finite-formal/fixture acceptance with a real multilingual article/first-link source, a reviewed repair, complete 2014 dump reconstruction or a modern language census.

## Promotion boundary

**Promote:** user-reported local Agda 2.8.0.2 isolated 5/5 success *under stated local repairs*.

**Do not promote:** unmodified original PR-head typechecking, full aggregate success, canonical Agda 2.9 golden acceptance, general graph certificate completeness, any historical original producer run, a genuine two-edition Wikipedia repair, real ITIR consumer truth/authority or universal cultural conclusions.

The source annotation commit is a **subsequent DASHI maintenance change**, not part of the original Ibrahim or Gabella authors' historical source.
