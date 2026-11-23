
# Paper 9 π P0 — master-native GMP consolidation (23 November 2026)

## Identity, goal and source boundary

**P0 objective:** fastest independently certified π. No external SOTA comparator
has been executed (deferred), so no record or world-leading claim.
The previous research PR [#1529](https://github.com/chboishabba/dashi_agda/pull/1529)
remains OPEN and diverged heavily from current `master` at inspection
(35 ahead, 85,317 behind). None of its three key GNU GMP C++ sources
was at the corresponding path on `master`; this branch starts directly
from `master`, without wholesale merging the diverged PR.

Byte-for-byte original restoration from #1529, with GitHub verified
matching Git **blob SHA**:
- `scripts/check_pi_gmp_fused_certificate.cpp`: `e356a56f33126059f2b1fa0db3b6668eeb747e80`
- `scripts/check_pi_gmp_quotient_residual.cpp`: `28f4657e5bdbfc27ebb7cc3690f6144590ba2d5e`
- `scripts/check_pi_gmp_codec_memory.cpp`: `82027bc7acee4b4711f0ca1a2ed42dce1d60b8c5`

New `scripts/check_pi_p0_consolidated_acceptance.py` compiles those
**original exact Git blobs** with C++17/GMP/OpenSSL, checks prior
SHA-256 exact decimal strings for 10k, 100k, 500k and 1M.
Its optional `--large` validates 5M and 10M using the original
in-place backend (bounded cost); no source mutation or network required.
The consolidated test harness was committed and GitHub-read-back,
but has not been rerun on the committed branch's exact bytes here.

The classical Chudnovsky identity and alternating-tail bound are
**external analytic premises**, while integer sqrt bound, ordered
P/Q/T binary splitting and integer-floor equality produce an
exact conditional decimal certificate. Same-original-Bishop
real identification, independent source-theorem proof, and
all-future-consumer identity are OPEN, not inferred from hash parity.

## Fresh local GMP scaling study, separate source authority

A locally constructed `/mnt/data/pi_p0.cpp` was compiled
`g++ -O3 -std=c++17 -Wall -Wextra -pedantic -lgmpxx -lgmp -lcrypto`.
It implements **mathematically equivalent** fused plain/in-place
P/Q/T, sqrt interval, exact one-quotient strict upper-bound gate
and two-quotient control with decimal hashing. **Not byte-identical**
to the committed historical source. All twelve initial
precision/mode settings at d=10k,100k,500k,1M match existing
exact output SHA-256 receipts with one terminal certificate
attempt and no digit mismatches.

Single-process within-run three-repetition medians (milliseconds,
initial sweep; deliberately preserve noise, no winner promotion):
| places | plain one floor | plain two floors | in-place one floor |
|---:|---:|---:|---:|
| 10000 | 2.004 | 2.063 | 1.642 |
| 100000 | 45.633 | 47.628 | 47.130 |
| 500000 | 310.472 | 343.911 | 306.816 |
| 1000000 | 775.368 | 705.065 | 730.620 |

A separate repeat at 1M gave 831.401 / 720.433 / 664.695ms,
respectively: mode timings fluctuate considerably. The
historical ~699ms is a previously reported *internal* baseline,
not a guaranteed replay on the current hardware/container.

New large-precision independent single invocation receipts:
| places | mode | elapsed ms | peak RSS KiB | terminal P+Q+T bits | attempts |
|---:|---|---:|---:|---:|---:|
| 5000000 | plain one floor | 5177.983 | 133004 | 99827455 | 1 |
| 5000000 | in-place one floor | 5339.544 | 131460 | 99827455 | 1 |
| 5000000 | plain two floors | 5830.217 | 129852 | 99827455 | 1 |
| 10000000 | in-place one floor | 11880.961 | 265988 | 206083400 | 1 |
| 10000000 | plain two floors | 12472.854 | 260868 | 206083400 | 1 |

These are **not** same-run medians or cross-device comparators.
At 10M about 260 MiB peak RSS is observed; runtime around 12s.
At 5M about 129MiB RSS, runtime around 5–6s.
The separate figures cannot establish statistically meaningful
compute-memory Pareto superiority. They exclude compilation
and process startup, but include split, integer isqrt,
endpoint arithmetic, floor gate, decimal conversion, and SHA256.

Exact decimal floor SHA256 (string begins with 3 and has d+1 digits,
no decimal separator):
| digits | SHA256 |
|---:|---|
| 10000 | `ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524` |
| 100000 | `79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711` |
| 500000 | `fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9` |
| 1000000 | `130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18` |
| 5000000 | `09eb526274ac828a3a54614e72fac5baa8ab6b26b8484fe1b065f678b2c8dbad` |
| 10000000 | `ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999` |

## Next P0 maximum cut

1. Re-run the **committed exact-source** harness on local master-based
   branch; keep the original code as baseline, do not replace historical
   results with independent prototype timings.
2. Reconcile speed/peak-RSS by rotated-order distinct processes
   at 1M,5M,10M; obtain per-stage GMP limb high-water memory
   and throughput; identify actual endpoint products causing growth.
3. Integrate one-floor/in-place into a single production implementation
   *only after* exact output and cold/hot matched regressions.
4. Evaluate source-preserving endpoint factor sharing,
   truncated products/streaming, measured multiplication scheduler
   rather than speculative RH coordinate/SWAR codec reordering.
5. Ultimately benchmark independent SOTA only when user resumes
   external comparison; it remains P0 goal despite execution deferral.

The CM residue/CRT/PQT ternary/SWAR work is a research donor, not
a proven faster GMP big-int multiplication backend. No GPU, Agda,
Lean, GH CI or external SOTA execution in this tranche.
