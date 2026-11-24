
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


## P0 correction — reuse existing formal performance / optimization machinery (23 Nov)

**Do not reinvent the optimization formalism or treat one number of
seconds as its replacement.** The canonical, pre-existing source
owners on `master` are:

- `DASHI/ComputerScience/FibreProgramComplexityExact.agda`:
  `ComplexityProfile`, `ExecutionFibrePath`, consumer-indexed
  sum/peak/head-travel costs; Git blob
  `275abb34923b91c5c1649c4484f7c520bfc015c6`.
- `DASHI/Core/EfficientRecoverableQuotientExact.agda`:
  independently charge quotient construction, receipt storage
  and reopening; blob
  `050e3c36d14bfe86e77ce6ef7ccb3ccd4565e201`.
- `DASHI/ComputerScience/StreamingResidencyComplexityErrorDNABidiExact.agda`:
  semantics-preserving bounded streaming versus eager residency,
  and resource versus transport failures; blob
  `a703293287cff776644c379f0e378613fd8b6e36`.
- `DASHI/ComputerScience/FibreMachineFoundation369Exact.agda`:
  consumer-relative adequacy of representations/cost paths,
  blob `879784c7e6e1667d984bcbbc865255ac1a21dbcc`.
- `DASHI/ComputerScience/EuclidGCDRegisterMachineExact.agda`:
  actual machine trace/transition/head-path cost consumer,
  blob `8eed7e1dbfc5f917aac6eeda9237286ebe323af6`.
- Existing `Docs/papers/drafts/Paper9ExactCMModularJetCertificates.md`
  **section 10.1–10.4** already defines physical bit widths, actual
  peak and summed live integer payload, register/scratch/copy,
  bit-operation models M_int(B), D_int(B), and measured p50/etc.
  It states a conservative fixed-constant binary split bound
  O(M_int(d log d) log d) plus sqrt/final division. The bound is
  conditional on conventional fast integer-multiplication
  assumptions, and is not a proved machine-level execution theorem.

**Concrete Pi P/Q/T execution fibre**, to instantiate rather than
replace those existing Agda definitions:
- state = (original leaf interval [a,b), P,Q,T, finite series
  endpoint signs, current sqrt precision, certificate candidate,
  allocator live buffer sizes and source/receipt IDs);
- transitions = exact Chudnovsky leaf construction, ordered
  P/Q/T merge, optional gcd/cancellation, sqrt, endpoint
  products, quotient, strict upper boundary comparison,
  serialization and independent verifier;
- path time cost = sum of type- and width-indexed
  multiplication/addition/square-root/division/serialization
  costs plus actual memory movement, allocation and teardown;
- peak memory = max over path states of live GMP allocated limb
  bytes including temporary products, retained tree states,
  scratch and receipt buffers; process RSS is an **empirical
  upper envelope/proxy**, not the same formal quantity;
- consumer = exact interval enclosure, certified decimal-floor
  integer string and its independent verification (plus original
  Bishop same-real target as a *separate OPEN* consumer).
  SHA-256 equality is a regression, not a mathematical certificate.

**Pareto admission for an optimization `new` against `base`:**
1. consumer/source preservation first: same ordered rational
   interval or a formally proved refinement sufficient for the
   requested decimal floor; maintain signed zero/residual, analytic
   premises and independent verification;
2. measure matched distributions of end-to-end wall time and
   separately construction, receipt and reopen/verification costs,
   pinned compiler/GMP/hardware/temperature and cold/hot runs;
3. compare actual allocated live limbs, peak RSS, memory
   movement and peak scratch separately; a faster result with
   higher residency is a *trade-off*, not overall Pareto dominance;
4. optimize constrained target throughput under declared memory
   budget, and retain the full time-memory-verification Pareto
   frontier rather than a single misleading scalar;
5. test 1M/5M/10M and scaling, include output conversion,
   certificate generation, source recompilation and tests in
   their respective separate ledger columns. Do not conflate
   asymptotic upper bounds with empirical median wall times.

**Named next P0 weld:** add original-GMP source instrumentation
producing path-indexed `(operation type, input/output bitlength,
allocation/reallocation size, live limb high-water, elapsed)`
records. Feed these into the existing sum/peak cost consumers,
and recover a measurement/model residual by comparing predicted
bit-operation cost to observed wall time. Test whether
the two-floor, one-floor, in-place and projective strategies
are consumer-equivalent and which are actually time-space Pareto.
Only then promote one production default. Formal Agda
instantiation and kernel replay remain OPEN; do not call this
roadmap note a kernel proof or a completed machine cost theorem.


## 23 November — COMP5g: real GMP heap execution-fibre and endpoint-lifetime Pareto

**Reuses rather than replaces** the already existing execution-cost algebra:
\`FibreProgramComplexityExact.agda\` sum/peak path consumers,
\`EfficientRecoverableQuotientExact.agda\` construction/receipt/reopen
costs, and \`StreamingResidencyComplexityErrorDNABidiExact.agda\`
same-outcome residency refactoring. Original Paper 9 §10 is the
bit-cost model; these additions are native *measurements* for its
concrete Chudnovsky P/Q/T execution path, not new Agda kernel proofs.

Source \`scripts/check_pi_p0_fibre_cost_profile.cpp\` is a separately
preserved instrumented derivative of original
\`scripts/check_pi_gmp_codec_memory.cpp\`. Each merge records the
**four ordered product operands** (P_L P_R, Q_L Q_R,
T_L Q_R, P_L T_R), one additive combination, max operand and result
bit widths, full tree merge count, schoolbook product bit-pair
PROXY and an explicit live-carrier-capacity PROXY. It retains both
baseline and in-place variants and exact π SHA-256 consumer.
An installed-before-initialization GMP memory allocator callback
measures actual **GMP-managed live bytes** with alloc/realloc/free
size accounting and peak. This does not include the non-GMP C++
heap, OpenSSL scratch, allocator internal fragmentation or kernel
page residency. Thus an independent Linux process image VmHWM
is measured too. Beware ru_maxrss may inherit the Python parent's
prior high-water on fork/exec; the raw ru_maxrss column is retained,
but process \`/proc/self/status\` VmHWM is used in comparisons.

The arithmetic work at d=1M is exactly:
n=71,430 leaves, 71,429 internal merges, 285,716 ordered
P/Q/T scalar-integer product sites, and 71,429 additive sites
per full binary tree. The child-operand bit-width model reports
\`74,635,285,787,351\` schoolbook bit-pairs, largest operand
3,746,858 bits, result 7,279,373 bits and max recursion depth 17.
This is **NOT** an observed CPU instruction count or a GMP
multiplication-complexity theorem. The original ordinary
\`O(M_int(d log d) log d)\` model remains authoritative.

At d=1M, in the isolated instrumented local source:
baseline expression-temporary explicit carrier-capacity peak
4,618,336 bytes, in-place carrier-capacity peak 2,309,552 bytes.
However the actual GMP-heap peak is the **same** in both modes:
23,074,600 bytes. The terminal endpoint/quotient phase dominates
and makes this a negative overall memory result for carrier reuse.

**New tested optimization:** \`scripts/check_pi_p0_endpoint_lifetime.cpp\`,
a derivative of the instrumented original, computes both
series endpoint numerators/denominators while P/Q/T is still
available, then uses \`std::move(s.t)\` and
\`std::move(s.q)\` to transfer the original numerator and
denominator into the terminal consumer and destructs
\`s.p\` via a scoped GMP swap BEFORE large products, division and
serialization allocate. No leaf permutations, truncations, GCD
changes or heuristic certification. Exact same accepted π
decimal SHA-256 at 100k, 500k, 1M; all have one successful
certificate attempt, with original Chudnovsky analytic premise.

Local separately constructed C++ sources
\`/mnt/data/pi_fibre_alloc_local.cpp\` (retained)
and \`/mnt/data/pi_fibre_endpoint_move_local.cpp\` (released)
were compiled using g++ -O3 -std=c++17, linked GMP/OpenSSL;
they implement the exact same source-level algorithm but were
not byte-identical compilations of the committed new C++ files.
The original committed files were read back from GitHub; the
new exact-source runner is SOURCE-COMMITTED and not yet executed
from a checked-out clone of this PR.

Independent initial single-run receipts:
| digits | mode | heap live peak bytes | process RSS KiB | time ms |
|---:|---|---:|---:|---:|
| 100000 | retain | 1,970,336 | 5,556 | 42.170 |
| 100000 | release | 1,766,088 | 5,420 | 42.041 |
| 500000 | retain | 11,385,168 | 15,888 | 282.456 |
| 500000 | release | 10,270,752 | 14,816 | 288.416 |
| 1000000 | retain | 23,074,600 | 27,800 | 672.598 |
| 1000000 | release | 20,765,464 | 25,948 | 694.804 |

Fresh 5-run alternating mode medians, each separate native process;
Linux VmHWM (not inherited ru_maxrss):
| digits | mode | runtime median ms | runtime range ms | GMP heap peak bytes | VmHWM median KiB |
|---:|---|---:|---:|---:|---:|
| 100000 | retain | 42.365 | 40.98–42.74 | 1,970,336 | 5,620 |
| 100000 | release | 42.651 | 41.69–43.69 | 1,766,088 | 5,420 |
| 1000000 | retain | 689.851 | 667.93–723.76 | 23,074,600 | 27,800 |
| 1000000 | release | 697.337 | 673.96–741.33 | 20,765,464 | 25,952 |

For 1M, exact GMP-heap reduction is 2,309,136 bytes (10.007%),
median process VmHWM reduction 1,848 KiB (6.65%).
The runtime distributions overlap; a ~1.1% median time penalty
in these particular runs is **not** established as a robust change.
Memory gain is reproducible within this local test.
All four precision/mode outputs agree with pinned historical
SHA-256 digests, including 1M
\`130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18\`.
SHA parity is a regression; the underlying exact integer interval
admission is the semantic consumer.

New exact-source reproduction runner:
\`scripts/check_pi_p0_cost_fibre_pareto.py\` uses Git blob
hash checks and local C++17 compilation of the committed
instrumented retained and released sources; for each precision
it runs three program variants (baseline expression temporaries,
in-place carrier reuse, in-place plus released endpoint P/Q/T)
in deterministic rotated order in independent processes, checks
exact digit hashes and structural P/Q/T counts, and constructs a
three-coordinate empirical Pareto frontier (time, real GMP peak,
Linux process VmHWM). It reports no statistical significance
without enough evidence and does not infer a formalized
source-to-consumer equivalence or an external record.
Run from branch checkout:

\`\`\`bash
python3 scripts/check_pi_p0_cost_fibre_pareto.py \
  --digits 10000 100000 500000 1000000 --reps 5 \
  --out build/pi-p0-cost-fibre-pareto.json
\`\`\`

**P0 next big bite**: extend the measured live-heap stage lifetime
ledger to reduce the large terminal numerator/denominator
products; consider operand factor sharing, multiplication-buffer
reuse, and early scope release. Re-estimate exact height and time
cost with \`M_int\` and \`D_int\`, with measured bit-width traces
as inputs; keep the lowest-memory variant available for a fixed
RSS envelope, but promote a latency default only after matched
runs and verified semantic equivalence. The classical analytic
Chudnovsky identity, Bishop same-original-real certificate,
formal Agda execution-fibre instantiation and external world-SOTA
comparison remain OPEN.


### COMP5g.1 — fresh 5M/10M extension of actual allocator measurements

The same independently compiled local retained and early-released
in-place GMP versions were executed once per 5M and 10M setting.
Both keep original ordered P/Q/T, source Chudnovsky tail, integer sqrt
and exact one-quotient strict upper-bound certificate. Their
decimal-output SHA256 values match each other and prior precision
receipts.

| digits | retained wall ms | released wall ms | retained GMP peak bytes | released GMP peak bytes | retained/released process VmHWM KiB |
|---:|---:|---:|---:|---:|---|
| 5000000 | 5146.06 | 4944.39 | 119,912,000 | 107,433,544 | 131,404 / 119,216 |
| 10000000 | 11382.5 | 11374.5 | 243,421,624 | 217,661,176 | 265,632 / 238,056 |

Thus the **measured GMP peak** falls ~10.4% at 5M and
~10.6% at 10M (at 10M delta 25,760,448 bytes);
Linux-process VmHWM falls ~9.3% at 5M and ~10.4% at 10M.
At 10M the two single-run wall times differ by ~8ms;
this is NOT robust proof of a runtime improvement. The earlier
five-run 1M wall-time distributions overlap significantly.
These source-equivalent local execution results are distinct from
unexecuted committed exact-source code.

5M SHA: \`09eb526274ac828a3a54614e72fac5baa8ab6b26b8484fe1b065f678b2c8dbad\`.
10M SHA: \`ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999\`.

The committed exact-source Pareto script now also accepts
\`--digits 5000000 10000000\` with pinned SHA checks. For its
three-way baseline vs in-place vs released comparison, monitor
total cost separately and preserve per-process isolation.
The strongest supported architectural conclusion is that
**early terminal-carrier lifetime termination pays actual GMP
heap and peak RSS**; simply making P/Q/T merges in-place did not.
This validates the existing streaming-residency fibre distinction
and provides a real memory-side Pareto candidate, not a
formal Agda kernel proof or external SOTA record.


## COMP5h — certified lower/upper endpoint lifetime separation (23 November 2026)

**P0 purpose:** apply the pre-existing execution-path sum/peak consumer and
streaming-residency formalism to the actual highest-memory segment of GMP
Chudnovsky π certification. Prior COMP5g released the tree P/Q/T after
constructing both series endpoints. COMP5h now also releases the
*lower decimal quotient* numerator/denominator and their no-longer-used
series endpoint **before** allocating the upper comparison witness.
No reordering of the original leaf product, altered rounding,
GCD substitution, truncation, or relaxed certificate.

Mathematical consumer: compute lower decimal bound
\`x = floor(numLow/denLow)\`, then the exact certificate condition
\`numHigh < (x+1)*denHigh\`, with finite positive denominators and
\`0 <= L <= U\`. After x is computed, the actual integer
\`numLow\`, \`denLow\`, and the lower-series endpoint
\`num2\`, \`den2\` are dead: none appears in the remaining
comparison. The retained objects are x, upper-series endpoint
num1/den1, sqrt bound and scaling. Terminal P/Q/T had already
transferred its T/Q ownership and released P in COMP5g.
This is a source-exact consumer-liveness consequence, not a new
Chudnovsky theorem or full algebraic identity proof.

New \`scripts/check_pi_p0_endpoint_scoped.cpp\` derives directly
from the instrumented COMP5g C++ source. It uses a C++ lexical
scope to destroy the exact lower \`numerator\` and \`denominator\`
before forming \`top\`, and scoped GMP swaps to destroy \`num2\`
and \`den2\`. \`scripts/check_pi_p0_cost_fibre_pareto.py\` now
pins this exact Git blob alongside three prior modes and
compiles them separately, with a four-variant empirical
(time, GMP-managed live peak, Linux VmHWM) Pareto ledger.
There is **no promotion to production default** until the
exact committed source is compiled/run on a local branch checkout.

Local source-equivalent C++ files in \`/mnt/data\`:
\`pi_fibre_endpoint_move_local.cpp\` and
\`pi_fibre_endpoint_scoped_local.cpp\`, compiled with
\`g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto\`.
The *committed GitHub C++ was read back and matches its
intended source transformation*, but the local benchmark was
on the independent source-equivalent versions, not the
byte-identical Git blob. Both use GMP allocator callbacks
installed before constructing GMP constants. They measure
actual GMP live allocation, not just P/Q/T capacity projections.
Linux \`/proc/self/status\` VmHWM independently measures RSS.

| decimal places | old release GMP peak bytes | scoped GMP peak bytes | old release VmHWM KiB | scoped VmHWM KiB |
|---:|---:|---:|---:|---:|
| 100,000 | 1,766,088 | 1,411,776 | 5,420 | 5,176 |
| 1,000,000 | 20,765,464 | 17,111,176 | 25,952 | 21,528 |
| 5,000,000 | 107,433,544 | 89,695,208 | 119,104 | 97,796 |
| 10,000,000 | 217,661,176 | 181,920,552 | 238,100 | 195,172 |

Measured one-million-digit GMP peak reduction *relative to
COMP5g* is 3,654,288 bytes (~17.6%). Relative to the earlier
retained-PQT baseline's 23,074,600 bytes it is ~25.8%.
At 10M COMP5h reduces the COMP5g GMP peak by 35,740,624
bytes (~16.4%), and is ~25.3% under the original retained
terminal P/Q/T peak of 243,421,624 bytes. MiB and KiB
denominators should not be silently interchanged with MB.

Rotated-order separate-process full certificates:
| digits | samples/mode | COMP5g median ms | COMP5h median ms | interpretation |
|---:|---:|---:|---:|---|
| 100,000 | 5 | 41.779 | 41.173 | overlapping distributions |
| 1,000,000 | 5 | 682.202 | 686.934 | overlapping distributions |
| 5,000,000 | 2 | 4940.345 | 4875.550 | insufficient repetitions |
| 10,000,000 | 1 | 11292.5 | 11128.1 | single observation |

At 10M both variants reproduce the pinned SHA256
\`ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999\`.
At 5M both match
\`09eb526274ac828a3a54614e72fac5baa8ab6b26b8484fe1b065f678b2c8dbad\`.
1M and 100k match the previously pinned original hashes.
These checks support executable *output parity*, not an
independent mathematical proof of the Chudnovsky analytic
identity, Agda formalization, or external SOTA.

**Cost-fibre conclusion:** memory lives in a sequence of
operations, not a collection of representations in isolation.
The upper witness does not consume the lower-side products,
so the two sides can occupy disjoint allocation lifetimes
while retaining the same exact admission test. The lower
intermediate is a *reopenable but unnecessary observation*
for the surviving consumer; the quotient x is sufficient.
Peak measured GMP allocation falls even though the
underlying P/Q/T multiplication count is unchanged.
No robust wall-time improvement has been certified, so
this is a **memory-side Pareto candidate** under matched
latency controls, not a new fastest-world π record.

Next exact-source acceptance on PR #1546:
\`\`\`bash
python3 scripts/check_pi_p0_cost_fibre_pareto.py \
  --digits 100000 1000000 5000000 10000000 --reps 5 \
  --out build/pi-p0-cost-fibre-pareto.json
\`\`\`
Requires a writable \`build/\` directory or use an absolute
output path; the script hashes and compiles all four committed
C++ sources before running. The workload at 10M with
four modes * five repetitions is substantial. The
formal Agda cost-weld and independent mathematical
Bishop same-original-real bridge remain OPEN.


## COMP5i/COMP5j — exact dyadic quotient relocation and decimal-power cancellation (23 November 2026)

### Exact consumer algebra — not a floating approximation

The COMP5h certificate contains the exact low-side quotient

```text
x = floor( N_L / (D_L * 2^k) )
```

with positive `D_L`, nonnegative `N_L`, and positive sqrt scaling `2^k`.
Its upper test is the strict integer inequality
`N_U < (x+1) * D_U * 2^k`.
The following identities are exact for all integers `N>=0`, `D>0`,
`k>=0`, `x>=0`:

```text
floor(N / (D*2^k)) = floor(floor(N/2^k) / D)
N < (x+1)*D*2^k  iff floor(N/2^k) < (x+1)*D
```

**COMP5i** implements both shifts using GMP's `mpz_fdiv_q_2exp`
and drops the huge explicit dyadic denominators. It also scopes the
`10005 * 2^(2k)` square-root radicand so it does not overlap the
terminal quotient products. It retains original ordered P/Q/T merges,
exact sqrt lower/upper bounds and the strict upper certificate.
No change to the Chudnovsky mathematical premise or its series bound.

**COMP5j** retains that exact certificate, but additionally cancels
the known factor `2^d` from `10^d=2^d*5^d` before building terminal
numerators: construct `5^d`, and shift by `k-d` (with explicit guard
`k>=d`) rather than construct `10^d` and shift by `k`.
The full output still represents the original `10^d` decimal
scaling; this is exact common-factor cancellation, not a reduction
in requested decimal precision.

### Execution evidence — independent local source-equivalent builds

Local sources `/mnt/data/pi_comp5i_shift.cpp` and
`/mnt/data/pi_comp5j_factor5.cpp` were compiled natively with
`g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto`. The new committed sources
`scripts/check_pi_p0_dyadic_quotient_shift.cpp` and
`scripts/check_pi_p0_power5_dyadic_certificate.cpp`
are transformations of the pinned GitHub COMP5h code, read back
successfully, **but have not been compiled from their exact GitHub
bytes**. That is an open source-replay gate.

The local native GMP source-equivalent versions emitted the
already pinned historical exact π SHA256s for 10k, 100k, 500k,
1M, 5M, and 10M decimal places; the 1M hash was
`130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18`,
and the 10M hash was
`ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999`.
Each reported one successful exact upper-bound certificate.

In addition, a locally executed standalone finite integer regression
tested 13,878 (n,dyadic-shift,denominator) cases with 4 strict upper
thresholds each, and 216 independent decimal-power cancellation
triples with 3 upper thresholds each: both tests PASS.
`tests/test_pi_p0_dyadic_quotient_certificate.py` stores the
regression. The finite test is supporting validation, not a replacement
for the all-integer proof of the identities above.

Peak measured GMP-managed allocated bytes, single isolated process
for 5M and 10M; these figures do NOT account for non-GMP heap or
reproduce a formal kernel cost theorem:

| digits | COMP5h scoped | COMP5i dyadic shift | COMP5j 5-power factor |
|---:|---:|---:|---:|
| 100,000 | 1,411,776 | 1,121,976 | 1,096,976 |
| 1,000,000 | 17,111,176 | 14,124,952 | 13,874,952 |
| 5,000,000 | 89,695,208 | 74,453,568 | 73,203,568 |
| 10,000,000 | 181,920,552 | 151,169,512 | 148,669,512 |

At 10M the final COMP5j source-equivalent implementation reduces
GMP peak by **18.28% relative to COMP5h** and **38.92% relative to
the earlier P/Q/T-retaining baseline peak** of 243,421,624 bytes.
One process VmHWM observation at 10M for COMP5j is 166,072 KiB,
versus 195,172 KiB for COMP5h; do not infer exact 1-to-1
GMP/RSS accounting.

Time comparison: five alternating independent-process 1M-digit runs
for COMP5h and COMP5i gave medians **698.071 ms vs 624.521 ms**
with observed ranges **669.36–706.18 ms** and
**595.96–647.41 ms**, respectively; no range overlap in that
sample, but not cross-device SOTA or general statistical proof.
Five COMP5i-vs-COMP5j 1M runs gave medians **617.43 ms vs 617.80 ms**,
overlapping; the 5-power improvement is principally memory-side.
One 10M run gave COMP5i 10.535s and COMP5j 10.361s;
these do not establish a robust runtime improvement. The
candidate outputs and allocator measurements are attributable
to independent local builds with callbacks installed before GMP
allocation; separate-phase costs and hot/cold matched machine
comparators remain P0 work.

### Current owner and admission boundary

Original performance/correctness owners are
`FibreProgramComplexityExact.agda` (path-indexed sum/peak),
`EfficientRecoverableQuotientExact.agda` (quotient/receipt/reopen),
`StreamingResidencyComplexityErrorDNABidiExact.agda`
(same-consumer streaming), and Paper 9 section 10 bit-cost model.
The exact finite quotient identities show why
intermediate high-width denominators are **not consumer-sufficiently
necessary** once the shift can be moved into a numerator quotient.
Runtime and memory results are measured execution-fibre *receipts*,
not kernel-checked cost theorems.

The PR's `scripts/check_pi_p0_cost_fibre_pareto.py` now includes
the original baseline, in-place, COMP5g, COMP5h, COMP5i and COMP5j
variants as separately compiled and Git-blob-pinned candidates.
Before promoting a production default: execute the exact checked-out
GitHub source, verify all pinned hashes, measure independent processes
with controlled cold/hot order and process VmHWM/GMP allocation,
and add end-to-end certificate verification (not hash equality alone).
Classical Chudnovsky analytic identity/tail, formal Bishop same-real
bridge, Agda kernel and external world SOTA comparison remain OPEN.

Recommended bounded exact-source command, run on PR checkout:

```bash
python3 -m unittest tests/test_pi_p0_dyadic_quotient_certificate.py
python3 scripts/check_pi_p0_cost_fibre_pareto.py \
  --digits 100000 1000000 --reps 5 \
  --out /tmp/pi-p0-fibre-sixway.json
```


## 23 November — independent-oracle lane in lieu of original workstation replay

The local container cannot resolve github.com for a full Git checkout.
The connected GitHub source API was used to read, update and verify
the exact original PR #1546 files; this is not a claim that the full
committed C++ source was compiled in the local container.
Native GMP/OpenSSL and g++ **are** available, and existing
locally constructed equivalent COMP5i/j binaries remain available.
Re-executing those locally compiled COMP5j code paths against
independently computed `mpmath.pi` decimal values gave SHA-256
equality at **100, 1000 and 10000 decimal places** (independent
algorithm and decimal production, with 40 guard digits). This
cross-engine result is strictly stronger than comparing the same
GMP implementation against its own old hash, but still is **not**
a theorem proving the classical Chudnovsky series or the
Bishop original-real formalization.

New reproducible independent checker
`scripts/check_pi_p0_independent_decimal_oracle.py`
pins the actual committed COMP5j Git blob
`be8e746a5c73ed2ec212664b68e5eceacc4420e7`,
compiles it natively, and compares SHA-256 of its certified
decimal string against high-precision `mpmath.pi`
for 100, 1000, 10000 digits. This particular committed checker
is GitHub read-back verified but **not run** against exact GitHub
bytes in this environment; the independent local experiment
above compiled source-equivalent C++.

**Receipt correction discovered and committed:** the scoped,
dyadic-shift and power-five source variants moved/released P/Q/T
early but their legacy `Receipt.bits` field read the **moved-from**
`s.p,s.q,s.t` instead of the original terminal product.
This did not change any numerical certificate or hash, but
corrupted a performance/bit-cost observation. All four
optimized C++ variants now snapshot the original triple
bit-width before ownership transfer and report that exact
snapshot; their Git blob SHA pins in the six-way Pareto runner
were updated as a single ordered follow-up. Do not promote old
`Receipt.bits` values from these variants as physical bit
width measurements.

Available bounded local acceptance when Git checkout is
possible:

```bash
python3 scripts/check_pi_p0_independent_decimal_oracle.py \
 --digits 100 1000 10000 --out /tmp/pi-p0-oracle.json
python3 tests/test_pi_p0_dyadic_quotient_certificate.py
python3 scripts/check_pi_p0_cost_fibre_pareto.py \
 --digits 100000 1000000 --reps 5 \
 --out /tmp/pi-p0-sixway.json
```

The local 100–10000 oracle is an immediate, executed
in-lieu cross-engine acceptance; the full exact-source
compilation/large matched Pareto/independent SOTA and
Agda proof remain OPEN.


## 24 November — COMP5k/l projective geometry (execution DEFERRED)

User explicitly deferred testing/benchmarking and requested fresh
geometry optimization using newest PRs. Audited newest #1550
(input-indexed consumer sufficiency), #1549 (shared sparse
geometric representation), #1548 (semantic coverage/cost
separation) and original #1529. Only source-legal
consumer/quotient and shared-computation ideas apply to Pi.

Two **UNTESTED candidate source files** now exist, both derived
from the latest pinned COMP5j GMP implementation:
- \`scripts/check_pi_p0_signed_tail_cone.cpp\` (COMP5k):
  the original 2x2 upper-triangular P/Q/T matrix product has
  next-term signed delta \(\delta=P_n p_n(A+Bn)\), whose
  sign is \((-1)^n\). Select the adjacent rational endpoint
  order by parity/source signs; eliminate *both* giant
  numerator/denominator cross-products and avoid an extra
  leaf by sorting either parity via constant-time swaps.
- \`scripts/check_pi_p0_residual_witness.cpp\` (COMP5l):
  choose even n so \(\delta>0\) and use TWO exact
  quotient/remainder fibres for the lower integer quotient
  to rewrite the strict upper-bound certificate as
  \(x\delta+\rho+\lfloor(\ell+FC)/2^k\rfloor<Tq\).
  This avoids the upper numerator's large \((R+1)\)
  radical multiplication, while introducing retained
  remainders with not-yet-measured cost and residency.

The full derivation, exact positivity, signs, matrix-source
identity, conservative performance hypotheses and future
acceptance cuts live in
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.
No new execution results, compilation, SymPy checks, Agda
kernel checks, source-independent π theorem or external
SOTA claim were made. Retain COMP5j as the measured historical
baseline, and do not inject these untested candidates into
the six-way default Pareto runner until the testing
deferral is lifted.
