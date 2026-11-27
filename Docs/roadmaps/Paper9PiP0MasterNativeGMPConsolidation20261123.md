
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


## 24 November 2026 — COMP5m/n source-geometric continuation (NO EXECUTION)

User retains instruction to **defer testing**. After inspecting fresh
PR state (π #1546 still open, 46 ahead/11 behind \`master\` on inspection,
mergeability reported false), and newer #1550, #1549, #1548 and source
#1529, two independent **UNTESTED** GMP research candidate sources
were committed; the existing COMP5j default and six-mode
benchmarker remain unchanged.

1. **COMP5m — output-aligned radical:**
   \`scripts/check_pi_p0_output_aligned_root.cpp\`.
   Instead of dyadically scaling \(\sqrt{10005}\), then multiplying
   by \(5^d\), construct exactly
   \(H=\lfloor 2^g426880\,10^d\sqrt{10005}\rfloor\) by GMP
   integer square-root of
   \(10005(426880\,10^d)^2 2^{2g}\).
   The original signed-tail cone orders both adjacent positive
   series endpoints at *either* cutoff parity. The lower quotient
   is \(\lfloor HD_{\mathrm{hi}}/(2^gN_{\mathrm{hi}})\rfloor\);
   the upper witness is
   \((H+1)D_{\mathrm{lo}}<(x+1)2^gN_{\mathrm{lo}}\).
   The root/split guard indexes are widened when the strict
   witness is inconclusive, with explicit unsigned overflow guards.
   **This is an alternative outward rational enclosure of the
   SAME infinite-series π target, not identical finite COMP5j
   endpoints.** Radical squaring and repeated \`10^d\` generation
   can negate the saved post-root multiplication. No speed or
   peak-memory benefit claimed.

2. **COMP5n — operand-width-informed execution order:**
   \`scripts/check_pi_p0_width_scheduled_pqt.cpp\`.
   The EXACT original interval Q width satisfies
   \(\log_2 Q[a,b)
      =3(b-u)\log_2 640320
      +3\log_2((b-1)!/(u-1)!)\)
   for \(u=\max(a,1)<b\). A cheap floating lgamma estimate
   chooses which child tree to *execute first*; the consumer
   still composes \((P_L,Q_L,T_L)\) and
   \((P_R,Q_R,T_R)\) in strictly original left-right
   upper-triangular matrix order.
   The scheduling heuristic is NOT a proved
   Sethi–Ullman or GMP peak-memory optimum, and its lgamma
   overhead may dominate. No performance gain claimed.

The complete same-source mathematical derivation, cost-path
boundaries and original-source producer–consumer obligations
live in
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`,
now extended through G4/G5. No C++ compile/run, no Python/SymPy,
no CI, no kernel Agda/Lean and no SOTA check performed in this
continuation. GitHub source readback only.
The classical Chudnovsky analytic source and Bishop
same-real theorem remain open formal obligations. Preserve
the already measured COMP5j certificate/benchmark receipts
without confusing the new untested candidates with them.


### COMP5o — exact independent signed-square verifier (research implementation, UNTESTED)

Added \`scripts/pi_p0_signed_square_verifier.hpp\`, a *separately
compilable consumer* for a candidate integer x and
**source-authenticated** original P/Q/T triple. Let
\(F=426880\,10^d\), \(S_{\rm lo}=N_{\rm lo}/D_{\rm lo}\),
\(S_{\rm hi}=N_{\rm hi}/D_{\rm hi}\).
Conditional on the same original infinite Chudnovsky
π identity and alternating-tail bound, the following
two EXACT INTEGER slacks suffice for the accepted floor:

\[
10005(FD_{\rm hi})^2-(xN_{\rm hi})^2\ge0,\qquad
((x+1)N_{\rm lo})^2-10005(FD_{\rm lo})^2>0.
\]

This does not use \`mpz_sqrt\` in the verifier and
retains original signed parity. A malicious arbitrary
triple could still pass signs, so exact P/Q/T producer
replay or original source receipt verification is REQUIRED.
The independent verifier may cost more large products
and RAM than COMP5j/m: no measured or claimed speedup.
Full proof boundaries are in
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.
Testing deferred; no compilation, benchmark or kernel
acceptance for COMP5o.


## 24 November — PNP/Langlands source valuation donors and COMP5p/q/r (TESTING DEFERRED)

Audited live P-vs-NP [#1548](https://github.com/chboishabba/dashi_agda/pull/1548)
(G60–G64 signed source support/valuation pruning and
charged alternate representations) and Langlands/GCT
[#1549](https://github.com/chboishabba/dashi_agda/pull/1549)
(R85–R96 source labels, signed zero, creation versus
inherited precision and relative reconstruction). The
proper π application is **source-exact projective
common-factor elimination**, not an imported SAT or
Langlands theorem. New mathematical authority is
the ORIGINAL Chudnovsky leaf factors and original
ordered triangular P/Q/T multiplication.

For j>=1, \`p_j=-24*f_j\`,
\`q_j=640320^3*j^3\`, \`t_j=(A+B*j)*p_j\`,
with \`f_j=(2*j-1)*(6*j-5)*(6*j-1)\`.
Since \`640320=24*26680\`,
each nonzero leaf has a guaranteed common 24.
**COMP5p**
\`scripts/check_pi_p0_projective24_leaf.cpp\`
constructs the 24-normalized leaf *before*
binary splitting, rather than materializing
the extra factor or computing a generic gcd.
For the original \`[0,n)\` tree
\`(P',Q',T')=(P,Q,T)/24^(n-1)\`
with exact sign, series ratios, future
right-multiplication and π-floor consumer.
The source gauge and n-1 scale exponent
are recorded; reopening the literal
raw source triple requires restoring
that factor. It is NOT necessary for a
homogeneous quotient/inequality consumer.

**COMP5q**
\`scripts/check_pi_p0_projective24_residual_witness.cpp\`
combines the same projective-24 leaf
normalization with COMP5l's exact signed
two-remainder upper certificate.
**COMP5r**
\`scripts/check_pi_p0_indexed_prime_content.cpp\`
extracts additional exact local
\`h_j=gcd(f_j,(640320^3/24)*j^3)\`
from **only** primes \`{3,5,23,29}\`
using valuations of original small
linear factors and j. Why no other
prime can divide the gcd:
\`gcd(j,2j-1)=gcd(j,6j-1)=1\`,
\`gcd(j,6j-5)=gcd(j,5)\`;
the constant 640320 has prime support
\`{2,3,5,23,29}\` and \`f_j\` is odd.
The resulting true leaf scale is
\`24*h_j\`, with source reopening
recipe \`prod_(1<=j<n) 24*h_j\`.
No generic GMP gcd; two exact
post-construction divisions by small
source-justified h_j remain.

Neither design changes the signed
zero mode, coefficient precision,
series tail, root enclosure or
original source attribution.
No performance claim: valuation
preprocessing, exact divisions, receipt
storage and optional source reopening
are real costs, not free compression.
The existing measured COMP5j baseline
and selected six-way cost runner stay
unchanged. **All tests, compilation,
benchmarks, kernel execution and
external SOTA comparisons remain
explicitly deferred.** Full proof,
newly indexed P/Q/T source contracts,
cost ledger and references:
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.


## 24 November — COMP5s: exact projective source and output-precision-indexed peak scheduling (UNTESTED)

The candidate also emits counts of source prime-content
calls, local modular checks, valuation divisions and exact
GMP leaf reductions. These are not free normalization
operations, and their measured time/bit cost remains OPEN.
The reported C++ planning-object payload omits allocator
overhead, unlike the separately measured GMP heap peak.

**P0 endpoint:** pursue fastest *independently certified* pi with
correct source and cost. At user's explicit direction, testing,
native compilation, benchmarks, Agda/Lean, CI and external SOTA
comparison stay **deferred**. COMP5j measured historical results
are unchanged and NOT reassigned to this candidate.

New connected implementation:
- `scripts/pi_p0_projective_precision_schedule.hpp` —
  bounded-depth source-width planner with recorded
  output demand (decimal digits, root working bits),
  modelled branch peak, modelled P/Q/T widths and
  separately listed C++ plan object payload (not measured total C++ heap). It chooses only
  evaluation order of the two child computations;
  original matrix merge remains ordered.
- `scripts/check_pi_p0_precision_projective_schedule.cpp` —
  exact COMP5r normalized leaves, guaranteed factor
  24 and indexed prime content \(h_j\) computed
  from original small factors; positive scalar
  \(\prod 24h_j\) retained as a deterministic
  interval/source recipe. A callable
  `reopenOriginalRawSource` reconstructs literal
  original P/Q/T if requested, charging the
  recomputed big-integer scale. Fast pi consumer
  DOES NOT call this expensive reopening.

**Source identity, no precision truncation:** the
original \(2\times2\) upper-triangular Chudnovsky
\((P,Q,T)\) matrix is unchanged up to the exact
positive scalar \(G(a,b)\). The original leaf
order, signed parity, zero mode, next-term
residual and exact one-floor dyadic certificate
are retained. Only independent subtree
*execution* order is allowed to vary.
The working precision controls which large
subtrees merit forecast planning, NOT whether
source P/Q/T limbs may be dropped.

The planner forecasts integer carrier sizes
from exact original leaf-factor **inequalities**
on \(|p'_j|\), \(q'_j\) and \(|T/Q|\),
numerically approximated by `lgamma` and
`log2` ONLY for scheduling. It chooses
between \(p_{L\to R}=\max(p_L,s_L+p_R,m)\)
and \(p_{R\to L}=\max(p_R,s_R+p_L,m)\)
at top levels. Unplanned subtree cost and
GMP merge scratch remain estimated, **not**
a mathematically certified or empirically
calibrated optimal memory schedule.
Actual source values are never
truncated by this estimator.

Separate `FIBRE` coordinates include
source scale recipe; selected sign and
original cutoff; scheduling precision,
plan nodes, right-first decisions,
predicted peak and C++ plan allocation;
original GMP allocated peak and final
decimal certificate. Do not identify
model peak with actual physical RSS or
with a kernel execution-cost theorem.

Complete math, producer/consumer source
coordinates, positivity and original-source
proof obligations plus S1–S6 roadmap:
`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md`.
Any future actual P/Q/T truncation requires
an independent error/strict-boundary
admission proof; no such work is claimed.
Original analytic Chudnovsky identity,
Bishop same-original-real and independent
world SOTA comparison remain OPEN.


## 24 November — COMP5t: exact affine-edge and suffix-only retries (NO TESTS)

The COMP5s precision-indexed projective normalized GMP producer
has a new, separately selectable **UNTESTED** COMP5t continuation:
\`scripts/pi_p0_affine_edge_retry.hpp\` and
\`scripts/check_pi_p0_affine_retry_schedule.cpp\`.
User-directed testing deferral remains active; no local
compiler, C++ benchmark, SymPy/Python test, CI,
Agda/Lean kernel or external SOTA comparison was run.

At original terminal \(n\ge2\), the future series observer
already consumes \(V=T'_nq_n+P'_np_n(A+Bn)\).
Thus the source-indexed affine edge
\(E_n=(T'_n,Q'_n,V)\) retains exactly enough to
recover the **normalized** original P/Q/T via
\(P'_n=(V-T'_nq_n)/(p_n(A+Bn))\), with exact
signed nonzero divisor. The projective leaf source scale
\(G_{0,n}=\prod_{j=1}^{n-1}24h_j\) remains a
separately indexed, optionally reopened raw-source receipt.
This is an actual original-source algebraic bijection,
not a lossy decimal-hash quotient; authentication of
the underlying P/Q/T producer remains a separate gate.

When the ordinary strict upper witness fails, choose
the exact next refinement using two integer-square slacks
with positive series endpoints
\(S_\mathrm{lo}=N_\mathrm{lo}/D_\mathrm{lo}\) and
\(S_\mathrm{hi}=N_\mathrm{hi}/D_\mathrm{hi}\),
candidate \(x\), \(F=426880\,10^d\):

\[
D_b=10005(FD_\mathrm{hi})^2-((x+1)N_\mathrm{hi})^2,\quad
D_n=((x+1)N_\mathrm{lo})^2-10005(FD_\mathrm{lo})^2.
\]

- \(D_b\ge0\): root precision insufficient for exact
  fixed-source lower floor; increase only \(b\) and
  KEEP the identical authenticated edge.
- \(D_b<0,D_n>0\): same output floor is certified
  by signed-square upper witness; accept.
- \(D_b<0,D_n\le0\): source interval too wide,
  increase **only** \(n\), reopening P from
  signed edge residual by exact division and
  computing the genuine original-indexed suffix
  \([n,n')\). Recompose original ordered
  \(M'_{0,n}M'_{n,n'}\); KEEP the existing root
  and decimal factor.

The source-indexed suffix planner is implemented as
\`makePlanInterval(begin,end)\`, not by incorrect
rebasing to zero. Structural counters track all
classification squares, guard-only/root rebuilds,
series-only/source suffix builds, signed P reopening
divisions, prefix-built-once admission and all actual
leaf valuations. Those comparisons may consume
substantial additional memory and runtime; no
speedup/memory improvement is claimed. A
three-coordinate edge does NOT assert that any
unseen raw source or independent analytic π
identity has been proved.

Full derivation and exact S7–S12 proof/acceptance
obligations: \`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.
COMP5j is still the original measured candidate;
COMP5t is not added to the historical six-way
GMP Pareto default. Source parity, positive cone,
zero-mode identity, \(n,d,b\) separate indexes,
signed delta, scale recipe and original strict
decimal-floor consumer remain explicit.


## 24 November — COMP5u: dyadic 3-sector retry geometry from PNP G83 (TESTING DEFERRED)

Using the user's G79–G83 P-vs-NP guard-geometry note as
**methodological inspiration**, not as a theorem about π,
COMP5u contracts the failed-certificate decision to three
exact integer residue sectors rather than fully expanding
two expensive square-root-free signed-square slacks on
every failed dyadic upper witness. The G83 lesson is
that explicit representation size is not synonymous
with actual source-preserving consumer work.

New standalone **UNTESTED** source:
`scripts/pi_p0_dyadic_sector_contraction.hpp`.
New integrated original-source/COMP5t-derived **UNTESTED**
implementation:
`scripts/check_pi_p0_dyadic_sector_schedule.cpp`.
No historical COMP5j or COMP5t baseline is overwritten.

For original authenticated positive ordered Chudnovsky endpoints,
\(H=426880\,5^d\), \(k=b-d\), \(R=\lfloor2^b\sqrt{10005}\rfloor\),
the lower quotient and its two remainders are

\[
H R D_h=2^k(xN_h+\rho)+\ell,\quad
0\le\rho<N_h,\quad0\le\ell<2^k.
\]

For \(W=H(R+1)D_l=2^k u+\eta\),
the exact consumer result is:
- **Admit:** \(u<(x+1)N_l\).
- **Extend source suffix:** ordinary admission failed;
  \(u+\lfloor(\eta-HD_l)/2^k\rfloor
     \ge (x+1)N_l\)
  AND \(\rho+\lfloor(\ell+HD_h)/2^k\rfloor<N_h\).
  Lower output floor is resolved, but original series
  upper endpoint cannot yet admit; recompute only
  source suffix \([n,n')\) after signed-P reopening.
- **Refine radical guard:** all remaining authentic
  cases; retain the exact affine edge and
  original cutoff, increase only \(b\).
  This can over-refine relative to COMP5t's full
  square-slack classifier, so it is SAFE but
  not certified minimal-cost.

The algorithm uses quotient/remainders and
one signed floor-shift on \(\eta-HD_l\);
mistaking floor division for signed truncation
would corrupt source obstruction.
The source end, initial tree, original
prime-local projective normalization,
identity/zero mode and signed residual
are unchanged. Structural cost fields
distinguish dyadic quotient/remainders,
integer division, scaled denominator
products, guard/source decisions and
false positives for any modelled memory
estimate. No performance promotion.

**Original-coordinate BIDI:** final \(\pi\)
output is projectively homogeneous,
but intermediate dyadic remainders
are not. With raw scale \(G>0\),
\[
c=\lfloor G\ell'/2^k\rfloor,\quad
\rho=G\rho'+c,\quad
\ell=(G\ell')\bmod2^k.
\]
The new optional `reopenRawDyadicFibre`
constructs these exact raw-source
remainders; raw producer authenticity
is still independently required.
This transfer is not inferred from
P-vs-NP's finite-field separator theorem.

Full equations, decision-proof and
positive/negative S13–S19 obligations:
`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md`.
**All testing/benchmarking/Agda/Lean/CI
and independent world-SOTA comparisons
remain deferred**. No new measured
runtime/memory figure.


## 24 November — COMP5v common-root source contraction (TESTING DEFERRED)



Source review removed an inherited
`viewEndpoints(edge)` call from
the new COMP5v wrapper: it had
materialized \(Q'q_n\) before the
shared classifier even though the
new path needs only \(T',Q',V\)
plus the original indexed \(q_n\).
The code now omits that unwanted
allocation. For \(n<2^{20}\),
\(q_n=(640320n)^3<2^{120}\),
a source-derived upper bit-width
for the small parity factor; this
is an exact conditional width
fact, NOT a demonstrated
performance result.

COMP5v is a separately committed **UNTESTED** extension of
COMP5u's exact signed affine/prime-local projective π
certificate controller. It preserves the original
source and its suffix-only retries; the measured
COMP5j, experimental COMP5t/u, and the six-way
production benchmark are not overwritten.

New files:
`scripts/pi_p0_shared_radical_sector.hpp` and
`scripts/check_pi_p0_shared_radical_schedule.cpp`.

With \(H=426880\,5^d\), \(R=\lfloor
2^b\sqrt{10005}\rfloor\), original
normalized terminal edge
\((T',Q',V)\), next source denominator
\(q=q_n\), define \(Z=HQ'\), \(Y=ZR\).
The original two endpoint products factor exactly:

| Original n | Lower \(A=HRD_h\) | Upper \(W=H(R+1)D_l\) |
|---|---|---|
| even | \(qY\) | \(Y+Z\) |
| odd | \(Y\) | \(q(Y+Z)\) |

Therefore ONE \(Y=HQ'R\) source-common
large radical product feeds both adjacent
original source endpoints. No fake
commutation of the noncommutative P/Q/T
matrix or change of source leaf order.
We also avoid separate materialization
of original adjacent denominator \(Q'q\)
when creating terminal bound numerators.
The source sign/residual determines
which parity branch is used.

The exact nested quotient/remainder and
COMP5u three-sector classifier are
unchanged. On an ordinary successful
strict upper comparison, the large
upper dyadic remainder \(\eta=W\bmod2^k\)
is never built; only a failing comparison
requires \(\eta\) and the signed
\(\lfloor(\eta-HD_l)/2^k\rfloor\)
correction. Structural counters expose
one shared radical product, source
q-products, lower divmod, upper quotient,
lazy upper remainder, dyadic corrections,
source versus root retries and existing
prime-local GMP producer work.

The final floor consumer is invariant
under source projective scaling, BUT
the Euclidean raw-source remainders
still demand G14's exact indexed
dyadic carry. Raw signed source
reconstruction and full analytic
Chudnovsky/Bishop proofs remain
separate consumer obligations.

Potentially lower multiplication
duplication does NOT establish lower
bit complexity, wall-time, GMP heap
or process RSS: the additional
q-products may dominate. The exact
source equations, S20–S25 proof/negative
control gates and all producer-consumer
links are in
`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md`.
**Compilation, tests, CI, Agda/Lean,
profiling and SOTA comparison
are all deferred by user instruction.**
No new quantitative result.


## 24 November — COMP5w: quotient-only common path; lower remainders eliminated (TESTING DEFERRED)

The user-directed next exact geometric cut from COMP5v
is a **separate UNTESTED candidate**. The original
measured COMP5j, source-complete COMP5t, dyadic
COMP5u, and shared-radical COMP5v are unchanged.
No runtime, latency, memory or world-record
performance figure is attributed to COMP5w.

New files:
`scripts/pi_p0_lazy_lower_sector.hpp` and
`scripts/check_pi_p0_lazy_lower_schedule.cpp`.
They keep the literal original Chudnovsky
ordered P/Q/T leaf signs, exact positive
prime-local projective gauge, original
affine-edge producer, source scale recipe,
n/d/b indexing, and source-only suffix
versus radical-only guard continuation.

Let \(H=426880\,5^d\), \(k=b-d\),
\(R=\lfloor2^b\sqrt{10005}\rfloor\)
and signed adjacent rational source
endpoints \(N_l/D_l,N_h/D_h>0\).
Preserve COMP5v's *single*
common product \(Z=H Q'\), \(Y=ZR\).
Then for even n \(A=qY,W=Y+Z\);
for odd n \(A=Y,W=q(Y+Z)\).
The identical conservative π
floor \(x\) is computed using only

\[
x=\left\lfloor
\frac{\lfloor A/2^k\rfloor}{N_h}\right\rfloor.
\]

The source's actual GMP path uses
`mpz_fdiv_q_2exp` and
`mpz_fdiv_q`, not divmod:
neither \(\rho\) nor \(\ell\)
is allocated on the ordinary
path **or** exceptional path.
The upper witness
\(u=\lfloor W/2^k\rfloor
<(x+1)N_l\) remains unchanged.
Only when it fails does the
candidate build \(\eta=W\bmod2^k\)
and the original signed correction
\(\lfloor(\eta-HD_l)/2^k\rfloor\).

The G12 lower-residue/root crossing
sector can be checked WITHOUT
constructing \(\rho,\ell\):
the opposite-series upper-root
numerator \(H(R+1)D_h\) is
\(\boxed{qW}\) for even n or
\(\boxed{W/q}\) for odd n.
The odd division is exact by
original source construction, with
a fail-closed divisibility guard.
One late q multiply or exact
divide and a dyadic shift recover
the identical COMP5u/v three-way
sector decision. If the source
is truly blocked, reconstruct
the signed affine P and append
only the real indexed suffix;
otherwise increase only
root precision b. The source
zero mode and invalid signs
remain rejected states, not
quotient zero.

The precise S26–S32 ledger
and both-parity equivalence proof
are in
`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md`.
Actual GMP peak/bit-cost may rise
or fall: the exceptional q division
and source replay are real costs,
and a quotient-only API is not
guaranteed faster than GMP divmod.
Structural counters track the
two quotients, zero lower
remainders, upper failure-only
remainder, late parity reopening,
and root/source retry costs.
G14 raw-source dyadic carry
is retained as an OPTIONAL
consumer; raw remainders are
not fabricated from a decimal
hash or normalized observation.
The integrated candidate is
not promoted into the original
six-way benchmark runner.

**Per ongoing explicit user
deferral**, no exact-source C++
compilation, benchmark, Python/
SymPy execution, GitHub CI,
Agda/Lean formal kernel or
external SOTA comparison was
performed in this tranche.
Analytic Chudnovsky/Bishop
same-real and exact-source
acceptance remain OPEN.


## COMP5x/y — signed four-corner and streamed parity observer (24 November 2026)

COMP5x compares all three original boundary predicates via virtual dyadic shifts, retaining exact equality and the intermediate upper-source test. COMP5y adds a two-limb parity-product observer: independently stream q0*a and q1*a, delay the second by one limb and add with a separate carry. This avoids the potential 129-bit overflow of a combined two-product accumulator. Scan low to high; the last unequal limb determines the exact sign, with terminal carry flush and explicit zero. On nail-free GMP with <=64-bit limbs and unsigned 128-bit support, q of <=2 limbs uses constant auxiliary storage; otherwise exact materialized GMP fallback. The even lower-floor parity multiplication is still present. All source indices, signed residual, positive projective gauge, G14 carry reopening, root-only and suffix-only continuation remain intact.

G28: split carry streams and prove prefix reconstruction; G29: highest disagreement and terminal support/equality; G30: compile all parity boundary comparisons with exact fallback; G31: source-matched sector equivalence and adversarial carry/zero/limb tests; G32: physical cost Pareto including full low-to-high scans versus optimized GMP multiplication and high-to-low early exit. Donor inspiration from latest PR metadata: X369 future-consumer quotient, Langlands unique extension, P vs NP costed coverage, F8 independent residual channels, Monster source-labelled transport; these are patterns, not imported proofs.

Owners: scripts/pi_p0_stream_boundary_sector.hpp and scripts/check_pi_p0_stream_boundary_schedule.cpp; COMP5x/w/j retained. No compilation, executable tests, formal kernel or benchmarks per inherited deferral. Independent analytic identity/Bishop same-real and external SOTA remain open. Next: virtual affine sum Y+Z and liveness-aware choice of scan vs materialization; do not claim speedup from smaller explicit state.

## COMP5z — fused affine boundary observer (untested)

G33: stream Y+Z with a one-bit affine carry into COMP5y's independent q0 and q1 multiply streams, delayed limb and addition carry. G34: for m=max(limbs(Y),limbs(Z)), at most m+3 output limbs suffice for a two-limb factor; flush all carries and preserve exact sign and zero. G35: compile all three original four-corner predicates, using factor 1 or indexed q and retaining the intermediate upper-source test. G36: preserve original source indices, signed tail, positive gauge, G14 raw-coordinate reopening and suffix-only retries. G37: compare allocation and actual scan cost against COMP5x/y; retaining base and Y can offset savings, and factor-one streaming may lose high-to-low early exits. The even lower-floor product remains. Exact materialized fallback for unsupported GMP configuration/wide factor. Owners: scripts/pi_p0_affine_boundary_sector.hpp and scripts/check_pi_p0_affine_boundary_schedule.cpp. No compilation, execution, kernel or benchmark acceptance; prior candidates retained. Next: cost-aware blockwise carry bounds, exact early termination and quotient consumer liveness, not unconditional streaming promotion.

## COMP6a — bounded bidirectional prefix observer (untested)

G38: put P=M^h, decompose Y=P Y_H+Y_L, Z=P Z_H+Z_L, and 2^k B=P B_H+B_L. The literal signed residual is P delta+q(Y_L+Z_L)-B_L, delta=q(Y_H+Z_H)-B_H. With q>0 and h>0, delta>=1 certifies positive, delta<=-t*q certifies negative, where t is the number of globally nonzero affine operands (1 or 2). Otherwise retain unresolved; h=0 gives exact sign including zero. Proof: lower term >=-(P-1) and <=t*q*(P-1). No claim that delta=0 is original equality.

G39: native virtual high-window extraction by public GMP value limbs and bounded mpz_import, including arbitrary dyadic offsets and nail bits. Prefix widths 4,8,16,32 limbs, aligned to maximum of original operand and shifted-boundary supports; the small q can grow the computed prefix by at most two product limbs plus one affine limb. Read only high windows, no full shifted boundary, lower remainder or product. If no strict sign follows, use the exact COMP5z carry observer (or its exact materialized fallback). Keep all three four-corner tests and source index/scale/signed residual/zero-mode/suffix contracts.

G40: cost ledger counts attempts, decisive prefixes, exact complete prefixes, window slots and fallbacks. This is a bounded heuristic schedule, not calibrated. Prefix work is repeated; cap prevents unbounded doubling cost. Critical negative control: near a decimal floor boundary the relative gap can be O(10^-d), so constant-width high prefixes may fail on nearly every large successful admission. A narrow interval is not evidence of speedup; compare bypass, prefix, streaming and materialized GMP with actual source-matched branch frequencies and heap/time. Do not promote until measured Pareto. 

G41 remains open: original lower-floor parity product and quotient liveness. Investigate lower quotient's exact slack/remainder as an optional shared consumer, despite prior remainder-elimination cuts; retain COMP5w/x/y/z and measured COMP5j for independent comparisons. This is geometry-first and not unconditional streaming.

Owners: scripts/pi_p0_adaptive_boundary_sector.hpp and scripts/check_pi_p0_adaptive_boundary_schedule.cpp. No compilation, numerical execution, formal kernel checks, CI or benchmarks per inherited deferral; original analytic identity/Bishop same-real and external SOTA remain open.

## COMP6b — both-parity signed local slack fibre (UNTESTED)

Reuse original COMP5q even-parity residual witness in scripts/check_pi_p0_projective24_residual_witness.cpp, not a new independent arithmetic theorem. For original indexed edge (n,T',Q',V), q=q_n, signed defect V-qT', set e=abs(V-qT') only after parity sign validation. Let (a,b)=(q,1) even or (1,q) odd, (Nh,Nl)=(V,T') even or (T',V) odd. Then ab=q, b Nh-a Nl=e. With Z=HQ', Y=ZR, the upper-minus-lower enclosure width is (Ye+b Z Nh)/(2^k Nh Nl).

G41/G42/G43/G44: obtain aY=2^k(x Nh+rho)+ell by nested divmods, L=Nh-rho>0, J=b L-(x+1)e, C=ell+aZ. Exact original admission residual multiplied by a is b C-2^k J; intermediate upper-source lower-root residual multiplied by a is b ell-2^k J; opposite lower-source upper-root residual is C-2^k L. Strict negative first admits, strict negative second refines root, nonnegative third refines root, else append original suffix. J<=0 makes the first two strict predicates impossible, but J=0 and ell=0 is an inhabited equality, not invalid source. At k=0 ell=0. The signed defect is preserved by the original edge and its index; no loss of source zero mode or scale receipt.

Native owner scripts/pi_p0_slack_sector.hpp reuses signed defect during validation, overwrites the packed lower numerator with dyadic quotient, pays for two actual remainder outputs, releases it before slack/correction work, and reuses base storage for C. No retained Y or materialized absolute (x+1)Nl or (x+1)Nh threshold. Odd parity may still materialize q*C and q*ell; even lower aY product still exists. Uses existing virtual shifted comparator; signed J domain handled before positive comparator. Counters distinguish skipped nonpositive-J predicates, exact zeros (including inferred), executed comparisons, divmods and parity/tail product sites. Raw L and J are not generally homogeneous: G14 carry t=floor(G ell/2^k) gives L_raw=G L-t, J_raw=G J-b t, C_raw=G C-2^k t. Thus b C_raw-2^k J_raw and C_raw-2^k L_raw scale by G; b ell_raw-2^k J_raw does likewise. Preserve original gauge recipe and explicit carry reopening, never silently identify normalized remainders with raw ones.

G45: compare against COMP5q and COMP5w/x/y/z/6a with actual original-source hashes, strict boundaries, all parity and retry sectors, GMP allocation capacities, scratch, tail multiplication x*e, divmod incremental cost, and suffix-only schedules. No claim of lower latency/peak heap: retaining remainders and multiplying x*e costs real work. Next candidate: bound x*e from original next-term magnitude and use a sufficient slack admission, fall back to exact J only when required; keep equality/unknown distinct. No compilation, tests, formal kernel, CI, benchmarks or external SOTA comparisons per inherited deferral. Analytic identity/Bishop same-real still open.

Integrated owner scripts/check_pi_p0_slack_schedule.cpp; prior candidates unchanged.

## COMP6c — integer tail budget and source-indexed sufficient admission (UNTESTED)

G46: reuse COMP6b's original signed defect e=abs(V-qT'), parity factors a,b and L=Nh-rho, C=ell+aZ. Set E=(x+1)e, K1=bL-floor(bC/2^k), K0=bL-floor(b ell/2^k). K1<=K0. Exact policy: E<K1 admits; otherwise E<K0 refines upper radical; otherwise C>=2^k L refines lower radical; otherwise extend the genuine original suffix. This is the same three-boundary decision, not a different analytic stopping rule. A budget tie E=Ki is NOT necessarily an exact original boundary zero: the corresponding dyadic numerator must also be divisible by 2^k.

Original source bound: |p_j|/q_j < 1728/640320^3=1/53360^3<2^-47 for j>=1. For an authenticated ordered P/Q/T producer, e=Q' q_n (A+Bn) product_(j=1)^n |p_j|/q_j, hence e<Q' q_n (A+Bn) 2^(-47n). This is a source-relative mathematical enclosure; projective gauge cancels from the ratio. It does NOT follow from the signed cone alone. Runtime still obtains exact e from original edge; no claim to have eliminated that producer or evaluated the source envelope as a runtime admission predicate.

G47: for positive u=x+1,v=e, K=K1, first test L2(u)+L2(v)<=L2(K)-1, sufficient for u*v<K. If inconclusive, obtain at most 64 high bits of each operand with shifts su,sv, and use strict upper bound (hu+1)(hv+1)2^(su+sv); compare virtually against K without constructing the shifted bound. K<=0 never admits. A failed bound is UNKNOWN, not a sign/equality; exact u*v is constructed once on fallback, then reused for both K1 and K0. No exact tail multiply on sufficient admission; no changed retry sectors. This fixed 64-bit prefix is a heuristic cost choice, not optimality. The radical budget itself requires a dyadic quotient; odd parity still pays q*C.

BIDI: for w=bC or b ell, let eta=w mod 2^k, K=bL-floor(w/2^k). Under authentic G>0 and carry t=floor(G ell/2^k), Lraw=G L-t and wraw=G w-2^k b t, so Kraw=G K-floor(G eta/2^k), Eraw=G E. Since 0<=floor(G eta/2^k)<G, E<K iff Eraw<Kraw. The same holds for K0. Dyadic ties are representation-dependent; original signed residuals and exact zero remain homogeneous by G45. Original source zero, signed tail, n,d,rootBits and indexed scale recipe remain separate.

G48: measure source-matched incremental divmod, budget-shift and parity costs, bounded-prefix decision rate, fallback cost, live GMP allocation and exact output hashes; compare with COMP6b, COMP5q, COMP5w/x/y/z and COMP6a. The original source bound motivates cutoff planning but does not prove typical budget margin or speedup. Next investigate retaining the signed next-term defect at the producer rather than recomputing V-qT', and replacing absolute edge endpoint storage by reversible signed coordinates with fail-closed provenance and measured liveness. No execution, compilation, formal kernel, CI, benchmarks or SOTA comparison per inherited deferral. Classical analytic identity/Bishop same-real remain open.

Owners: scripts/pi_p0_tail_budget_sector.hpp and scripts/check_pi_p0_tail_budget_schedule.cpp. All earlier candidates retained.

## COMP6d — producer-retained signed defect carrier (UNTESTED)

G49: retain (n,T',Q',delta=P'f_n), f_n=p_n(A+Bn)<0, rather than (n,T',Q',V=q_n T'+delta). Exact BIDI V=q_n T'+delta and P'=delta/f_n, with divisibility checked when reopening. Original positive gauge G scales T',Q',delta uniformly; signed source zero remains excluded for active n>=2, and the empty interval identity remains (P,Q,T)=(1,1,0). The original split producer and scale recipe authenticate provenance separately, not merely the parity cone.

G50: private factory retains the signed defect, overwriting moved P storage. Positive adjacent numerator follows immediately for even n; for odd n verify q_n T'>|delta|. With positive factors T',q_n and e=|delta|, L2(T')+L2(q_n)-2>=L2(e) suffices (strict inequality follows from e<2^L2(e)). Otherwise check exact V>0 once at construction. Private coordinates prevent arbitrary caller injection; shape checked by classifier and reopening. Even lower quotient needs V, materialized once per attempt and released after slack L; odd lower quotient uses T' and does not need V unless producer positivity fallback or explicit reopening is requested. Classifier consumes delta directly; even uses reference, odd currently copies magnitude. Same COMP6c budget and fallback helper, same strict/equality semantics. Avoid old scheduler's repeated V-qT' cone reconstruction and classifier's independent defect reconstruction.

G51: for true indexed suffix (P_s,Q_s,T_s) on [n,m), ordered composition is P_m=P'P_s, Q_m=Q'Q_s, T_m=T'Q_s+P'T_s. Hence delta_m=(delta_n/f_n)P_s f_m. Exact divide first by f_n, not by an arbitrary projective factor. Integrated scheduler reopens P' once (checked exact), moves Q',T', drops old delta, then reuses existing ordered split/join and produces new delta_m. This is suffix-only and preserves the index and scale recipe. Direct defect-native join without intermediate P is not implemented; P is also needed by the T cross-term. Root-only retries retain the same carrier.

G52: actual GMP scratch, odd magnitude copy, producer positivity check/fallback, per-attempt even endpoint reconstruction, exact reopening and prefix/suffix work require matched cost measurements. Compare all preceding candidates and independent certified output, not operation-count-only dominance. Earlier COMP6c retains V across root retries, so repeated even materialization may offset gains. No compile, numerical test, formal kernel, CI or benchmark per inherited deferral. Next: source-specific quotient decomposition of the even endpoint or cached/lazy endpoint policy; compare against simply retaining P' with lazy defect construction. Do not promote until physical Pareto and independent analytic identity/Bishop same-real gates are paid.

Owners: scripts/pi_p0_defect_source.hpp, scripts/pi_p0_defect_sector.hpp, scripts/check_pi_p0_defect_schedule.cpp. Existing COMP5t/6c and historical measured COMP5j remain intact.

## COMP6e — integrated direct quotient, signed correction, and literal corner acceptance (UNTESTED)

Donor pattern: the attached Langlands R208 restricted mixed-geometry work constructs the consumer interface from the original source rather than expanding a raw frontier, and charges precision-probe overhead against savings. This is methodological inspiration only, not an imported arithmetic proof or Langlands correspondence. Keep the original index n, source gauge, signed defect, zero, and independent precision d,b,k. All previous candidates are retained as comparisons, except the explicit portability repair below.

G53: for even n write T=T', e=delta_n>0, q=q_n, V=qT+e, D=2^k, Y=ZR. Directly divide the unscaled Y: Y=D(x0 T+rho)+ell with 0<=rho<T, 0<=ell<D. Let F0=q rho-x0 e, F=F0+floor(q ell/D), eta=q ell mod D. Then qY=D(x0 V+F)+eta; F<V and the literal lower floor is x=x0+floor(F/V). No universal single-integer correction assumption. Odd route reuses COMP6d since its lower floor is already the unscaled x0. Never build full qY on either path.

G54: if x0=0 or a strict bit-length product bound proves x0 e<=q rho, x=x0 without constructing either product. Otherwise compute F0 by q*rho and signed submul x0*e. If F0>=0, x=x0 and no parity dyadic carry needed. Only F0<0 consumes q*ell and its exact dyadic divmod. F>=0 gives x=x0; observed F=0 is a valid neutral state, not invalid or empty. F0=0 alone does not establish F=0. If F<0, h=-floor(F/V)>=1. Put dF=-F; h=ceil(dF/V). If dF<=V, h=1 and corrected slack L=dF, no extra division. A sufficient bit-length bound dF<qT proves this without constructing V. Otherwise materialize V once and compare exactly; only dF>V pays signed divmod and h>=2. General corrected slack L=V-r where F=-hV+r and 0<=r<V. This branch can have arbitrarily many corrections on admissible source-shaped synthetic edges; no universal source-specific bound on their frequency is asserted.

G55: if x=x0, the full upper admission reduces to ell+Z<D(T-rho), otherwise refine upper radical (upper-source lower root lies in floor x0). If F<0, x<x0 and both upper strict predicates necessarily fail. The opposite lower-source upper-radical crossing is eta+qZ>=D L, otherwise append genuine [n,m). Exact ties retain the original non-strict/strict semantics. No approximate stopping rule or extra source/root retry. All original source rebuilding, exact reopening, root-only and suffix-only contracts from COMP6d preserved. 

G56 BIDI: for positive original gauge G let t=floor(G ell/D). The common rho_raw=G rho+t and ell_raw=G ell-Dt. Hence F_raw=GF+c where c=floor(G eta/D), 0<=c<G, and eta_raw=G eta-Dc. If F=-hV+r, then F_raw=-h(GV)+(Gr+c), with 0<=Gr+c<GV; correction h and x invariant. The corrected slack reopens as L_raw=GL-c. The original corrected radical residual eta+qZ-DL scales exactly by G, including zero. Common unscaled slack residual ell+Z-D(T-rho) likewise scales by G. Inhabited F=0 is not itself a projectively homogeneous observable; preserve dyadic carries and original source coordinates.

Implementation: scripts/pi_p0_quotient_sector.hpp and scripts/check_pi_p0_quotient_schedule.cpp. The new even path counts common quotients, sufficient bit proofs, exact signed residual products, dyadic carries, no-correction and single/multi-correction sectors, endpoint products, and corrected radical products. No unbounded prefix-probe heuristic; cost of the remaining signed tail multiplication and possibly a second integer division remains charged. No claim of heap or latency dominance; compare with historical COMP5j and all relevant COMP5q/5w/6b/6c/6d alternatives. Retaining signed source defect and an exact pair of remainder outputs still incurs real memory and arithmetic.

Portability blocker found by inspecting the available standard GMP header: mpz_fdiv_qr_2exp is not a supported GMP API. New scripts/pi_p0_gmp_dyadic_divmod.hpp uses the standard separate floor quotient and remainder calls in alias-safe order, with distinct output guard. Replaced calls in the eight inspected candidate files (dyadic_sector_contraction, shared_radical_sector, slack_sector, tail_budget_sector, defect_sector, quotient_sector headers, residual_witness and projective24_residual_witness C++). This changes operation-site accounting: one logical dyadic divmod means two supported calls, not a single native fused GMP operation. The historically restored baseline files remain untouched. Source-level correction, not compilation acceptance.

Consolidated next acceptance owner: scripts/check_pi_p0_quotient_sector_exact.cpp (authentic raw ordered prefix cases, synthetic signed cone, explicit materialized corner oracle, prior COMP6d equivalence, gauge reopening, negative/multi correction, zero root, k=0 and limb-boundary shifts, alias checks against generic mpz_fdiv_qr). Added but NOT compiled or executed. Separate actual source shapes from synthetic controls. Compare whole original source schedules, independent decimal hashes and matched per-stage time, GMP alloc/scratch and RSS, including probe cost and rare retries; do not select production default from algebraic counts. Remaining P0: independent analytic identity/Bishop same-real, native exact-source acceptance, calibrated cost Pareto, external independently certified speed comparison. No more purely representational candidate extension before evaluating the now-integrated routes unless user explicitly directs further mathematics. No compilation, numerical execution, CI, kernel or benchmarks performed in this tranche per inherited deferral.

## 25 November — indexed quotient transport cube and consolidated acceptance frontier (UNEXECUTED)

Live donors inspected: #1291 at 65950c7fe941a817464ea647cbfc49c58f7db6ab (actual scripts/check_ssp_singer_incidence_wheel_20261125.py blob a68708f3fa817f927fa80f0d2f10ebb60fc7a119); #1552 at 4e9049ab899a9beee76b493698cb647cda116c48, #1549 at e8bd35e56c6f0291f5f0d9a4bf1788b79cc14962, #1547 at 8cf8761e5c1da5346d4604dfa81bd25611a8fccb, #1548 at 87c46ab1c0a4ce7910ddcbf16bcce9aa62d37d8a (metadata audit except named wheel source). JMD retains SSP/prime-encoding motivation, Conway FRACTRAN, Griess/Sah and Singer classical geometry; DASHI wheel attachment is a donor pattern, not an imported pi theorem. No 13-wheel, group equivalence or prime-lane speedup is asserted for Chudnovsky. The important donor is signed transport/history, including nonempty neutral fibres; F8 same-index source capture and Langlands charged discovery costs are methodological donors.

Retain original source prefix (P,Q,T), n, decimal d, radical b, D=2^(b-d), R=floor(2^b sqrt(10005)), Z=426880*5^d Q, and common quotient x0 with W=ZR-D x0 T=D rho+ell. W is a homogeneous full residual under positive source gauge even though rho and ell individually have carries. Zero W is an inhabited exact integer boundary, not an empty prefix. No claim to preserve all producer history from x0,W alone.

G57 — original suffix [n,m) with triple (p_s,q_s,t_s) in the SAME chart. Let T_m=T q_s+P t_s, Q_m=Q q_s. Unreduced new residual relative to old x0 is W*=q_s W-D x0 P t_s. Then h=floor(W*/(D T_m)), x_m=x0+h, W_m=W* mod (D T_m). For radical refinement b->b+s, r=R_new-2^s R in [0,2^s), W*=2^s W+Z r, D_new=2^s D; take the same signed divmod. Combined source/root unreduced residual is 2^s q_s W+q_s Z r-2^s D x0 P t_s. Neither correction is universally single-integer or free. A source correction must retain the original P t_s sign and the true suffix index.

G58 — gauge axis is indexed, not a fixed global label: G_n=product_(1<=j<n) gcd(|p_j|,q_j)=product 24*h_j, matching the existing native source recipe. For [n,m), G_m=G_n G_[n,m). Reopening before suffix composition requires the original raw suffix, not the normalized suffix again. Gauge maps W->G_n W, D fixed, x0 invariant. The two normalized source/root operations commute after Euclidean reduction by uniqueness of quotient/remainder of the same original terminal numerator and denominator; gauge commutes with each provided this indexed suffix factor is respected. Thus six faces and six endpoint paths on the explicitly typed three-axis cube; this is not a statement about arbitrary source revisions, physical time, Frobenius or autonomous FRACTRAN computation. Identities at zero source/precision step retain their typed command histories. Literal four-corner residuals scale by G_n and preserve exact signs and zero, including COMP6e parity correction. Separate zero correction h from zero W and zero signed tail (excluded active source).

G59 — added scripts/check_pi_p0_indexed_quotient_cube.py: independent integer oracle using original leaf formula and gcd gauge, explicit suffix/root/gauge transitions and all six faces/endpoint paths, independent full-prefix rebuild comparison at each vertex, BIDI numerator reconstruction, even quotient correction and signed corner gauge checks. Includes identity source and precision steps; no test or compilation executed. It is not linked into the production scheduler: W and x0 P t_s may be large, and reusing a quotient may cost more than recomputing. No promotion from algebraic transport to a performance benefit. Need native trace/fixture comparison, exact original decimal hashes and charged incremental-vs-full cost including source/gauge reopening.

P0 sequencing remains the four major obligations in COMP6e: original analytic Chudnovsky identity/Bishop same-real; exact native source acceptance; measured physical Pareto; external independently certified comparison. This cube is an acceptance/provenance aid, not another unconditional optimization. Inherited execution deferral remains; no CI, tests, compilation, kernel or benchmarks in this tranche.

## Analytic endpoint — 25 November, quantitative same-real cut (UNTESTED)

See `Docs/proofs/Paper9BishopQuantitativeEndpoint20261125.md` for the controlling source-specific proof: uniform negative-real q branch bounds, fixed precision n=max(1,ceil((k+5)/41)), b=k+2, literal Machin partial vs CH midpoint error <=4/(k+1), and native source-written limit consumer. Classical identity premises and prior CM receipts explicitly retained. New `DASHI/Foundations/BishopChudnovskyMachinLimitWeldExact.agda` consumes the actual original Machin partial stream and quantified embedded rational approximation bound; all-index native source producer and sound semantic reflection remain OPEN. `scripts/check_pi_p0_quantitative_same_real.py` fixtures UNEXECUTED. No kernel, compilation, tests, benchmark, CI or SOTA claims. Existing source/precision/gauge cube remains independent and production scheduler unchanged.

## 25 November — literal rational Chudnovsky midpoint and native source-bound limit (UNTESTED)

See `Docs/proofs/Paper9BishopLiteralMidpointReflection20261125.md`. Recovered original qMachinStage convergence and the existing full source-written 4/25^k native Machin remainder; reuse canonical floor-square-root and original split algebra. New `DASHI/Foundations/BishopChudnovskyRationalMidpointExact.agda` computes a fail-closed literal interval/midpoint with original indexed leaves and fixed cutoff/precision. New `DASHI/Foundations/BishopChudnovskySourceBoundLimitExact.agda` binds each certificate to that computed interval and transports its rational error to the original Bishop carrier, using pinned vendor absolute-value/subtraction laws and native reciprocal convergence. The ordinary all-index bound is derived on the previous classical identity premises; the native total-success/finite-sum/analytic reflection producer of StageCertificate remains OPEN. Source-written only, no compiler, test, benchmark, CI or kernel claim. Production GMP scheduler unchanged.

## 25 November — geometry-first endpoint reverse-solve (source-written, untested)

Controlling remaining dependency register: `Docs/proofs/Paper9GeometryFirstEndpointClosure20261125.md`. New `BishopChudnovskyIndexedEdgeAlgebraExact.agda` writes literal prefix and signed adjacent-edge identities. Finite cone: adjacent partial-sum brackets nest because the next signed defect reverses orientation and shrinks relative to the transported denominator by <2^-41; base S2>A/2 yields all-index positive sums in ordinary arithmetic. Native sign/order/totality proof remains open. Analytic A1–A7: phase, normalized q/modular identity, degree-41 cyclic self-isogeny, isolated double root, transverse cubic jet, local hypergeometric uniqueness, positive terminal normalization. Two routes: actual Bishop analytic construction or sound universal rational proof reflection, neither yet native-closed. Decimal-floor apartness/fair retry separate from width totality. No new arithmetic candidate, compilation, execution, CI, kernel or benchmark. Existing status flags unchanged.

Endpoint register section 6 reconciles actual `DASHI/Interop/LeanMoonshineDeltaIdentityPinnedReceiptExact.agda` and companion branch source declarations for eta24_eq_normalizedDelta, levelOne_weight_zero_const and exists_smul_eta24. External proof receipt retained; no new kernel replay. The prior two-slice kappa formula is derived with explicit conjugate-tangent apartness and BIDI beta reopening, avoiding quadratic-field inversion for the scalar; source Taylor binding and universal rational reflection remain open.

## 25 November — signed positive gap, Hecke generator BIDI and direct q uniqueness (UNTESTED)

See `Docs/proofs/Paper9SignedConeHeckeQCoordinate20261125.md`. New `BishopChudnovskyPositiveGapExact.agda` writes universal positive polynomial contraction, literal positive Q product and paired original affine identity. Pair positivity and nested interval totality derived mathematically, native T sign/positivity still open. Explicit 42-chart S/T action with unimodular corrections and inverse reconstruction reduces A3 to analytic j invariance, coefficient reconstruction and symmetry; 84-edge regression source unexecuted. A6 now uses direct original-q triangular coefficient uniqueness with |z|<=1345/3375<1 on the whole small complex disk, removing inverse-coordinate continuation from the critical path. Native Ramanujan/source reflection and same-real certificate remain open. No execution or new kernel claims; no GMP change.

## Native paired positivity/totality source extension (unexecuted)

New `BishopChudnovskyPairedTotalityExact.agda` writes explicit integer equality witnesses for positive, negative and nonnegative original coordinates. `weakGapIdentity` removes the factor 2^41 using the existing positive gap; `pairGapExact` proves the actual signed paired contribution is a positive successor; `evenWPositive`/`oddWNegative` prove the actual indexed product orientation; `evenTNonnegative`, `evenNonemptyTPositive`, `oddTPositive`, `allNonemptyTPositive` give the paired induction from T0=0. `positiveViewTotal` and `intervalAtTotal` rewrite the actual evaluator with these witnesses, not an alternate value. Corrected twoStepSource solver to expose both original next p and a variables so associativity is paid by the ring solver. These are complete intended proof terms, uncompiled; elaboration, pinned library compatibility and kernel closure remain open. No claim that source terms were accepted. Stronger S>A/2, shrinking widths, factorial interpretation and universal analytic overlap still require native proof; totality alone does not certify pi.

## 25 November — original rational overlap / Bishop order owner reconciliation (UNTESTED)

See `Docs/proofs/Paper9RationalOverlapBishopReuse20261125.md`. Recovered pinned bidirectional rational-order reflection, existing Machin rational stages and exact 4/25^k Bishop remainder, strict 3<pi_M<22/7, actual interval/regular-real constructors and finite convolution donors. New `BishopChudnovskyRationalOverlapExact.agda` writes sharp midpoint bound from the two literal crossed endpoints, membership-to-cross reflection and all-index source certificate consumer. At k=0 use 22/7 instead of 4 to preserve the error budget. Native source width/rate budget and analytic crossed inequalities remain OPEN; no proof promotion. Direct original-q triangular coefficient proof refined; no new generic formal-series engine. Lean #104 source theorem recovered, proof replay not observed. No compilation, tests, CI, kernel or benchmark in this cut.

## Rate-budget source proof extension (uncompiled)

`BishopChudnovskyOverlapBudgetExact.agda` writes the universal Nat inductions k+1<=2^k and 4(k+1)<=25^k for k>=1 (the latter uses the exact positive step margin 188+96j). Existing FiniteNatFractionOrderExact reflects the denominator cross-products, with actual source Machin denominator and explicit nonzero witnesses. `budgetFromWidth` derives the entire sharp-radius budget from the literal fixed-schedule width <=2^-k: for k>=1 h+e<=(3/2)/(k+1)<=4/(k+1); k=0 uses the exact rational inequality 1/2+22/7<4. `literalConvergenceFromWidthAndCross` now needs just two all-index source families: literal CH width and literal rational crossed endpoint inequalities. It consumes previous paired totality and overlap modules. No kernel or compilation, no guarantee of elaboration, no analytic overlap proof assumed. This supersedes the earlier remaining separate rate-budget obligation at the source-written level only. Native F3 width, actual common-value A1-A7/F5 cross, and exact-head verification remain open.

## 25 November — integer width residual and pinned Ramanujan rigidity (source-written, untested)

See `Docs/proofs/Paper9IntegerWidthRamanujanRigidity20261125.md`. New `BishopChudnovskyWidthSourceExact.agda` writes actual signed defect magnitude contraction, all-index M^n H_n<=A Q_(n+1), translated lower plane 2T-AQ>0 by paired induction, radical bound, cutoff exponent and final integer width numerator budget. Ordinary full width proof: J=Q_n H_n, K R J<=2 tL tH, K dL<=tL imply width<=3/s<2^-k. Native cross/parity, plane/order, power schedule and fraction reflection joins remain; no literalWidth theorem promoted. Recovered actual Lean levelOne_nonpos_wt_const (stronger than weight-zero); f/Delta eliminates weight 4/6/8 cusp forms, Serre/log-derivative anomaly cancellation proves all three classical Ramanujan identities on the named analytic premises. Formal derivative/quotient/cusp packaging and same-object reflection remain. No new production candidate, tests, CI, compiler, kernel or benchmark.

## 25 November — literal width reflection and Hecke Laurent reconstruction (source-written, unverified)

See `Docs/proofs/Paper9WidthReflectionHeckeLaurent20261125.md`. New `BishopChudnovskyWidthReflectionExact.agda` writes intended `literalWidthBound` on actual O.window, using positiveView source equalities, signed cross magnitude, both ordered branches, source schedule and denominator-cleared corner comparison. No compiler or kernel acceptance; possible elaboration repairs remain. A3 ordinary proof uses actual 42 Hecke charts, pole bounds, existing level-zero rigidity after Laurent cancellation, dual adjugate symmetry and distinct leading Puiseux branches. Original diagonal and fixed slice scripts are linked through exact cyclotomic norm/log-derivative recurrence and sufficient Laurent truncations; no full bivariate table necessary. Analytic source packaging/reflection and universal cross remain open. No tests, CI, benchmarks, new GMP candidate or status promotion.

## 25 November — selected CM real isolation and direct signed tau Taylor (UNTESTED)

See `Docs/proofs/Paper9CM163SourceReplaySignedTaylor20261125.md`. Selected q is real; actual j real slice plus original dyadic half-unit enclosure and complementary coefficient dominance avoid general complex norm machinery. Direct Taylor in original tau coordinate gives denominator-cleared 163 S2*((alpha^2-alpha)*j''+j'*h'')=(j')^2*(alpha^2-alpha)*(41 P3-326 S3), no local inverse j or quadratic-field inversion. `JInvariantCM163SignedTangentPolynomialExact.agda` writes integer polynomial identities and signed discriminant. `scripts/check_cm163_source_bound_jet.py` adds original pinned coefficient forward Laurent replay, original 128-bit dyadic endpoint binding, integer dominance and signed scalar jet receipt; UNEXECUTED. Native analytic source/finite coefficient reflection and universal rational cross remain OPEN. No kernel, tests, CI, benchmark or proof promotion. Existing CM computation owners and attribution retained.

## 25 November — original Eisenstein completion, Euler jets and Rankin–Cohen reduction (UNTESTED)

See `Docs/proofs/Paper9OriginalEisensteinEulerJets20261125.md`. Recovered actual Agda unit-disk completion, Round11 Machin source, lattice same-object compiler, native proof-relevant j, and Lean literal E4/E6 target semantics, normalized Delta cusp and nonvanishing. New `JInvariantBishopEisensteinRealSliceExact.agda` writes realness of literal completed E4/E6/Delta/j from actual real q and negative Delta, via original series limit uniqueness. New `JInvariantBishopEisensteinEulerJetExact.agda` writes all-order literal weighted coefficient absolute convergence, using existing polynomial-geometric majorants; derivative interpretation still open. New `JInvariantEisensteinRankinCohenResidualExact.agda` writes signed residual adjugate identities: weight12 cusp bracket 3E6 DE4-2E4 DE6=1728 Delta follows on named analytic premises from existing weight12 rigidity/first coefficient, giving both DE4/DE6 via determinant Delta, with only weight4 E2 correction remaining. No independent E2 model or new carrier; native derivative/slash/cusp packaging and actual source binding remain. No execution, kernel, CI, benchmark or proof promotion; all new terms uncompiled.

## 25 November — actual cusp derivative target and level-three coefficient bridge (UNTESTED)

See `Docs/proofs/Paper9EisensteinThreeB54Derivative20261125.md`. Reuse pinned Mathlib cuspFunction/qExpansion analytic derivatives on original E4/E6; companion branch `research/paper9-original-eisenstein-derivative-20261125` at 7ffe113edd10d2ba1a28fcea5be00b888bccaf29, source-written actual q-bracket derivative at zero and weight12 rigidity consumer. Slash/cusp packaging, Delta product derivative and native binding remain open. New `JInvariantEisensteinThreeB54CoefficientBridgeExact.agda` ties actual 240,-504 to 744,1728=32*54 and classical level-three t=(eta/eta3)^12, j=(t+27)(t+243)^3/t^3, whose first q coefficient is exactly 54+196830. Independent Leech theta/eta chart yields 196560+6*54. External Maier/Elkies and classical theta attribution preserved; no Monster equivariance or analytic theorem promoted from coefficient arithmetic. No new P0 dependency, execution, CI, kernel or benchmark.

## 25 November — 66/12 original Tate signed ultrametric and Delta derivative (UNTESTED)

See `Docs/proofs/Paper9Tate66UltrametricDeltaDerivative20261125.md`. New `JInvariantThreeBTate66UltrametricExact.agda` reuses actual Tate dimensions and SSP369 prefix carrier, signed VpDepth comparison gives v3(66-12)=3 and gain2 versus unsigned 78 gain0. Y443 actual 66 pairs/12 nodes/78 relations matches signed cardinality only; natural arm swap virtual trace is not Tate trace. Fricke central shell t=27u preserves v3(u+1) and both j-chart valuations on named rational premises. Lean companion c3b77fc94f302d8a2b4bf733c5f1ff4229ae7146 writes literal Delta cusp-function identity, derivative and Ramanujan46 consumer needing actual bracket and disk membership. No new kernel, compiler, tests, CI or benchmark; no analytic localization or F5 proof promotion.

## 25 November — original 66 prefix and actual bracket cusp closure (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9IntegratedFrontier66Cusp20261125.md`. Original 66 means ordered 6->6 neutral prefix, not integer sixty-six radix expansion. New `TernaryThirteenNeutral66PrefixExact.agda` reuses original word/pants/cylinder and split/join owners for prefix, suffix round trips and nonzero/last-coordinate non-descent witnesses. No Tate-to-word semantic map asserted. The earlier signed valuation chart is a distinct arithmetic observable. Lean companion `a541a44dc990cba133d031eabc9c01adf287beeb` adds actual `Paper9BracketCuspClosure.lean`: intended holo/zero cusp, derivative anomaly cancellation, genuine CuspForm packaging, actual q-disk equality and first coefficient. `ramanujan46FromSlash` consumes actual slash covariance, which reduces to the two original derivative chain rules; E2 correction still open. All terms uncompiled; no native/Lean kernel, tests, CI or benchmark. Manuscript main text reconciled, historical ledger preserved. A2-A7/F5 remain critical; 66 is secondary donor, not a P0 dependency.

## 25 November — original Euler Möbius transport (SOURCE, UNVERIFIED)

Lean companion `23602955180fdddd46375c5ce6198f504950a0e6`, then `3063310926b1ab038a85ab0fbedf65ea63d81f91`: `Integration/Paper9EulerMobiusTransport.lean` writes actual qParam derivative, original modular-form cusp extension derivative, determinant-one fractional-linear derivative, local (only on H) transformation equality, derivative equality and signed Euler anomaly. `dxTransport`, `dyTransport`, `originalBracketSlash` and `originalRamanujan46` now have intended unconditional proof terms from the pinned imports, superseding the prior explicit derivative-transport hypotheses at SOURCE level. `originalE2Transform` writes the actual normalized Delta log derivative anomaly via the same weight-12 transport; `e2CorrectedCovarianceAlgebra` writes exact cancellation after its second derivative. Still unpaid: actual derivative of the logarithmic anomaly and corrected weight-four modular form/cusp quotient, all new Lean elaboration and kernel replay, A3-A7/F5 native/source reflection and F1/F6-F9. No new compiler, executable checks, CI replay or benchmark. Do not call A2 kernel-closed or the independent Bishop endpoint proved.

## 25 November — original Ramanujan system and compact q differential transport (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9RamanujanQHypergeometricClosure20261125.md`. Lean companion `dd30fc1016177e08a4f13588e55247e2ad671c5c` then `9ee290cd9343a85aa0e3710651c42672812f1d87` writes intended `originalRamanujanSystem` on actual E2/E4/E6, reusing original eta-product analytic unit, actual local derivative anomaly, weight4 cusp packaging, existing eta24 domination and negative-weight rigidity. All source terms uncompiled; no kernel closure claimed. New `Paper9HypergeometricQTransport.lean` writes actual punctured-q transport and differential coordinates a=(E2 E4/E6-1)/6, h=E4^3/E6^2-1, L a=-a^2/2+h(a/2+5/72), L h=h(h+1), L z=z. Two exact polynomial multiplier identities reduce ODE to actual LF=aF and iterated product law; actual binomial branch and convergent coefficient semantics still open. A3–A5, A1/A7 native binding, F1/F5 and acceptance unchanged. No compilation, executable checks, CI or benchmark; no new production optimization.

## 25 November — selected hypermetric comparison and cusp-order transport (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9HypermetricCuspOrderFactorial20261125.md`. Actual RG two-metric, H3 residual and indexed chart transport donors audited; no 369/analytic metric identification. Fixed-radical reciprocal adjacent widths have exact shared-endpoint distortion S_n/S_(n+2), at most 2 on actual source band; signed sum contraction 2^-41 transfers to <=2^-40, radical refinement separately bounded. Lean companion `e9b8e422c4b8503074dbf45d6bf6632bd711bbae` writes actual normalized log sqrt branch/first derivative, cusp-order leading multiplier n and residual n^3*g0, all-index factorial ratio and actual CM leaf ratio, exact rational metric comparison. Actual H analytic ODE, germ uniqueness assembly and native prefix/rational reflection remain. All new terms uncompiled; no execution, kernel, CI or benchmark; A3–A5/F5 and acceptance remain open.

## 25 November — actual factorial-series ODE and local hypergeometric identity (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9OrderedCuspActualSeriesODE20261125.md`. Latest #1552 ordered ultrametric and #1545 single residual actual donors read; #1549/#1553 reviewed at metadata level. Lean companion `094b4f6cc9c9a653783d7ff42621dc91e06c4d89` writes all-order normalized germ uniqueness, actual sqrt ODE, literal factorial-series radius and Euler jets via pinned derivativeSeries diagonal, actual composed H(z) ODE, intended unconditional `actualHyperIdentityGerm` and connected-disk consumer `actualHyperIdentityBall`, plus signed period algebra. A6 intended local analytic identity now source-written; selected actual E4/E6 small-disk norm bounds and CM q membership, real-positive branch, CM certificates, native F1/F5 reflection and all elaboration/kernel replay remain open. All new source uncompiled; no executable arithmetic, CI, kernel or benchmark. No donor branch modified.

## 25 November — selected actual CM domain and signed certificate consumers (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9SelectedCMDomainCertificateConsumer20261125.md`. Lean companion `85eff0dd4590c0f6c37f9dc26c02ef68dff95dd0`, then `979f2ba17ceb7bb701efc79377b6ff6dfdbf6156`: `Paper9SelectedCMDomain.lean` uses original shifted E4/E6 limits, q-chart lift and zero mode to source-write actual norm bands, GoodZ on |q|<=2^-36, actualHyperIdentitySelected and first-jet local congruence, positive period normalization. `Paper9CM163CertificateConsumer.lean` writes the degree-80 complement dominance consumer, direct signed cubic elimination and original j*z=1728, with explicit certificate premises. Local exact arithmetic checked the three period constants and 269/675 domain bound; SymPy checked three tangent linear combinations identically zero. No actual CM packet replay or kernel acceptance. A3 actual Hecke product/Laurent binding, A4 actual coefficient and dyadic reflection, A5 actual analytic Taylor source and signed correction, selected CM q membership and positive branch, A1/F1 native source and F5 all-index rational crosses remain OPEN. No new production arithmetic, benchmark, CI, or general-purpose infrastructure. Agda PR reported mergeable before this cut, unmerged; verify live before any merge. Classical and existing donor attribution preserved.

## 25 November — literal F1 prefix and original CM163 exact replay (FINITE PASS; SOURCE UNVERIFIED)

See `Docs/proofs/Paper9LiteralPrefixCMReplay20261125.md`. Original CM degree-82 diagonal/degree-42 slice, signed correction and independent forward Laurent replay from four exact Git-blob-matched Python sources **executed locally, PASS**. Dyadic original 128/160/256-bit enclosures pass; 128-bit offsets match the original Agda receipt. Dominance floor=6593105375567751; kappa=-77859659565707/19943834790540897829879824384000; s2=77265280/90856689. Full local coefficient/receipt SHA256 and regeneration instructions in proof register; finite acceptance only, not formal reflection. Local independent factorial/product and weighted prefix checks 192/192. New native `BishopChudnovskyPrefixSemanticsExact.agda` source-writes rational product and weighted prefix recurrence and original positiveView binding; Lean `Paper9LiteralFactorialPrefix.lean` at 92599ad2ed252824d163640fd10f4308893434b5 writes intended all-index literal factorial and actual weighted hypergeometric limit. `Paper9ActualCMPoint.lean` at a83e83f45ebd8c71b2b692dfc31bd795a6bbfa5b writes actual upper-half-plane fixed point, signed tangent, q phase/domain and actual CM hypergeometric/first-jet specialization; four exact symbolic geometry identities passed. No compilation or kernel acceptance. F1 Agda factorial or sound rational reflection, A3 actual Hecke analytic/Laurent binding, A4 finite coefficient/dyadic soundness reflection, A5 actual Taylor/correction, A7 actual real-positive branch, A1 original Machin and F5 all-index rational crosses remain OPEN. No GMP change, CI or benchmark. Attribution preserved.

## 25 November — actual Hecke/discriminant and reverse-solved signed period (FINITE PASS; SOURCE UNVERIFIED)

Controlling latest endpoint register: `Docs/proofs/Paper9ReverseSolvedActualHeckeDiscriminantPeriod20261125.md` (66af4a52b3cb122b36be2a97ae948e13e5e48899). Audited original source owners and all A1–A7/F1–F9. New Lean source on existing companion branch: actual j SL2 invariant, cusp unit J=qj, actual signed j first/second derivatives (3c717d9985dac900a6b1287a7779525c5c3e941d); actual 42-chart S/T covariance and adjugate reverse root (02b131fe263863b1daeea175886444e97f055fd3); formal normalized Laurent column uniqueness/log-norm coefficient recurrences (29380f1066cc16f7d460019a49fd9988e6f96b79); formal actual normalized Delta qExpansion shift U=Delta/q and JRelation/JUnique (ff8f49d720b84a5ceab63ae1e92fdb40e29b1b13); actual real-positive CM branch and weighted period/literal prefix limit on exactly two remaining CM inputs (8b5a85dcdfc68b3236b81c279368c0d247264298): jTarget(cmTau)=-640320^3 and actual transverse kappa jet. The signed period scale is p=pi Im(tau)=pi sqrt163/2; do not conflate with pi sqrt163. Exact local SymPy checked 126 original S/T/dual matrix identities, all 42 pole bounds and the Euler/signed correction residual. New `scripts/check_cm163_junit_discriminant_reflection.py` at 187cf31244d83ae18bf96e613ad411b68bbcf387: original eta-based J producer Git blob verified; normalized-discriminant recurrence J_n=a_n-sum_(i=1)^n u_i J_(n-i), u_i=(a_(i+1)-b_(i+1))/1728, matched **3363/3363** coefficients (full degree-3362 frontier, 5.1364s). This removes infinite eta-log-derivative formalization from the coefficient-producer path; does not remove eta from nonvanishing/Ramanujan. Actual analytic Hecke Laurent/growth/pole removal and symmetry, actual Taylor/germ coefficient binding and finite packet reflection, actual dyadic analytic soundness, signed CM Taylor root/jet and A1/F1/F2/F3/F4/F5 universal rational source binding remain OPEN. No new downstream adapter, GMP change, kernel/compiler, CI, benchmark or solvedness promotion. All intended Lean proof terms uncompiled, including finite decide targets.

## 25 November — recovered original Hecke owners / direct ramified pole removal (FINITE PASS; SOURCE UNVERIFIED)

See `Docs/proofs/Paper9RecoveredHeckeOwnersPoleRemoval20261125.md` (c56124763f1c244fbac2f07e9971b0df3f941d16). Original PR #580 at 554c127e3727013d0698846eb2a88bde011c5efa owns classical variable-degree correspondence, positive finite neighbour system, prime-regular geometry and separate characteristic/Hecke degree indexing. Restored those four original files verbatim (0ce2e39, 5a62d43, 7a7789f, 511d785); previous omission was a branch recovery issue. Native `CM163ClassicalHecke41LatticeSpecializationExact.agda` (97d41dd) uses original Fin42 neighbour/fold and original lattice rows, dual correction returns common scale 41, not scalar j equivalence. Local SymPy 126/126 projective chart/correction/dual arbitrary row-basis checks PASS, literal S table and normalized phase/exponent checks PASS. Lean `Paper9HeckePoleRemoval.lean` at 1cccf93c0887c653da168b17a7beaa3bb40a9906 consumes actual pinned `SpecialLinearGroup.SL2Z_generators`, actual j/chart holomorphicity, original weight-zero rigidity and zero-cusp residual. A4 diagonal and fixed slice now have independent direct residual consumers: if t^3362 R_d=t^3363 G_d or t^1722 R_s=t^1723 G_s, G continuous at 0 for actual t=exp(2pi i tau/41), cancellation gives zero cusp and actual identity. A4 need not wait for bivariate symmetry. Remaining A3: actual analytic normalized product and Taylor/formal coefficient/packet order reflection; A4 actual dyadic enclosure; A5 full bivariate symmetry and actual signed Taylor. No repeated Hecke algebra or new downstream adapter. All new proof source uncompiled; no kernel/CI/benchmark or solvedness promotion. Classical and existing DASHI/JMD/Aristotle donor provenance preserved.


## 25 November — actual Hecke finite Taylor remainder (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ActualHeckeFiniteRemainder20261125.md` (e9f31397a71fa24cab190937d3b446188799184a). Lean companion `7d58601790fce7c4965615d305488c679045e9d0`, `Integration/Paper9HeckeFiniteRemainder.lean`, writes finite signed germ remainder transport, monomial ramification, original normalized diagonal/slice/column expressions and consumer of existing zero-cusp rigidity. Actual Taylor(J_a)=J is forced by actual qExpansion(deltaQ)=deltaPS, deltaQ=q U_a and U_a J_a=x^3, or equivalently finite polynomial quotient with analytic remainder; no eta-log coefficient proof needed. Diagonal J truncation 3322 sufficient (shift 40), slice 1722; existing 3363 coefficient receipt retained. Cyclic phase rotation and exact norm/log recurrence prove descent and specify finite packet divisibility through t^3362/t^1722; actual finite packet reflection remains unpaid. Local SymPy 35/35 algebra/exponent checks PASS; not a full replay. Next exact tasks: actual Taylor coefficient/finite quotient bridge, actual chart exp identities, reflect packet and assemble product/order; then independent A4 dyadic root and A5 bivariate symmetry/signed jet. A7 still conditional; F1–F9/A1–A6 existing gates unchanged. All new Lean source uncompiled, no kernel/CI/benchmark. No new Hecke carrier, no GMP change. Preserve original classical and DASHI/JMD/Aristotle/Mathlib source attribution.


## 25 November — actual Taylor-unit reflection and shifted analytic tail (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ActualTaylorUnitReflection20261125.md` (7360fafad4dc18212c122229d1b8b9fe3193d9c3). Lean companion `b3ca690606097fd4f1e6d13620c6405088a07919`, `Integration/Paper9ActualTaylorUnit.lean`: source-writes germ equality, factorial-normalized Leibniz from pinned Mathlib qExpansion_mul, Taylor(id)=X, Taylor(deltaUnit)=U by cancelling X at coefficient n+1, and Taylor(jUnit)=J by original JUnique. Pinned iterated dslope/fslope supplies exact analytic shifted tail including zero mode, yielding actualJTruncation for every m. Actual q-chart exponential transport and sharp finite-factor remainder (3323+40=3363 diagonal, 1723 slice) source-written. Local SymPy 42/42 polynomial-model algebra/exponent checks PASS, not a full CM replay or proof verification. No Lean/lake available; no kernel/CI/benchmark. Remaining A3b/c: actual normalized product/phase and columns assembly, cyclotomic descent, sound integer packet reflection. A4 actual dyadic root, A5 symmetric Taylor jet, A7 and F gates remain open. Hopf369 P0H #1554 user-supplied donor is methodological (original object/finite observation/retained tail), not a physical or mathematical identification. Attribution preserved; no new Hecke carrier or GMP change.


## 25 November — actual 42-chart assembly and sector packet gate (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ActualHeckeProductAssembly20261125.md` (02d7c38ba07e2730b5b002aba8016a0688b25f9e). Lean companion `e54be6f4bd0a1ab6c19b86543e9b45bb18d93d1b`, `Integration/Paper9HeckeProductAssembly.lean`, source-writes actual Fin42 product split, phase product, diagonal/fixed-slice normalization, sharp finite product and column remainders, polynomial divisibility via pinned `Polynomial.X_pow_dvd_iff`, and direct original zero-cusp rigidity consumers `diagonalFromCoefficients`/`sliceFromCoefficients`. The remaining coefficient-zero premises are literal, not a hash. Primitive-root sector cancellation and strong-induction norm recurrence uniqueness source-written; actual rotation/phase-filter and concrete J/H/L/N/column integer reflection remain open. Only 83+43 q coefficients need comparison after rotation reflection; prior integer packet retained. Local SymPy 1.14.0 48/48 exact small-polynomial resultant/recurrence, phase and exponent checks PASS (not full CM replay). Lean/lake not on PATH; all proof terms uncompiled, no kernel/CI/benchmark. A4 actual dyadic root isolation, A5 symmetric analytic jet, A7 and F gates remain open. No new Hecke carrier or GMP change; original attribution preserved.


## 25 November — primitive phase descent, literal CM163 packet and integer residual cast (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9CyclotomicIntegerSectorReflection20261125.md` (858d0ef359433449a305f1f13db20de8f5fc075a). Lean `Integration/Paper9CyclotomicPacketReflection.lean` at 4dd52c66eadd36c29582d5b82f83f27f40b87066 source-writes actual primitive phase rotation, pinned Mathlib expand/contract descent, finite character trace, denominator-cleared Euler residual product and original diagonal/slice sector consumers. Literal signed-hex 126 coefficient data committed at db0eb9ac260c49d749e2be42eea4566c15883137; Lean literal arrays and concrete 83/43 gates at 1d18136b84371bded22f305cde294f76db768f76. Integer polynomial residual cast, finite Euler uniqueness, norm cast and column transport source at 128291dddab6e61c0db13f8c934346a43256e698. Local scratch Python/SymPy exact replay exit 0: 3363 J parity, 5086 H/L identities, 126 N/V identities and 126 forward sector coefficient comparisons all PASS, both shifts, half-unit dominance and historical signed kappa/correction pass. Independent connector BigInt reconstruction matched local FNV64/length and committed packet read-back; no kernel or direct cyclotomic product run. Existing full source-bound entrypoint not executed; dyadic analytic enclosure not rerun. Remaining A3c actual integer J binding, executable recurrence/cast soundness and literal residual proof consumption; A4 actual dyadic root, A5 symmetric analytic jet, A7 and F gates open. All Lean terms uncompiled; no CI, benchmark or new backend. Original attribution retained.


## 25 November — canonical integer Fourier binding, concrete sector gates and actual CM root (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9EisensteinIntegerCMRoot20261125.md` (d80db1a4174d81dbe7963ce2d7b6d8ee0236ed5c). Lean canonical all-index E4/E6 coefficient source at 7ee0d13264e20a20d1ff8580d1fe1cfd4ad2bac9 consumes the original Agda-shaped shifted HasSum/limits and pinned qExpansion_coeff_unique; derivative zero/first coefficient consumers updated at 9e3115c3dca2f521d0ba60e20f1056e494ff74c9; integer discriminant/J finite quotient uniqueness at 23e68a154686dcdecb76aa762c9106df3bbe3560. Concrete signed integer residuals to actual diagonal/slice gates source-written at aa0d0cabcab4e403462cd4bfe68602b3606ea04f, using J cutoffs 3322/1722 and zero modes (1,0,1). Local exact Python/SymPy scratch: 6726 divisor comparisons, 6728 majorant bounds, 3363 shifted discriminant and 3363 J residuals PASS, 14 signed first-defect cases in both families PASS. Connector-side exact replay of actual literal packet with sharp cutoffs: 5086 H/L, 126 N/V and 126 literal comparisons PASS; binomial shift, both double roots, tangent relation and half-unit dominance pass. Original exact dyadic checker blob 8581a684cfb6ba6bfbfa45adbf6bfe01e9617258 locally hash-verified and executed at 128/160/256 bits, all PASS, original 128-bit offsets recovered. A4 direct source-written actual point and binomial-shift isolation consumer at 281748617f2350b532ba39da488aada42d3c8f34. A3c remaining executable finite recurrence/residual reflection, not another Hecke generator. A4 remaining literal shift/dominance and actual dyadic analytic reflection. A5 symmetric transverse Taylor, A7 and F gates open. All Lean source uncompiled; no kernel, CI or benchmark; full source-bound jet entrypoint not run. No GMP change or solvedness promotion. Attribution retained.


## 25 November — finite residual reflection, literal shift and direct symmetric tau jet (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ExecutableResidualSymmetricTauJet20261125.md` (7b33bf069769001403c4ea35a734af644ee0d67a). Lean source `Paper9FiniteResidualCheck` (603fd5e) writes finite convolution/ramification and clipped Horner soundness into the existing analytic gates, `Paper9ExecutableCM163` (bc226bc) supplies candidate U/J/L/N and decidable unitOK/diagOK/sliceOK, and `Paper9CMShiftCheck` (3c41f66) writes literal integer dominance reflection and rootOfChecks. No generator-correctness or hash premise; actual Lean elaboration and boolean execution remain unpaid. Local Python/SymPy scratch passed 6646 divisor comparisons, 3323 each U/J and full diagonal sector, then timed out at 90s in the slice. Separate GMP scratch replay completed both sectors (5086 H/L, 126 N/V, 126 Horner, 52 signed probes PASS); reconstructed compact signed-hex packet SHA256 9f61b1ece8f5539106576071d82abe5b07f909a96c998495c248158446caa9e6 matches the committed literal packet. Both double zeros, tangent ratio and strict half-unit dominance PASS. Prior exact dyadic receipt retained, not rerun. `Paper9SymmetricTauJet` (2315ab9) writes reverse-chart polynomial uniqueness, actualTwoPointSymmetry on explicit universal monic-slice/separated-infinite-image premises, and direct tauJetToSigned, with local SymPy exact algebra PASS. Universal slice existence is triangular with unit pivots; cusp separation follows from distinct primitive phases and the infinity pole in ordinary mathematics, formal attachment remains. No full bivariate coefficient table, inverse j, new Hecke carrier or production GMP changes. A3c actual Lean check/elaboration, A4 analytic dyadic reflection, A5 universal slice/separation and actual symmetric pullback cubic/branch attachment, A7/F gates remain open. No kernel/CI/benchmark; full original source-bound entrypoint not run. Original attribution retained.


## 25 November — prior Machin / Taylor / infinite-j source-owner recut

See `Docs/proofs/Paper9OriginalMachinTaylorInfiniteJOwnerAudit20261125.md` (1035156abd1e507e4edb52fb19ce63802d6e3847). Do not reconstruct existing analytic machinery. Original Bishop Machin arctan interlacing/π rational windows and Lean faithful eval_machinPi_eq_real_pi, Bishop exponential ratio-half/series and faithful eval_exp_eq_real_exp, original E4/E6 degree-4/6 majorants and original scalar seriesTail/actualJSeries already exist. The older literal Agda CM half-integer checker explicitly leaves actual analytic enclosure open. New Lean `Paper9CMOriginalMachinWindow` (7eb0d74) uses original 90/91, 30/31 prefixes, pinned alternating sum bounds, exact source evaluator and original 128-bit pi/sqrt endpoints. Independent exact Fraction floor/ceil and integer-square checks PASS; closed Lean piRoundOK/sqrtRoundOK still unpaid. `Paper9UniversalMonicSlice` (60223aa, 24e775b) constructs generic slices from original normalized unit pivots and consumes sliceSectorConsumer; `Paper9SeparatedCusp` (4d5c3fe) attaches existing q-unit and exact phase asymptotics, proves intended eventualChartSeparation, separatedImageInfinite and actualSymmetry. No prior actual separated-image theorem located; infinite q-series is not itself infinite image. `Paper9OriginalCMChartWeld` (a780e72, 0cd8bf1) instantiates existing Taylor tail at actual centered j, uses exact rational original Mobius remainder, actual branchVanish and correctionFromTransverse into existing period scalar. `Paper9ActualCMRoot` (3569b6d) now consumes existing cmJReal rather than duplicate proof. Local SymPy toy 7 triangular rows, 820 primitive phase differences and exact Mobius residual PASS. All new Lean source remains UNCOMPILED, no kernel claim. Remaining A4 existing exp/Fourier bounds instantiated at original 180-term dyadic interval and actual quotient binding; A5c actual mixed cubic extraction and literal shifted coefficient reflection; A7 existing positive period consumer; A3c actual Lean decision checks and F1/F5 native acceptance separately. No new analytic foundations, no CI, no new production GMP or full literal original checker rerun.


## 25 November — A5 reciprocal Möbius disk max-cut

See [reciprocal disk proof and arithmetic receipts](../proofs/Paper9ReciprocalMobiusDiskPeriod20261125.md).
Reuse the existing Hecke matrix and CM fixed point, not the engineering Smith observer.
Linearize the literal forward/inverse degree-41 charts in the original CM disk;
factor the actual product by the symmetric quadratic
w²+v²+(81/41)wv. The residual's first symmetric differential replaces the
mixed cubic extraction. The scalar period consumer is source-written in
Lean Integration/Paper9MobiusDiskPeriod.lean (0e3271e3fbca831b8dae77acfd1bdd153589c178).
Remaining: chart 0 inverse binding, divided-difference first-order analytic
weld, four literal coefficient equations; then consume actualCMWeightedPeriod.
Exact original coefficient packet shift and independent 128/160/256-bit
dyadic algorithm replay passed; A4 analytic interval reflection remains unpaid.
No kernel acceptance, native same-real proof, or performance improvement claimed.


## 25 November — scalar reciprocal and normalized cusp replacement cut

See [scalar reciprocal proof and normalized cusp window](../proofs/Paper9ScalarReciprocalNormalizedCusp20261125.md). This supersedes the previous bivariate residual construction as the critical path, retaining it as an independent proof route.
A5 uses the original chart-0 and chart-1 factors and the 40-index finite polynomial difference, with scalar derivative comparison only. Lean Paper9ScalarReciprocal (32057f677a9185175cbf32b172131ce263b54cc0) contains source-written reverse binding, finite product difference, algebra, scalar germ and existing literal-prefix endpoint consumers. Actual germ and coefficient instantiation plus kernel replay remain.
A4 uses j=1/q+744+O(q), explicit error <=500000|q|, and exact rational positive exponential window with original Machin/sqrt dyadics. Lean Paper9CMNormalizedCuspWindow (4e0df23da0f7718d29ed673f11cd74ec581f7508) contains the finite predicate and root consumer. Actual exp/Fourier semantic binding remains.
Local SymPy 11+1 exact identities, 164 product-difference cases, Fraction exponential and Fourier constants, and original packet BigInt shift/ratio/dominance passed. No full residual replay or native kernel acceptance this turn. F1/F5 and production performance objectives unchanged.


## 25 November — A4 actual Delta and exponential assembly

Starting PR head f8bcfb6fe623b31e29b8187478c5c76d92cb1aa3. Reuse original signed coefficient bridge (240,-504; 744; 1728=32*54), actual Fourier HasSum tails, deltaUnitSourceOnDisk, formExtAt, actual jExtAt, cmQPhase/cmQSmall, original Machin and sqrt windows, and Mathlib's exp series as in BishopVendoredExponentialSemantics. No level-three or Monster representation premise added.

Lean Paper9ActualDeltaWindow (3938f60c3a9f43f44e2d650cc7dca8ef7c887497, 73a1acd836f4bd420c89eee3640634fdaafd9d52) writes smallBands, cubeSquareTails, deltaTail, originalDeltaRelation, actualCuspRemainder and actualCMFourierQuarter. Exact residual factorizations yield cube/square errors 17232484 r^3 and 18252361 r^3; combined normalized Delta error (35484845/1728) r² < 24000 r². Existing cuspRemainder gives <=500000 r, r<=2^-36. Lean Paper9CMExpWindow (2e000b641fc684b8729d72f5907399b7cf21f8e0) writes original exp HasSum, shifted factorial ratio bound, positive prefix/upper bound, actual Machin/sqrt argument bracket, actualExpQuarter and rootFromOriginalFiniteChecks. Endpoint now has six explicit finite premises (unitOK, diagOK, shiftOK, piRoundOK, sqrtRoundOK, expWindowOK); no free analytic enclosure hypothesis in its statement. All new Lean source remains uncompiled; theorem elaboration including exact library API and tactic repair is outstanding.

Executed locally via Python SymPy/Fraction: E4 cube and E6 square symbolic prefixes and normalized discriminant; all remainder constants and radius inequalities; original 90/91 and 30/31 Machin rounding, sqrt squares, exact 180-term positive exp window with ratio-half tail. Exp endpoint differences from 640320³+744 approximately -7.499274099153538e-13 and -7.499273976413151e-13. No Lean/Lake/Agda executables found; no native kernel checks or manual CI. No full A3c residual rerun. A4 is now source-written to the original finite-check consumer, not kernel closed. Next cut: A3c finite execution, A5 actual reciprocal scalar germ and shifted coefficient attachment; elaborate A4 in parallel. A7 and F1/F5 unchanged.


## 25 November — outstanding-owner re-audit (supersedes broad F1/F5 labels)

Audited exact Agda head f3d32443e69a7dc31f6933f661e58fd57e73d28a and Lean companion; donor #1529 head d8956bb9ba274e40734bb5ff136c014dd9b38dda. Source bodies, not filename parity. Native BishopChudnovskyPositiveGapExact supplies weightedContraction, PairedTotalityExact supplies allNonemptyTPositive/positiveViewTotal/intervalAtTotal, PrefixSemanticsExact supplies prefixSemantics/literalPositivePrefix on the actual unnormalised rational leaves, WidthSourceExact supplies defectContraction/scaledDefectBound/nonemptyLowerPlane, WidthReflectionExact supplies literalWidthBound for all k, OverlapBudgetExact supplies budgetFromWidth, RationalOverlapExact supplies nativeMembershipToCross and the literal limit consumer. No new mathematics needed for these stated interfaces. All source-written status retained; no kernel acceptance inferred.

New BishopChudnovskyCrossOnlyEndpointExact.agda (1c588bf72bcd623932c06a1fde4febe4d36b9509) composes the actual width theorem with literalConvergenceFromWidthAndCross. Only c : forall k, Cross(window k, qMachinStage k, machinRadius k) remains as a premise of this endpoint; alternatively actual native interval membership via nativeMembershipToCross. F1 native source semantics already written; exact Agda-to-Lean factorial/interval correspondence or all-index rational proof reflection still required. F5 common-value cross remains, not a new convergence theorem. Lean Paper9LiteralFactorialPrefix already supplies leafQ_pos, prefixQ_pos, productFactorial, sumFactorial and literalPrefixTendsto; Paper9SignedCMPeriod already has actualCMWeightedPeriod and actualLiteralPrefixPeriod. A7 is an existing consumer, not an independent mathematical obligation.

A3c unitSound/sectorSound and diagonalOfCheck/sliceOfCheck already exist; previous complete local GMP residual replay in Paper9ExecutableResidualSymmetricTauJet20261125.md retained (not rerun). ActualCMRoot.shiftedCoeff/complementCoeff/shiftedFactor pay the diagonal; fixed slice needs analogous literal shift and cross-multiplied kappa finite predicate (original scripts/check_cm163_source_bound_jet.py verify already owns exact arithmetic). A4 source-written finite-check root endpoint, native elaboration/evaluation only. A5a/b universalSliceEval, separatedImageInfinite, actualSymmetry already source-written. A5c reverseChartValue/forwardChartValue/productSplit already source-written. A5d centeredJTaylor, seriesTail (iterated dslope), remSub/remMul/remProd/remMonomial and chartAffineAnalytic/jExtAnalytic are existing donors. Do not add generic multivariate Taylor or inverse j infrastructure.

Further A5 reduction: let x=wX, s=S(x)/x² and p=P(x)/x² denote evaluations of exact shifted polynomial complements, N and M normalized two-branch products. R=R_w(0), T=T_w(x(w)) finite telescoping quotient. Existing two scalar equations s X²=N R and p X²=M(R+w X T) imply (N p-M s)X=MN w T near zero when X(0)=A≠0. Thus R cancels before taking any derivative; T need only be continuous at 0 with T(0)=S3. At w=0 obtain 41P2=163S2; first-order coefficient after substitution is A²*(A²*(41P3-326S3)-326*B*S2)/41=0. Local SymPy exact cross-elimination identity PASS this turn; no additional analytic or native proof claim. Remaining actual disk pullback, finite factor/shift attachment and scalar first-order comparison, no derivative of the 40-factor residual. Reuse centeredJTaylor and dslope rather than a new Taylor engine. No Lean/Lake/Agda executable in local container, no manual CI, no full residual replay or performance changes. P0 performance and independent comparator gates remain separately unpaid.


## 25 November — literal shifted slice and actual residual-free cross (SOURCE, UNVERIFIED)

Lean companion research/paper9-original-eisenstein-derivative-20261125:
- 92832a39c08d3c70b886dc99fc6923acdeac2197, Integration/Paper9ScalarCross.lean: fixed-slice binomial shift, exact double-root complement, jetOK/jetFacts (four zeros, nonzero S2, quadratic relation, cross-multiplied signed kappa), actualShiftedProducts, residual-free first derivative and literalPeriodFromDisk.
- a2fb25fc0e8b24346d48c26ccf7b4448f453bb6f, Integration/Paper9ActualCross.lean: actual forty-index restPoly and restSlope, restDifference, chart0CM, sliceIsCMRootPoly via existing actualSymmetry and separatedImageInfinite, sliceShiftIsRest, actualTZero = literal S3, actualRawCross.
- e58728758ac159ebc4ebaf74e4664e3745f9b9aa exposes crossPeriodOfCross so the actual raw identity is consumed without recovering R or its derivative.
- b13398583fad064d267189d63c143eaf24916502 writes normalizedActualCross: cancel only w^4 away from zero, use the literal 41 P2=163 S2 at zero. Preserve the original signed chart indices and all forty residual factors. No inverse j, no new Hecke carrier.

Actual original packet Lean blob 185fbf271b9089afc1ce123d2f53a21f5d89a6df read directly; independent JS BigInt Horner shift (83/43 coefficients) passes all seven jetOK clauses, including exact signed kappa. Fresh local SymPy 10/10 PASS: forward/reverse disk, reciprocal trace, raw normalization, axis/diagonal residual cancellation, N0/N1/M0/M1, cross derivative elimination. Neither check executes Lean. No full GMP/A3c rerun or CI. Lean/Lake/Agda unavailable locally.

Remaining A5 source payment is now the original local upper-half-plane disk pullback and three normalized centered-j germs (X, alpha X(alpha w), alpha^-1 X(alpha^-1 w)), first derivatives of p/s/N/M, and continuity of restSlope along the actual disk; w*T has derivative T(0)=S3. Then instantiate crossPeriodOfCross and literalPeriodFromDisk using the finite A4 endpoint. No derivative of the forty-factor residual and no derivative of T away from zero are required. F5 universal rational cross into original Bishop carrier, native proof acceptance, and independently certified performance remain open. All new Lean declarations are source-written and uncompiled; no endpoint promotion. Original Hecke/CM, Machin, Chudnovsky, Bishop and pinned Mathlib attribution preserved.


## 25 November — ramification and cross-paper reconciliation

See current section in ../papers/drafts/Paper9ExactCMModularJetCertificates.md. Prior elliptic source owners recovered, including proof-relevant original Klein j. Exact independent local SymPy coefficient replay at p=5, K=1728, e=2 gives c=64/25 and signed jet ratio 23/46656; p=7, K=0, e=3 gives c=972/343 and ratio -23/55296. Preserve W=w^e and beta=alpha^e. Both literal double-root and quadratic identities passed. New committed checker scripts/check_paper9_ramified_cm_cross.py reuses original producers, but exact committed script execution remains unpaid. General cross coefficient and quadratic norm identities locally passed. Repair ScalarCross at Lean 794c7dc, raw cross sign ba5e748; Paper9DiskGeometry 6ee19bb source-writes local disk chart and reciprocal maps. Actual analytic germ/continuity and period instantiation, A3c/A4 kernel, F5 same-real and performance gates remain. No CI or promotion. Cross-paper notes placed on this branch, not merged into master or TOE; no new publication dependency.


## 25 November — Hopf refinement donor / exact two-slice non-descent

See Docs/proofs/Paper9TwoSliceIndexedResidualFibre20261125.md. Exact observer section and full symmetric kernel, first invisible quartic, explicit branch cubic collision, minimal transverse repair and orientation-independent quartic consumer. Two exact committed checkers replayed locally and blob-matched. Original chart pair moves under S/T; carry mask and full complement. Reuse diffAt/productDifference to pay restSlope continuity without differentiating residual; A5 actual normalized germs and source attachment remain P0, then A7/F5. Lean raw cross orientation restored at ab9df47 against literal hp/ha/hT sides. No Lean/Agda/Lake, CI, or external promotion. Keep higher-jet acquisition as separate extension; do not widen pi certificate scope.


## 25 November — actual normalized germ and original adjacent-prefix enclosure

See `Docs/proofs/Paper9ActualDiskGermLiteralWindow20261125.md`. Lean Paper9DiskGerm at 37533f04 writes the actual Taylor pullback, three literal reciprocal branches, first derivatives and finite restSlope continuity; literalPrefixFromFiniteChecks composes A4/A5/A7 with eight finite predicates and no free analytic germ premise. Paper9LiteralWindow at 5f405bc4 writes all-index adjacent convex nesting, limit enclosure and rational cross from the period and source root/Machin bounds. Native cross-prover rational source reflection, proof elaboration and actual finite checks remain. Exact local SymPy/Fraction 9 identities, positive gap coefficients, 19 nesting controls, 20 positive prefixes and 513 rational cross/width stages PASS; executed checker byte-matched to commit 40360db. No Lean/Lake/Agda, CI, full CM163 GMP residual replay, or promotion. Higher jets remain independent.


## 26 November — literal signed integer cross and strict floor correspondence

See `Docs/proofs/Paper9LiteralSignedCrossCoordinates20261126.md`. Lean Paper9LiteralCross at fb223368 source-writes actual cutoff/scale/strict Nat.sqrt, original Machin stage/radius (first-omitted-term error and zero-stage exact bracket), raw unreduced stage, positiveView corners and eight-predicate -> forall k, RawCross k. Agda cbce74cc strengthens original floor with strict uniqueness; dba6f148 exposes actual ExpandedCross ↔ SignedCross ↔ Cross and existing native convergence consumer. Source-shaped recurrences and representation order are explicit; no inter-kernel proof transfer or all-index Agda inhabitant yet. Exact local SymPy/Fraction checker 50e009d blob 431b39b6 verified: 129 unreduced stages and 258 expanded inequalities, 1000 signed order/add controls, 1000 strict-floor uniqueness controls, 5 gap coefficients and zero-stage/equality/sign controls PASS. No Lean/Lake/Agda available, no kernel or CI, no full CM163 GMP rerun or performance promotion. Next P0: actual elaboration/finite checks and verified cross-prover proof transport or independent native all-index proof; avoid more observer abstractions or higher-jet scope expansion.


## 26 November — complete finite predicate arithmetic replay

See `Docs/proofs/Paper9EightFinitePredicateReplay20261126.md`. Local exact independent SymPy/Fraction plus GMP Euler recurrence/scatter replay completed in 14.024 s (prior scalar attempt timed out at 90 s during slice). All eight predicate specifications passed: 6646 unit residuals, 3323 independent eta coefficients, 3363+83+83 diagonal and 1723+43+43 slice residuals, strict shift/jet and original Machin/sqrt/180-term exp windows. Full 126 coefficient packet reconstructs original blob 17ed967d; all 126 literal Lean array entries also match. Corrected original expWindowOK and shiftOK namespaces and Machin denominator form. Lean 204c52d2 adds a separate uncompiled native acceptance target with eight `decide` proof terms and `#print axioms universalRawCross`. This is not kernel acceptance; Lean/Lake/Agda absent, direct download DNS unavailable, no CI. Remaining P0 actual elaboration and proof/axiom audit, verified all-index Agda proof transport or independent native proof. No 10M production timing or publication/novelty promotion.


## 26 November — native cofinal cross and exact signed phase/selector donors

See `Docs/proofs/Paper9CofinalCrossGRHPhasePNPSelector20261126.md`. Reopened master, #1529, #1546, #1533, #1548, #1549 and controlling owners. Actual positive-stage Chudnovsky/Machin windows nest by signed convex contraction, strict dyadic floor and increment/radius gap; zero stage explicitly handled. Agda 24443f51 writes actual Cross decider, negative-witness BIDI, crossZero and conditional cofinal restriction; native monotonicity and actual cofinal overlap/common-value proof remain, no all-index inhabitant claimed. SymPy/Fraction 29 edges, 512 root/window, 511 Machin and 513 overlaps, 12 phase layers, 44455 child-count pairs PASS, exact blob 2f426b74. GRH sixth/eighth signed mixed observation kernels and P vs NP strict normalized occupancy contrast equivalent to valid-child selection are scoped donors, not global endpoint solutions. Existing eight finite checks PASS retained; kernels absent. Next P0 verified native analytic common-value or cross-kernel proof, not additional reflection abstractions.


## 26 November — construct the original native Bishop Chudnovsky real

See `Docs/proofs/Paper9NativeBishopRealFactorialNesting20261126.md`. Paper9 lane only. Source-written original strict dyadic floor refinement (f134695f/b11eda74), signed adjacent/two-step nesting (27a1aa23), native factorial P/Q/T normalization (50b55302), literal reciprocal interval ordering/nesting (40ca1e9b/63339925), and actual Bishop `Real.mkℝ` midpoint construction and native doubled-index interval membership (1aa68f16). New direct BIDI: `chudnovskyReal ≃ bishopMachinPi` iff all original `ExpandedCross`; no additional Machin nesting/cofinal premises needed on this route. Actual same-real identity still OPEN; all new source terms uncompiled. Exact local byte-matched checkers 1cb9d08d and 7c78bb66: 2 polynomial identities, 3072 generic floors, 4097 root/windows, 513 factorial identities, 512 signed cross/nesting controls, 4096 window inclusions, 16384 regularity and 16512 paired order controls PASS. Existing 8/8 finite specifications receipt retained. Next P0: actual native analytic common-value attachment or verified proof transport; local kernel acceptance remains separate. No CI, external lane changes, or production performance promotion.


## 26 November — actual native factorial-period product

See `Docs/proofs/Paper9NativeFactorialPeriodProduct20261126.md`. Re-audited master 8d5b3697, #1529 d8956bb9, #1552 6d2260fb, targeted #1478/#1533/#1551/#1250 and actual Lean 204c52d2. Native seriesReal constructed from original signed defect bound and adjacency (9561c014/532fe225); canonical total root wrapper repaired with positive-index correspondence and direct consumer transport (0e99c67e/51b774ff). Synchronized chart k=41n gives actual lower corner times selected high prefix exactly 426880 times canonical floor fraction. Product-limit theorem source-writes `actualProduct : chudnovskyReal * seriesReal ≃ 426880 * sqrtReal` and positive-series cancellation in both directions (5480db8b/d191ca61). Exact remaining native mathematical obligation is `NativePeriod : bishopMachinPi * seriesReal ≃ 426880 * sqrtReal`, equivalent to all-index ExpandedCross. This is NOT proved by actualProduct. Reuse Lean actual signed CM theorem or verified proof transport; native normalized modular/ODE/CM/period reflection remains open. #1552 shell bounds/folds are donors, not a completed period proof. Local byte-matched regression d191927c: 2 symbolic identities, 259 signed defect bounds, 258 inverse budgets, 16384 regularity pairs, 257 synchronized product stages and shifted-product negative controls PASS. No native elaboration, CI, full CM replay or performance promotion. No other research lane edits.


## 26 November — native signed period normalization and literal Euler attachment

Paper 9 only. Reopened the actual #1546 native factorial/product modules, master nonnegative square reflection, #1552 punctured-shell fold at 6d2260fb, and Lean Paper9SignedCMPeriod/Paper9RootODE/Paper9HypergeometricQTransport at 204c52d2. Master search also recovered BishopPowerSeriesElementaryBridgeExact and BishopPowerSeriesDifferentiationSourceTransportExact (source-backed interfaces, not a completed modular identity). Default-branch search for actualCMWeightedPeriod returned no match; the pinned Lean owner was read directly. This is targeted reuse, not an exhaustive branch audit.

New BishopChudnovskySignedPeriodNormalizationExact (e1e8a50b) uses X=E4, Y=E6, E=E2, F=H(z0), J=theta H(z0), r=canonical sqrt(163), p=bishopMachinPi*seriesReal, C=640320^3, D=B-6A=463591680. With X positive, the signed first Euler flow 6YJ=F(EX-Y), original CM relation Y²=(C+1728)/C X³, F²=X, and signed Hecke correction pi*r*(B X E-D Y)=6 B X, the literal weighted sum S=A F+B J gives p*r*Y=B F X. Square only after retaining that signed equation. Cancel X three times using constructive apartness; obtain [163(C+1728)/C]p²=B². Exact constant normalization [163(C+1728)/C]*(426880²*10005)=B², existing Machin >3, positive original S and canonical sqrt positivity, and original nonnegative square reflection yield NativePeriod. No newly constructed ratio root, no foreign real, no unlicensed cancellation. The terminal source is conditional on the displayed native analytic equations, not a proof of them.

BishopChudnovskyNativeFactorialEulerAttachmentExact (99c3f8e0/a8b24fdb/178a80ac) retains the actual signed factorialTerm u_n and n*u_n, finite all-index weighted-prefix split, and original vendored sum/product convergence and uniqueness. periodFromEulerCMRealSlice composes the two literal stream convergence witnesses directly into the terminal normalization; no separate weighted-series identity assumption. At z0=-1728/C, c_n z0^n=u_n for c_n=(6n)!/((3n)!(n!)³ 1728^n); zero term H=1, theta H=0. Exact local checker f89d0581 (blob 84a4016aa854c3c02a3d7537d253c1768e9f5a11 matches executed bytes): 5 symbolic identities, 257 factorial/CM-coordinate/split/bound stages, 256 sign controls, 2 square-sign controls PASS. This is not an all-index convergence or kernel receipt.

Revised native analytic max cut: (i) actual literal H/J convergence and identification with the positive real E4 square-root and Euler jet (reuse existing native geometric majorants, Euler jets and Lean normalized germ uniqueness); (ii) actual CM E4/E6 relation from j(tau0)=-C, on the same native q/lattice object; (iii) actual signed Hecke derivative correction on the same native E2/E4/E6, with source cusp/normalization and finite certificates; (iv) native elaboration, axiom audit and proof transport if choosing the Lean alternative. The arithmetic terminal normalization and weighted combination are now source-written, uncompiled. No CI, native kernel receipt, full CM replay, publication/production performance promotion or edits to other lanes. All classical Chudnovsky/Ramanujan/Machin/CM source attributions retained.


## 26 November — actual native Euler limits, guarded CM cubic BIDI and selected disk

Paper 9 only. Reopened #1546 original factorial/width/period modules and master search for power-series, Ramanujan, CM and q owners. Directly inspected pinned vendor RealProperties/Sequence (viktorcsimma/bishop 240e38c7), including absolute embedding and absolute convergence API. Recovered actual native Klein quotient and real-slice owner, upper-half-plane radius, unit disk completion, existing Machin positivity and the explicit BishopMachinPiLeanSemanticReceiptExact firewall (Lean source theorem does not constitute cross-kernel proof transport). No claim that all historical PRs were exhaustively checked.

BishopChudnovskyNativeEulerLimitsExact (b4ba8fe3): original M^n*abs(P)*(A+B*n)<=A*Q, admissible multiplier k with A*k<=A+B*n, positive A cancellation -> |k*u_n|<=M^-n. Use k=1,n, original signed rational product/weight correspondence and existing native geometric majorant + vendor absolute convergence to construct actual H,J₁ and actualWeightedLimit S≃A H+B J₁, removing convergence hypotheses from terminal consumer. Preserve zero term H=1,J₁=0. Exact local checker dad86a18, executed blob 10dd010f483717d9b4b808af46c45f36a5cc836c: 2 symbolic rearrangements, 257 defect stages, 1028 multiplier cases, 257 weighted splits, 256 sign controls, 3234 finite-tail checks and 2 boundary controls PASS. No finite regression promoted to theorem.

JInvariantBishopCM163RealSlicePeriodExact (f0cef823): on the actual native completed E4/E6 real slice and negative literal Delta witness, clear the original guarded complex reciprocal using multiplyReciprocal and real projection to obtain j*Delta=X³. With C=640320³, actual j=-C iff Y²=(C+1728)/C X³, both directions use the same quotient/apartness witness. periodFromRootAndSignedJet consumes the actual Euler limits and actual native E4/E6, no arbitrary cubic or convergence assumption. Root theorem itself remains unpaid.

JInvariantBishopCM163SelectedDiskExact (a8213fe5): canonical tau=(-1+i sqrt(163))/2, radius=original native machinQRadius(Im tau), q=(-radius,0); prove real slice and exact norm-square radius, obtain Disk.BishopUnitDiskQ via existing strict radius bounds. This constructs actual original E4/E6 q-series at the selected negative-real coordinate with no arbitrary q or convergence premise. This is the selected coordinate construction, NOT yet the proof that the literal original complex q(tau) agrees with it. periodFromSelectedRootAndJet composes guarded root and native Euler limits. Exact local reference checker 764364f6, executed blob d96f7ab39929872635d3fbf9a91d331d0f898a3b: 4 symbolic identities, 257 signed power stages, 128 odd sign controls, 192 guarded quotient cases, 2 boundary controls PASS; test q=-2^-36 is a rational fixture, not the actual CM evaluation.

Revised critical cut on this native route: (1) bind selected q to actual complex exp(2*pi*i*tau), obtain quantitative positivity of X and negative Delta; reuse existing Machin phase, radius and source-bound disk owners; (2) original normalized lattice/q correspondence and actual CM root j=-C (finite integer/jet packets and Lean source are donors, not native proof); (3) actual H²=X and first Euler flow on this same q, including normalized E2 (or equivalent actual derivative expression); (4) signed Hecke jet correction on the same actual forms; (5) native elaboration/axiom audit, or verified Lean proof transport. All new Agda is source-written, uncompiled. No Lean/Lake/Agda executable in local PATH, no CI, no production timing or endpoint promotion. No other research lanes edited.


## 26 November — steelman/BIDI re-audit: exact phase, E4-only period and remaining source cut

Reopened master original K05 and native complex source owners; checked changed-file registers #1546, #1529, #1552, #1478, #580, Lean #104; reopened actual Paper9RootODE, Paper9HypergeometricSeriesODE, Paper9SelectedCMDomain, Paper9CM163CertificateConsumer, Paper9ActualJSourceJet, Paper9SignedCMPeriod and Paper9E2CorrectedClosure on Lean research/paper9-original-eisenstein-derivative-20261125. Relevant historical PR search is not an exhaustive audit of all repository branches. Lean source already writes actualHyperIdentitySelected, actualHyperFirstJetSelected, actualCMWeightedPeriod and actualLiteralPrefixPeriod (the latter two conditional on actual j=-C and signed derivative kappa). Do not list standalone classical hypergeometric ODE, germ continuation or positivity as unwritten Lean sources. All require kernel receipts; none is native proof transport.

JInvariantBishopCM163OriginalPhaseExact (a54b8362): actual complex exponent coordinates -2*pi*Im(tau)-i*pi, source trig parity and original native product, existing two-point Cayley composition and quarter-equality/endpoint theorem. qFromTwoOriginalAtans consumes precisely OriginalAtanFiveCayleyEvaluation and OriginalAtan239CayleyEvaluation to identify the actual original q(tau) with the selected negative-real disk. No general first-positive-zero premise or global period is needed for this consumer. Master already has source product, Pythagoras, addition and rational Cayley targets. Remaining native evaluation: actual exp_C(2i atan_B(t))=(1+it)/(1-it) at t=1/5,1/239, e.g. derivative of denominator-cleared residual with initial value at t=0; original derivative/composition and constructive zero-derivative transport needed. Lean #104 actual arctan Cayley is a donor, not Agda proof.

JInvariantBishopCM163E4JetPeriodExact (7e02757e): U=3*re(actual E4 first Euler coefficient jet), V=B*U+6*A*Y. Actual weighted limit S=A*H+B*J1, Flow=6Y J1=H U, Correction=pi sqrt163 V=6BX. These yield signed Cross=pi S sqrt163 Y=B H X. Reverse given H>0 and Flow. Original E2 formulation transports by U=eX-Y and D0=B-6A. Consume existing native normalizedSquare/squareToNativePeriod, with direct cubic route or guarded literal j root. No independent E2, Y division or new radical. U remains actual coefficient jet, not analytic derivative by definition.

Further exact mathematical reduction (not new kernel theorem): W=2 D Y, d=X^3-Y^2, bracket residual b=Y U-X W-d. For z=1-Y^2/X^3, Dz-z Y/X=Y b/X^4. Thus bracket=0 gives z transport without E2, and differentiating the actual analytic H(z(q))^2=X(q) gives 6Y J1=H U wherever X,H,z transport are defined and H apart. Likewise D^2 j=j(3X^3+3Y^2-YU)/(6X^2) when Dj=-jY/X and bracket=0. With p=pi sqrt163/2, K=-C, signed Taylor kappa=(3X^3+3Y^2-YU)/(6 K Y^2)+X/(2K p Y); U/Y-3X/(pY)=3+3X^3/Y^2-6K kappa. Existing signed finite two-slice kappa and C root imply correction exactly. Original derivative and Hecke source interpretation are still genuine obligations; coefficient jets alone cannot prove them. General E2 analytic system may be retained inside existing Lean hypergeometric proof, but no independent E2 witness at the native terminal.

Guard reduction: strong dyadic enclosure not needed for strict sign. On selected q=-r with 0<r<=1/1024, sigma3(m)<=m^4<=16^(m-1), sigma5(m)<=m^6<=64^(m-1) (m>=1). Absolute tails after first terms <=240*16*r²/(1-16r), 504*64*r²/(1-64r). Therefore 0<X<1<Y, hence Delta<0; 240r/(1-16r)<1, both tail/linear ratios <1. radius <1/1024 follows from pi>3, sqrt163>12, positive exp term (pi sqrt163)^3/6>36³/6>1024, existing negative-exp inverse, positive series monotonicity. Need native comparison/embedding of the exact tails and third positive exp term (reuse existing generic sequence limit order and polynomial-geometric owners). Strong 128-bit actual enclosure separately required for root isolation, not for positivity. H>0 follows from |u_n|<=M^-n and u0=1: H>=1-1/(M-1)>0.

Exact source cut: native phase evaluation and literal normalized lattice/Fourier binding (raw G_k vs normalized E_k factor); actual guard and dyadic interval soundness; actual degree-41 multiplicative norm polynomial Laurent identity, pole removal and exact finite coefficient reflection (not additive Hecke operator); diagonal root isolation via signed factor x²S and half-unit dominance; actual transverse second/third Taylor extraction at selected h(t)=-41/(t+1) with nonzero a and tangent, exact signed kappa; same-object analytic H(z(q)) square/jet transport from existing Lean donors or native proof, plus literal coefficient embedding, actual derivative interpretation and Rankin-Cohen bracket. Native terminal arithmetic, original limit/weighted split, signed cross normalization and universal original rational overlap consumers are source-written. End-to-end elaboration and exact kernel/axiom audit, original executable decimal/termination/cost and performance acceptance remain separate. No claim general CM integrality or inverse-j required. All new Agda uncompiled; local PATH lacks agda/lean/lake, no CI. Local SymPy/Fraction tests in current turn: 6 symbolic signed/residual identities, 256 index majorants, 128 rational guard cases, 5 scalar bounds PASS; mathematical all-index proof still distinct from finite tests. Previous-turn checker execution not independently reverified in this turn. No other lanes edited.


### 2026-11-26 — Full Lean companion branch audit; actual critical cut

A full main-to-research branch comparison (rather than default-branch code search) recovered the existing integrated Paper 9 chain. The Lean companion at 310a87a276b2526b159d1e9fe187680d6bb41371 already contains Integration/Paper9NativeFiniteAcceptance.lean (blob 0ac6f767061978b961280af35d41110eb6b272b0), with source-written universalRawCross : ∀ k, RawCross k. **This is not a kernel acceptance claim.** Three overlapping audit-time modules were removed; retain the original owners.

* Paper9CyclotomicPacketReflection, Paper9IntegerSectorWeld, Paper9ConcreteSectorConsumer, Paper9FiniteResidualCheck, Paper9ExecutableCM163: actual primitive phase filter, contract/expand, exact integer recurrence residuals and literal sector consumers. Do not reimplement the 83/43 coefficient extraction.
* Paper9CM163LiteralPacket, Paper9ActualCMRoot, Paper9CMShiftCheck, Paper9CMExpWindow: literal integer packet, shifted dominance, dyadic root and enclosure construction.
* Paper9UniversalMonicSlice, Paper9SeparatedCusp, Paper9ActualCross, Paper9DiskGeometry, Paper9DiskGerm, Paper9ScalarCross: actual symmetric slice and reciprocal Möbius branches, common forty-factor elimination, central cubic correction. The normalized disk coordinate retains the center; it does not invert j. DiskGerm.literalPrefixFromFiniteChecks supplies the period via the eight checks.
* Paper9LiteralCross.rawCrossFromFiniteChecks and Paper9NativeFiniteAcceptance.universalRawCross: existing universal source endpoint. The latter has eight source-written by-decide gates (unit, diagonal, shift, slice, jet, pi, sqrt, exp) and #print axioms. The companion pins Lean v4.28.0 and Mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365. Build the explicit Integration.Paper9NativeFiniteAcceptance target locally before claiming proof acceptance; no CI and no unchecked Boolean import.

Exact replay in this audit: the 126 literal signed coefficients in the Agda JSON (blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4) match the Lean arrays (blob 185fbf271b9089afc1ce123d2f53a21f5d89a6df); 14 integer scalar checks on the original packet passed, including dominance and signed kappa cross multiplication. Local SymPy: 2 direct Taylor identities, 3363 sector index/divisibility checks, 8 independent resultant/norm recurrence fixtures. These are finite external checks, not Lean or Agda acceptance, nor a complete 3363-coefficient replay.

Agda signed-coordinate BIDI: commit 90aaab8f8870f8b74fe36af18c070345047ae79e adds expandedTransport, expandedTransportBack and the two equivalent-coordinate cross directions to BishopChudnovskySignedCrossReflectionExact. It retains both signed cross inequalities and requires rational setoid equality of all four coordinates. No raw denominator identity is assumed; source remains uncompiled.

Remaining critical cut: (1) elaborate the existing Lean dependency chain and kernel-check all eight finite decisions and universalRawCross, audit axioms; (2) prove the four all-index actual raw-to-Agda coordinate equalities (lower/upper window, Machin stage, radius), including cutoff/root scale/positive denominator and sorted corner agreement; (3) provide a sound native Agda proof of the universal signed comparison or verified proof transport, not a hash or asserted Lean theorem; (4) kernel-check the existing ExpandedCross -> NativePeriod -> actual convergence consumers and BIDI reverse. Production and performance claims remain separate. Do not reopen the classical CM polynomial, Taylor, discriminant guard or period proof as unwritten Lean tasks.


### 2026-11-26 — Actual native raw-coordinate BIDI (source-written, uncompiled)

The all-index **Agda coordinate correspondence** now has explicit source declarations in `DASHI/Foundations/BishopChudnovskyRawCoordinateWeldExact.agda` at 52a7f4f589630c6374322cf59d95c558c43bec62 (blob 8e4140da0854208d7e7c5167817e613f27d365da).

- Reuse `IndexedEdgeAlgebraExact`, `PositiveGapExact`, `PairedTotalityExact`, `WidthReflectionExact.sourceView/sourceDen`, `PrefixSemanticsExact.fracWeight/fracMulEdge`, `MachinCrossEnvelopeBishopOrderExact.rationalReciprocalPower`, `FiniteNatFloorSquareRootExact.floorSquareRootUnique`, and `SignedCrossReflectionExact`. No separate real, square-root, or split-prefix implementation.
- `signCorrect`, `oddIndex`, `unsignedCorrect`, `weightedCorrect`, `rawTermNum/Den`, `termCorrect`, `stageCorrect`, `stageNumStep`, `stageDenNatStep`, `stageZeroNum/Den` bind the source-shaped signed Machin term and exact unreduced recurrence. `rawRadius`, `radiusCorrect`, and its projections preserve stage zero (22,7) and positive stages (4,25^k).
- `rawViewCorrect`, `rawViewNum/Den`, `cornerNum/Den`, `sortLeft/Right`, `windowCorrect`, `rootTargetShape`, `rootStrict`, `rootUnique` attach the same original positive T, Q, cutoff, root and ordered corner. The raw-window constructor deliberately reuses CH.orderedInterval, including equality/tie; this is not a second evaluator.
- `lowerCorrect/upperCorrect/stageCorrect/radiusCorrect` supply the four concrete native rational equivalences to `expandedCrossFromEquivalentCoordinates` and its reverse. `toExpanded/fromExpanded` and `periodFromRaw/rawFromPeriod` connect the concrete Agda RawCross family with the original NativePeriod. The native RawCross predicate is the exact two signed cross-multiplied integer inequalities. This is a source-level specification correspondence with Lean Paper9LiteralCross.RawCross; no cross-kernel equality/proof receipt is asserted.
- Local bounded independent integer/SymPy replay, `scripts/check_paper9_raw_coordinate_weld.py` (commit 5a6bc0c02ed89ba278993cdb4b32c92e62faedb8, blob e8670656acf1eae43ccbc73354c9b7f007cef380 matches executed bytes): 3 symbolic identities; 257/257 raw term, stage, prefix, root and window coordinate cases at k=0..256; 514/514 signed comparisons; 6/6 equality, negative, zero and failure controls. Checkpointed and timeout 90s; not native kernel checking or all-index evidence.

**Remaining cut:** The Lean companion at 310a87a276b2526b159d1e9fe187680d6bb41371 is unchanged; `Paper9NativeFiniteAcceptance.universalRawCross` is source-written with eight by-decide gates, not locally compiled. No Lean/Lake/Agda/Nix/Elan binary was found. The Agda coordinate declarations are also uncompiled; repair any elaboration/API defects before claiming they type-check. The remaining universal witness is precisely `(k : Nat) → BishopChudnovskyRawCoordinateWeldExact.RawCross k`, or a native proof of `NativePeriod` via the existing analytic route. A verified theorem/proof translation must supply a native Agda inhabitant; a Lean theorem receipt, hash, external checker PASS or finite decidability does not. Rechecked master `tools/agda_preflight/agda_preflight/external_proof_bridge.py` and `DASHI/Interop/LeanMoonshineEisensteinAnalyticParityExact.agda`: routing/evidence-only and explicit no automatic proof transport. PR #1552 provides shell/even-power majorants, not a universal cross proof. Do not manufacture an import or assume a generic cross-prover translator.

The independent native analytic route already has `JInvariantBishopCM163OriginalPhaseExact.qFromTwoOriginalAtans`, `JInvariantBishopCM163E4JetPeriodExact.periodFromRootAndE4Jet`, and the actual Hecke row-lattice donor. Its remaining inputs are the original phase evaluations (where needed to identify actual q), X positivity, negative discriminant/actual CM root (or direct cubic), H^2=X, actual Euler Flow and signed Correction. Source-written Lean proves the analogous classical chain; native Agda derivation or verified proof transport remains to be discharged. No change to production/performance gates or other lanes.


### 2026-11-26 — Native selected CM guards and signed jet reduction

See [native guard/jet ledger](../proofs/Paper9NativeCM163GuardJetReduction20261126.md). New source: JInvariantBishopCM163RadiusGuardExact (2a7543cc), TailGuardExact (80b87923), NativeJetReductionExact (b24e9f5c). Actual native radius 0<r<1/1024 from original pi_M>=3, sqrt163>=12 and positive cubic exponential term >=7776. The signed majorant telescope retains the first negative term and current residual m_n/15, yielding 3/4<=X<1<Y and actual Delta<0, so a native guarded Root is constructed. Source-written, UNCOMPILED. No need to list positive X, positive Y, negative Delta or coarse radius as independently unwritten producers; acceptance/repair remains.

The actual bracket and z-flow are BIDI after positive Y cancellation; under H^2=X the cleared hyperjet is BIDI with the original Euler Flow without an H positivity hypothesis. Original signed kappa scalar normalization and correction now have both directions; the cleared q-jet relations feed SignedJet and periodFromThree/rawFromThree. Remaining native producers are exactly CMRoot, HyperSquare, ClearedHyperJet and SignedJet (original signed q/disk jet interpretation). All remain genuine analytic obligations, not arbitrary replacements. Existing classical Lean chain is unchanged and uncompiled. Actual phase, lattice normalization, degree-41 norm, finite packet/dyadic root isolation, native H-square/derivative and signed disk identity are constituent leaves of these four obligations. Local exact replay PASS 6 symbolic, 514 growth, 66 radius/weight and 4290 signed stages, 6 scalar/boundary controls; script 04befd73 blob 666bfe130c5300c3c673652e768df1c39ca2878f matches executed bytes. No CI, no proof import, no performance claim.


### 2026-11-26 — Native hypergeometric formal-cusp maximum cut

See [native hypergeometric coefficient ledger](../proofs/Paper9NativeHyperODECoefficientUniqueness20261126.md). NativeHyperODEExact fba05f26: original signed all-index factorial recurrence, all Euler-order limits and actual J3 ODE at z0. HyperQCoefficientUniquenessExact f5aebd85: literal cleared third-order q-ODE P3..P0, constants (72,0,0,0), triangular prefix uniqueness with diagonal 72 n^3, finite Cauchy Euler Leibniz and differentiated square. HyperQOriginalCoefficientsExact c34a220b: literal finite geometric inverse, binomial square-root, hypergeometric and Euler composition candidates; zero-mode support, unweighted ODE from signed source, CM term attachments, conditional formalHyperSquare/Jet. RadiusGuard 2f7b8f85 and TailGuard 64636ec1 strengthen r<1/7000 and original absolute tails l1X<1/25,l1Y<2/25. Intended absolute composition budget 1517/4608<1/3; weighted Cauchy evaluation remains open. Exact local checker ba8da357 (blob 9cbd3fdb82b050d9172e865c2b9040be8403e6d5) matches executed bytes: 3 symbolic, 257 source recurrences, 33 degrees of independent constructions/ODE/jet/Ramanujan, 32 first-change controls, 33 literal compositions/Leibniz/flow, 3 exact composition budget controls. All source UNCOMPILED; no CI or kernel acceptance.

Do not list native factorial ODE, normalized formal coefficient uniqueness, finite Euler product rule, or literal candidate construction as unwritten. Actual remaining leaves: Cauchy ring/reindexing and inverse/binomial square; three original divisor convolution identities (explicit in ledger); actual formal root and hyper composition ODE satisfaction; absolute evaluation at actual negative q with original factorial and Eisenstein/jet attachments. Those pay HyperSquare/ClearedHyperJet together without classical analytic identity theorem. CMRoot and SignedJet still genuine separate producers. Preserve zero mode, sign, and kernel acceptance boundaries.


### 2026-11-26 — Reconciled finite divisor shears and recovered Cauchy product (supersedes previous outstanding inventory)

[Exact max-cut ledger](../proofs/Paper9DivisorShearAndRecoveredCauchyMaxCut20261126.md). Historical #1529 already owns hypergeometric mathematics; Lean companion already source-writes the actual analytic endpoint chain. #1552 fe44b21d supplies weight4/6 reciprocal shell bounds and finite shell domination (not final normalized lattice/Fourier equality). #1353 and master supply positive and signed Cauchy triangle convergence, already specialized for native complex exp. Do not list generic absolute triangle convergence or the mathematical hypergeometric ODE as unwritten.

R1: The ordinary all-index Ramanujan divisor-convolution proof is now reduced to two reversible positive-lattice shears on ax+by=n, with equality boundary preserved. Four weights Q=a^2-ab+b^2, Q^2, Q^3, a^2b^2(a-b)^2 give all three identities (plus 120S33=sigma7-sigma3) by boundary regrouping and polynomial antidifferences. Native source FiniteDivisorConvolutionShearExact e3ad497c implements grade/positivity/inverse laws, four polynomial differences/symmetries, all four scaled boundary prefix and closed endpoint proofs. Remaining native finite weld: exact unique enumeration permutation on each grade and grouping by ax, a+b, a using already-owned OneTo, FinitePositiveFactorPair, FiniteDivisorPowerSum, FiniteWeightedReindex. No native modularity/dimension theorem needed for the Ramanujan coefficient lane. R2: BishopAbsoluteCauchyProductSpecializationExact c8e73521 attaches existing positive/signed Cauchy triangles, productAbsolute, normSubmultiplicative, productConverges on actual real coefficient streams. Weighted per-row evaluation, formal ring/reciprocal/binomial/power identities, actual formal ODE satisfaction and finite-to-infinite composition interchange remain. Existing normalized uniqueness, actual coefficient recurrence, Euler Leibniz, zero-mode support, original factorial limit transport and absolute scalar budget retained. Then HyperSquare and ClearedHyperJet follow jointly.

C0 original phase two atan-Cayley actual evaluations; C1 #1552 shell convergence/reindex/normalization and same-object Fourier attachment; C2 actual 42-chart degree41 diagonal/slice norm reflection plus original narrow root isolation; C3 actual first/second q jets and reciprocal disk normalized cross -> signedFromDiskJet. Reuse the precise native and Lean constructors named in the ledger, not new generic interfaces. No general class-number-one proof necessary on degree41 route. Terminal periodFromThree/rawFromThree and rawFromPeriod/periodFromRaw already source-written. Lean direct universalRawCross is source-written and needs exact-head kernel/axiom acceptance; no automatic Agda transfer.

Local exact replay 608f5040 (blob 697f197fa6f3d9e5eda02e736f9e74d48aaf1e7f matches executed bytes): 26 symbolic grade/weight/boundary identities, 128 grades, 165146 positive lattice points, both shear directions, 512 boundary and 512 convolution identities PASS, SymPy 1.14.0. All new Agda source UNCOMPILED, no CI/kernel promotion. Ordinary all-index proof uses the bijections, not finite replay.


### 2026-11-26 — Original finite geometry weld consolidation (supersedes H1/H2/H4 finite inventory)
[Exact ledger](../proofs/Paper9FiniteGeometryWeldConsolidation20261126.md). Rechecked #1546/#1529/#1552/#1353, master, Lean companion. #1546 currently nonmergeable; retain original branch, reconcile before merge. Existing signed twist, Fin-sum, original imaginary exp-product and prior K04d/K05/Koenigs composition proofs recovered; H4 and C0 share one composition weld.

Source-written, uncompiled: original Cauchy ring reflection/simplex induction (5af44a56); general weighted Cauchy evaluation and absolute convergence (32cb4f0e); actual positive grade enumeration plus both strict chart list permutations (e49a4b9c); balanced signed boundary folds boundary1..4 (b5cf531b); literal finite composition exchange by zero padding and rectangular Fin-sum exchange (7a82ab03). No new carrier. H1 remaining: group original folds by i=ax and equality strata a=b/x=y using FinitePositiveFactorPair and existing unique proof-free key permutations; boundaryClosed1..4 already available; eliminate sigma7 and attach literal signed Ramanujan coefficients. H2 remaining: inverse/binomial square, finite power/compose algebra; generic row mechanics no longer unwritten. H3: actual formal ODE satisfaction and Euler chain. H4: finite composition exchange already source-written; use two-cut tail estimate in ledger, actual weighted power norm/limit induction and geometric/polynomial outer majorants, not a new general infinite rearrangement theorem. C0 complex extension uses existing original complex product/factorial owners; C1 lattice Fourier normalization/reindex, C2/C3 actual degree41 norm/root and signed disk residual jointly, as prior ledger. Lean universalRawCross is already source-written from eight by-decide predicates; kernel acceptance separate. Terminal consumers remain unchanged.

Local exact replay: 8712 row equalities including q=0, symbolic simplex regrouping, 25 actual box-filter grades, 2377 points, 100 signed boundary balances, 456 weighted composition prefix exchanges PASS. Checker 1801fb23, blob 42a6157994920c4fe809e7fabba01cecbbec92f9 matches local bytes. Previous shear checker also replayed successfully. No Agda/Lean kernel available; no CI; all new native source uncompiled.


### 2026-11-26 — Right-factor signed defect max-cut (supersedes auxiliary binomial-root lane)

[Exact right-factor ledger](../proofs/Paper9HyperQRightFactorDefectMaxCut20261126.md). Rechecked current #1546 starting d12e87b7, #1529/#1552/#1551/#1533/#1353, master and Lean companion. At starting HEAD #1546 reported mergeable. Actual original P3..P0 operator factors as (Q2 D^2+Q1 D+Q0)∘(2X D-DX), with Q2=36X^2Y^2, Q1=-36XY^2(EX-Y), Q0=(15/2)Y^2((EX-Y)^2-(X^3-Y^2)). Ramanujan derivation and four exact coefficient comparisons in ledger. For any actual normalized Solution F the signed defect S=2X DF-(DX)F has zero mode and leading diagonal 36n^2; S=0 by induction. G=F^2-X has zero mode and X DG-(DX)G=F S=0, leading diagonal n, hence G=0. Thus only actual Factorization and Solution of hyperCandidate required; no separate rootCandidate ODE, binomial square or second normalized candidate necessary. Existing root route retained independently.

New source-written uncompiled: scalar factor/derivative polynomial proofs a290d23f; original Euler defect prefix uniqueness 4860b62d; actual Q2/Q1/Q0/zero-mode and defect-to-square consumer 89d9c6f2 (explicit Factorization input not yet inhabited); generic divisor weight readout 650b6237. H1 remaining actual omega/grade and equality-stratum grouping into existing positivePowerReadout, boundaryClosed1..4 and literal Ramanujan coefficients. H2 remaining formal power/inverse/compose chain only. H3 remaining actual repeated Euler/product rule and formal ring interpretation of four scalar factor comparisons plus hyperCandidate Solution from existing unweighted recurrence and chain. H4 actual weighted power norms and two-cut evaluation, same-object CM argument and factorial/jet binding. C0–C3 and terminal remain as previous ledger, C2/C3 jointly share degree41 polynomial. Lean independent universalRawCross source unchanged, kernel acceptance separate.

Local exact replay 2c35cdcc, blob c99dc7e15372f994b5449b28116f33bb4493dba3 matches local bytes: 8 symbolic factor/derivative/cusp controls, 41 degrees actual q-coefficients, 82 signed impulses and 3362 coefficient comparisons PASS. No Agda/Lean executable on PATH; no CI, no kernel acceptance or native endpoint promotion.


### 2026-11-26 — Literal formal hypergeometric producer max-cut

[Exact source and remaining-weld ledger](../proofs/Paper9LiteralFormalHyperProducerMaxCut20261126.md). Rechecked #1546 starting 380233dc, #1552/#1529/#1551/#1533/#1353, master and unchanged Lean companion. Recovered vendored Bishop NonReflective rational coefficient solver and existing constructive ring adapter pattern. No axiomatic real adapter. Source-written original formal Cauchy ring and rational embedding c6dd70dd; actual Ramanujan-to-operator factorization c74e5253/97345a25; literal geometric inverse e36770fc; actual Z denominator and flow b5e74ce3; finite composition chain 2b4bf248; actual factorial recurrence 66d5fbef; denominator jet assembly and original hyperSolution, hyperSquare, hyperClearedJet 81238964/5081704e. H2/H3 conditional producer chain now source-written with ONLY literal RamanujanX/Y/E as mathematical inputs, no binomial root or independent factorization/ODE premise. No kernel acceptance.

H1 remaining actual grouping of signed shear folds into original positive factor-pair power readout and equality boundaries x=y, a=b, with existing unique membership permutations, boundaryClosed1..4, eliminate sigma7 and transport to literal RamanujanX/Y/E. H4 still actual weighted power norms and two-cut evaluation of original coefficient streams and original factorial/jet limits at CM coordinate. C0–C3 unchanged: original atan–Cayley where required, actual normalized lattice/Fourier equality, joint degree41 norm/root and signed transverse jet. Terminal consumers unchanged. Lean independent universalRawCross acceptance target unchanged. No native original-period promotion. Local exact SymPy 1.14.0: 4 symbolic factor/defect identities (fed6547b; blob 1d79f0b397486cd79631548c7db3f79e8712cbd6), symbolic denominator jet, 600 signed coefficient equalities, 25 original q-degrees through full chain (bd12a153; blob a2902d5114309675a14afd8f429824eb5f5bdc13), exact local/remote blob match. All seven new source modules static balance/no explicit holes or postulates; this is not parser/type/kernel checking. No Agda/Lean executable, no CI. PR reported nonmergeable at bd12a153 after mergeable starting head; recheck before merge.


### 2026-11-26 — Weighted powers and actual two-cut composition

[Full max-cut ledger](../proofs/Paper9WeightedTwoCutCompositionMaxCut20261126.md). Starting d349fbfe: previous formal producer, exact replay and roadmap already committed. Rechecked current #1552/#1529/#1551/#1533/#1353 and targeted master comparison. New source-written uncompiled: weightedPowerLimit 2dfd4c32; constructive two-cut diagonal modulus 694d2781; actual composition absolute/signed convergence and norm bound 9a8da43e/f477b107; selected CM formal evaluation consumer 3b246e8e uses original factorial H/J1 and original X/Y/3DX evaluations, consumes existing terminal rawFromThree. Neither the generic weighted-power induction nor generic two-cut interchange remains an unwritten native source obligation. Actual producer inputs remain explicit.

Direct CM norm budget suffices: a=1/25,b=2/25, T=(1+a)^3-1=1951/15625, disc norm<=4551/15625, inverse norm<=1/(1-T), hence Z norm<=1517/4558<1/3. No need to separately construct inverseX cubed; previous sharper 1517/4608 is distinct. H4 remaining: literal real-slice E4/E6/3DX coefficient binding and tail norms; actual inverse/majorant construction and Z evaluation from CMRoot; literal factorial ratio bound and summability of hyper/jet majorants. H1 original factor/strata readout and actual Ramanujan remain. C0 complex specialization (not automatically paid by real proof), C1 normalized lattice/Fourier equality, joint C2/C3 degree41 norm/root/jet, kernel and axiom audit. Local timeout 90s exact replay 8ebc43a6 blob 7ea41251cdd41807e5490b996cb9a0d764c30b71: 5640 signed rational controls, CM budget and 256 ratio checks PASS. Four source modules lexical balance/no explicit holes checked only. No Agda/Lean/lake, no CI, #1546 currently nonmergeable.


### 2026-11-26 — Literal CM evaluation and positive factor charts

[Max-cut ledger](../proofs/Paper9LiteralCMBudgetAndFactorChartsMaxCut20261126.md). Starting 4bb6a57a verified; targeted master and #1552/#1529/#1551/#1533/#1353 rechecked. Source-written uncompiled: original real-slice coefficient/head/jet and tail norm binding 974545d3; actual weighted norm arithmetic and inner/disc witnesses 5edf8d19; literal geometric inverse and root-to-Z evaluation 5e06f585; actual factorial coefficient band and hyper/jet majorants 640e3117. AtRoot.rawFromArithmeticAndCM now has only original CMRoot (module parameter), literal RamanujanX/Y/E, SignedJet and index k as inputs, not external H4 convergence/norm/evaluation premises. H2/H3/H4 conditional path source-written, kernel/type/termination audit outstanding. H1 positive product grade/strict complement, original factor-pair coordinate completeness, reverse interior and equality-stratum forward charts 6dc1f5ed. Remaining H1 actual reverse equality-stratum list maps, proof-free grade/strata permutations, sigma/boundary folds and literal Ramanujan equations. C0–C3 original phase/lattice Fourier/degree41 root and jet still open. Local timeout 90s checker b781110d, blob 158bea928d9ceb95b829e6a285b2ea4c6296b9e8 matches local: 5 signed radii x 25 degrees, 256 coefficient steps, 4 conditional root-to-Z, 80 grades/51926 points PASS. Five new files lexical balance/no explicit holes only; no Agda/Lean/lake or CI. PR reports nonmergeable.


### 2026-11-27 — Terminal-first disposition (controls earlier open-lane inventories)

Reconciled Agda HEAD c8d9f7a8ad1d with the Lean companion research/paper9-original-eisenstein-derivative-20261125, Integration/Paper9NativeFiniteAcceptance.lean (blob 0ac6f767061978b961280af35d41110eb6b272b0). PR #1546 nonmergeable at inspection. The eight predicate specifications already passed the exact independent replay recorded in [the eight-predicate ledger](../proofs/Paper9EightFinitePredicateReplay20261126.md); do not reopen their arithmetic as unwritten. The actual eight Lean by-decide declarations and universalRawCross composition exist, but elaboration, kernel reduction and axiom audit remain unverified. No new acceptance claimed in this entry.

| Lane | Disposition | Completion gate |
|---|---|---|
| Lean terminal | Source-written | Check entire import closure, eight named decisions, universalRawCross and axioms |
| H1 | Lean donor reported; native finite grouping incomplete | Literal all-index Ramanujan equations via existing grade/equality strata folds |
| H2–H4 | Conditional native source-written | Typecheck and inhabit existing producer inputs |
| C0 | Existing Cayley/phase machinery | Actual analytic attachment where required |
| C1 | Existing lattice convergence/reindex machinery | Exact same-object normalization/Fourier attachment if on terminal dependency path |
| C2–C3 | Lean root producer and signed disk jet source-written per companion reconciliation | Verify closure and attach same original root/germ/jet in native route |
| Native cross | Existing RawCross/ExpandedCross/NativePeriod transport | Inhabit all-index source witness constructively; no cross-kernel assumption |
| Production | Existing GMP implementation and historical independent replay | Exact committed-source build, certified enclosure and matched performance gates |
| Integration | Open | Manuscript synchronized, merge conflicts reconciled, audit recorded |

P0 execution: (A) terminal Lean acceptance first; repair only demonstrated failures using verified reflection/chunked integer reductions, never an externally asserted Boolean. (B) reverse-solve the native rawFromArithmeticAndCM/periodFromRaw inputs using existing donors, preserving zero mode, signed residual, branch and coefficient indices. (C) attach accepted endpoint to existing GMP certificate path and run exact-source harness. Keep local bounded execution (90 seconds per attempt), checkpoint raw receipts; no GitHub CI. Distinguish source-written, replayed, kernel-accepted and production-accepted. No generic CM/jet/Cayley/Fourier/hypergeometric rebuild absent a demonstrated terminal dependency. This entry updates disposition only, not a claim of new mathematical or kernel closure.


### 2026-11-27 — Native H1 equality-stratum chart and fold transport

Starting HEAD 84cf583f30d9, #1546 reported mergeable at start. Native reverse equality maps in FiniteDivisorConvolutionFactorChartExact at 39d5089626b2: strict split positivity and sum, fromXY/fromAB, grade/omega membership, recoverXY/recoverAB and divisor/quotient readbacks. FiniteDivisorConvolutionEqualityPermutationExact a08e4a8cda39 adds proof-free factor-key projection freshness using the ORIGINAL positive factor-pair scan, two strict split key lists, duplicate freedom, both directions of membership, xyPermutation/abPermutation and signed xyFold/abFold transport to the existing omega equality filters. The two boundaries are separate observations of the same original grade; their intersection is not deleted. No new divisibility scanner or cross-kernel axiom.

Exact local replay scripts/check_paper9_equality_strata.py b472659c8831, blob 966f12d42c6998098e1ce565d01a619af7cfdd0f (executed local bytes match GitHub blob): SymPy 1.14.0, 4 symbolic boundary sums, 128 grades, 165146 original lattice points, 12890 XY and 12890 AB equality points, 280 double-diagonal points, both roundtrips and 1024 boundary folds PASS, 90s timeout. This is executable arithmetic acceptance, not Agda elaboration.

H1 reverse coordinate maps and equality-list permutation/fold transport are now SOURCE-WRITTEN, UNCOMPILED. Do not list them as unwritten. Remaining H1 native attachment: regroup each key list by factor pair and strict split into boundaryClosed1..4; group the interior omega fold by i=ax and read out sigma powers via positivePowerReadout; eliminate sigma7 and attach the three literal Ramanujan coefficient equations (including zero mode). H2–H4 conditional source, C0–C3 same-object native analytic attachments, Lean kernel acceptance, original native RawCross family and production GMP endpoint integration remain unpromoted. No CI, no formal kernel run. Preserve original classical authors and existing DASHI donor owners; this change supplies only native finite-coordinate and list-fold attachment source.


### 2026-11-27 — RawCross direct signed real-ray disk / half-unit root cut

Reverse-traversed actual RawCoordinateWeld, NativePeriodProduct, NativeJetReduction, TailGuard, WindowNesting, and Lean companion Paper9ActualCMRoot, CMShiftCheck, ActualDeltaWindow, CMExpWindow, ScalarCross, ActualCross, DiskGerm, LiteralCross. WindowNesting already has windowNests/windowLowerMono/windowUpperAnti; do not list Chudnovsky window nesting as missing. Cofinality alone does not prove intersections. Lean terminal remains source-written/uncompiled. No proof import.

New native source (UNCOMPILED): JInvariantBishopCM163DiskCrossCoefficientExact 3ca7872e98b4 / 148992bbb554, literal reciprocal disk first coefficient with zero mode, packetP2/packetP3/packetResidual, factor, constructive apartness cancellation, diskShape, actual pPositive, signedJetFromLiteral consumes existing FirstQJet/SecondQJet and signedFromDiskJet. For p=pi_M sqrt(163), a=Dj,b=D²j, real disk ray log(q/q0)=-2pw/(1-w), A=-2pa,B=-2pa+2p²b. The original first coefficient of (N P-M S) X²-N M X (w T) factors after original packet equations as (163/41) A³ S2 (kappa A²-2B). Thus S3 cancels; no derivative of the forty-factor residual. Keep A/S2 apartness, actual ray germ and original Hecke product identity explicit. No analytic producer claimed.

JInvariantBishopCM163HalfUnitIsolationExact 27e49099aaa1 adds actual guarded-j offset, ascending Horner tail and abs majorant by induction, signed negative complement, cancellation and existing squareZeroReflectsSetoidZero, rootFromShiftedDiagonal. Native C2 root elimination no longer unwritten. Exact packet blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4 fetched and independently replayed with integer Horner shift (connector JS BigInt): 83+43 coefficient slots, both double zeros, P2<0 and S2<0 (4629 bits for |S2|), 41P2=163S2, signed kappa cross, and 80-term dominance. Tail/|P2| < 152/10^18. This is integer replay, not native proof terms for the packet or actual root identity.

Local SymPy 1.14.0 timeout90, scripts/check_paper9_disk_cross_coefficient.py 8e433dcc7f55 blob 1f53a83c9cd0678538e9189d2a450a059389575d matches executed bytes: 8 symbolic identities, 144 signed reverse-solved cases, 144 perturbed cases, 2 degenerate controls PASS. scripts/check_paper9_half_unit_isolation.py ace82b94cf613 blob 54b2370d3836ec5d0dde4147e33cff43b5099704 matches executed bytes: 1 symbolic factorization, 387 signed rational sample controls PASS; optional original-packet Python mode not run locally, actual packet checked by separate connector integer calculation above. No CI or kernel acceptance.

Remaining native direct cut: (1) actual original phase/normalized lattice/Fourier and degree41 diagonal/slice polynomial identities (not simply copying Lean statements); actual narrow CM half-unit enclosure and literal shifted packet interpretation to inhabit rootFromShiftedDiagonal; (2) actual first/second q derivatives and reciprocal disk normalized first-coefficient identity on real ray, A/S2 apartness and literal packet equality reflection to inhabit signedJetFromLiteral. (3) H1 native final divisor folds and Ramanujan producer, H2–H4 conditional source already present. Feed same original root and signed jet to rawFromArithmeticAndCM and existing periodFromRaw; no new terminal carrier. Lean eight predicate independent replay already paid; kernel closure separately unverified. Production GMP endpoint acceptance remains. PR #1546 reported nonmergeable at 148992bbb554. No unconditional RawCross/native period claim. Preserve classical CM/Hecke/Chudnovsky/Machin/Bishop attribution and existing DASHI/Lean owner provenance.


### 2026-11-27 — RawCross literal packet and degree-41 generator transport

Native finite premises advanced (SOURCE-WRITTEN, UNCOMPILED): JInvariantBishopCM163LiteralPacketExact cc3264c3d512 binds the actual 83+43 descending signed coefficients, denominator 1, original JSON blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4; native blob eb41e2c937d89dfb8cf2f90d1f31e69b945ad5e0. Read-back exact integer comparison 126/126, all 10 signed shift/dominance predicates passed via independent BigInt Horner computation. Both double zeros, negative P2/S2, 41P2=163S2, signed kappa equation, strict dominance and ratio <152/10^18. JInvariantBishopCM163LiteralPacketShiftExact 3e4a6911f4b7 and 5c1b2275e256 gives structural Horner translation of original packet by K, rational closed cross equality and order proof terms, doubleZero, rootFromLiteralDiagonal, signedJetFromPacket, and signedJetFromActualFirst. FirstQJet entails a>0 using X,Y positivity and negative K, hence A=-2pa<0; S2<0 from literal packet. Finite native proof terms still require elaboration and kernel computation; connector exact replay does not replace them.

CM163ClassicalHecke41GeneratorTransportExact 50c1b84cdafa reuses original lattice rows and SL2Z carrier, all 42 S/T correction edges, determinant and inverse-index tables, explicit CM branch matrices [[0,-41],[1,1]] and [[-1,-41],[1,0]], both products -41 I. No new j or assumption of analytic modular invariance. Original Lean donor Paper9Hecke41ChartGeometry and Paper9MobiusDiskPeriod inspected; analytic normalization, lattice/Fourier identification and actual product identity still unpaid on native carrier. Local SymPy 1.14.0 scripts/check_paper9_packet_shift_chart.py 251a86e018f2 blob 734ed2d84f88926c23ea7effba7a6d90d84cf082 matches executed bytes: 336 finite chart assertions, six CM matrix/trace identities, twelve symbolic Horner identities PASS. No CI; no local Lean/Agda executables. No kernel acceptance.

Next shared producer: actual normalized degree-41 Hecke diagonal/slice polynomial identities via existing analytic lattice/Fourier/phase, Laurent pole-removal and sector reflection donors; actual narrow CM half-unit enclosure; actual first and second q jets and original real-ray coefficient residual. Feed rootFromLiteralDiagonal and signedJetFromActualFirst to existing rawFromArithmeticAndCM (H1 final Ramanujan folds still open). Do not reopen literal packet arithmetic or introduce substitute analytic inputs. Native universal RawCross, production endpoint integration and PR mergeability remain open. Preserve classical Hecke/CM/Chudnovsky/Machin/Bishop attribution and Lean/native donor provenance.


### 2026-11-27 — Signed interior cancellation

Source-written, uncompiled: `FiniteDivisorConvolutionInteriorFoldExact` (0513d86bf3cd) distributes the two observations over the original omega list, cancels their common integer baseline and transports both equality folds through the existing xy/ab permutations. The double diagonal is retained in both observations. No new postulate or finite-check premise. Remaining: regroup keys into the existing boundaryClosed1..4, interior factor-pair power readout and Ramanujan equations; native analytic attachments and GMP certification remain open. No CI or kernel run, per user direction.
