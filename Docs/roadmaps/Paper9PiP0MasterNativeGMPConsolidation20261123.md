
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


### 2026-11-27 — Consolidated native H1→H4 and direct GMP terminal cut

**Source-written, uncompiled, not promoted to acceptance.** Supersedes the earlier H1 unwritten inventory. Original arithmetic owners, signed strata (including their intersection), all-index zero mode, and original Cauchy ring retained.

| Commit | Source attachment |
|---|---|
| 75ca943c62cd | ClosedBoundaryExact: both equality-stratum boundary folds and four antidifferences |
| 64aa3b851893 | GradeFibreExact: bidirectional factor-key product permutation |
| e2cc973f003f | SigmaFoldExact: partition by positive grade, actual sigma-power readout |
| e1718439518c / 213b5ce5d446 | RamanujanIntegerExact: four signed identities, convolution exchange, sigma7 elimination |
| 8d9fde04451a | IntegerRowExact: literal integer Cauchy row and denominator-one reflection |
| c0cd8ef52de1 | JInvariantBishopLiteralRamanujanExact: all three literal coefficient identities |
| 9bd330ee8f53 | HyperMajorantsExact.AtRoot.rawFromCM consumes those three proofs internally |
| 09f93447ae48 | LiteralTerminalExact.AtOriginalCM.allRaw: original diagonal isolation and signed disk packet composed with rawFromCM |
| 0c38b7a0e29d | LiteralRealSliceEvaluationExact: all positive-degree original E4/E6 jet evaluations and absolute witnesses |
| 33278fcf0050 | LiteralBracketExact: original signed Rankin-Cohen bracket and differentiated bracket evaluation |
| 717696081267 / e3b19803ff02 | Original GMP receipt adapter and independent integer replay/Lean theorem generator |

Lean companion branch research/paper9-original-eisenstein-derivative-20261125 commit 1ca5f2d7666c, Integration/Paper9GMPWindowAcceptance.lean: raw segment join/append, rational observation equivalence, cross-GCD cancellation, actualPrefixLimit from eight existing decision proofs, arbitrary-scale gmpWindow, strict floorFromWindow/floorFromRaw. This is the direct production proof candidate, independently of the native Agda port; no cross-kernel postulate. Receipt adapter includes original check_pi_gmp_quotient_residual.cpp without editing it. Replay independently checks the original unreduced prefix ratios, adjacent step, sqrt bracket, reciprocal corners, strict floor residual and digest. Optional --emit-lean generates a theorem using floorFromRaw and kernel by-decide, without running the kernel.

Local acceptance (deferred at user direction): compile adapter with g++ -O3 -std=c++17 scripts/paper9_gmp_certificate_receipt.cpp -lgmpxx -lgmp -lcrypto -o /tmp/paper9_receipt; /tmp/paper9_receipt 100 plain > /tmp/paper9.json; python scripts/check_paper9_gmp_certificate_receipt.py /tmp/paper9.json --emit-lean /tmp/Paper9Receipt.lean; repeat cross mode; typecheck companion endpoint and emitted theorem from the Lean project, print axioms. Larger GMP receipts and timings are separate from feasible kernel reduction. No CI or kernel execution in this cut.

Native residual cut: original normalized lattice/Fourier/phase and degree-41 Hecke diagonal identity; actual half-unit analytic enclosure; identify actual j quotient Euler jets and original reciprocal-ray disk germ coefficient residual. The bracket and differentiated bracket evaluations are now source-written, not yet kernel-accepted. OriginalCMCut still explicitly requires first and second jet identities, enclosure, diagonal, cross; do not claim unconditional native RawCross. H1 literal source and H2–H4 consumer composition now written; all elaboration/termination/axiom audits and possible repairs remain. Production receipt-to-theorem source is written; runtime acceptance and actual compiler correctness are not established. No new external mathematical premise asserted. Classical CM/Hecke/Ramanujan/Chudnovsky authors retain attribution; DASHI contribution is the signed native fold and certificate transport.


### 2026-11-27 — Consolidated source implementation: H1–H4, C3 quotient and GMP proof/replay

Kernel/CI execution explicitly deferred to local operator. All newly written proof bodies are candidates, not accepted theorem receipts. No external Boolean or output hash is elevated to formal authority.

Reconciled actual branch: the preceding implementation already contains FiniteDivisorConvolutionClosedBoundaryExact, GradeFibreExact, SigmaFoldExact, RamanujanIntegerExact, IntegerRowExact and JInvariantBishopLiteralRamanujanExact. The latter is the canonical all-index E2/E4/E6 producer; JInvariantBishopCM163LiteralBracketExact evaluates the original bracket and differentiated bracket using the actual all-order X/Y weighted jet streams. HyperMajorantsExact.AtRoot.rawFromCM already consumes all three Ramanujan theorems internally. Thus H1–H4 source chain is present, not four unpaid caller hypotheses. 5071db0ea3c7 makes the natural shear sum embedding explicit in the actual integer difference theorem. Provisional redundant row/real-Ramanujan/terminal modules written during the pass were removed (ed370c31094a, 168bab669172, e3b757a4d9de) rather than maintaining alternative arithmetic owners. Keep original existing literal modules.

C3: c91d121ddc2d adds JInvariantBishopCM163QuotientJetExact. On the original guarded j with d=X^3-Y^2, constructs numerator and denominator first/second coefficient jets from the existing actual evaluated E4/E6 derivatives. Constructs a,b by the same d-apartness, proves q0/q1/q2, signed bracket and differentiated-bracket syzygies, derives FirstQJet and SecondQJet at the actual CM root. 9b7b882d30c5 extends existing LiteralTerminalExact: cutFromOriginalQuotient, allRawFromOriginalQuotient, periodFromOriginalQuotient. Remaining native C3 is the analytic identification of these formal quotient jets with the original reciprocal disk germ and vanishing of its normalized degree-41 cross first coefficient; scalar inverse solution and jet equations are no longer missing source.

GMP: companion Lean branch research/paper9-original-eisenstein-derivative-20261125: Integration/Paper9GmpCertificate.lean 9f7ae19b916e and cbd248a1adba implements arbitrary ordered split-tree correspondence to original prefix, signed cross-GCD common-factor invariance for P,Q,T, proof-relevant Evaluates, arbitrary actual Chudnovsky pi-window from existing eight finite decisions, and strict upper one-division decimal admission. Integration/Paper9GmpTraceChecker.lean 9bf806801295 implements executable checked trace plus sound, from exact reduction divisions, contiguous original leaf list, square root and floor inequalities. Both use actual existing Lean period source; no additional analytic premise in the terminal checker. Agda repo scripts/paper9_gmp_native_certificate.cpp e6458819fc5f calls original split without changing pinned benchmark source; optional postorder exact signed division trace, original prefix and adjacent append, strict integer square root and floor, coordinates/digest receipt. scripts/paper9_gmp_trace_to_lean.py 903fe57f0861 validates raw trace and emits local Lean decision input consuming sound. No generated local proof, compiler run or timing claim in this pass. Runtime trace replay is optional and distinct from the fast benchmark. Preserve source coordinate provenance and attribution; a successful Lean replay is not an Agda proof.

Exact remaining max-cut:
- C0: actual atan-series/Cayley source identity at 1/5 and 1/239 on original Bishop complex; original q phase consumer already present. Master K04d/K05 roadmap confirms actual nested atan-exp coefficient + evaluation or derivative/uniqueness source cut, not additional finite Cayley algebra.
- C1: actual normalized lattice/Fourier same-object, summable shell majorant and SL2Z reindex from donor #1552, actual Hecke monic polynomial/Laurent pole removal and coefficient reflection (Lean source donors named above).
- C2: narrow original CM half-unit enclosure and actual diagonal zero on same lattice/Fourier object; literal packet finite isolation already written.
- C3: identify constructed quotient jets with real ray analytic germ; actual degree-41 normalized product residual first-coefficient vanishing. Feed only enclosure, diagonal and OriginalRayResidual to allRawFromOriginalQuotient, no new terminal carrier.
- Lean universalRawCross and GMP checker terminal source exists; local kernel/axiom and trace acceptance pending. Actual native Agda universal RawCross remains conditional on the three genuine original analytic CM inputs. Do not mark acceptance or unconditional native theorem until discharged and run.


### 2026-11-27 — C0–C3 native analytic maximum-cut implementation pass

Source-written; no kernel or CI invocation. The half-unit witness is now constructed directly on the original guarded quotient, without assuming its CM equality or modularity.

- C2: JInvariantBishopCM163SharpRadiusExact (14385c9427c7; follow-up c382eb8041ec) consumes original Machin 32-stage error, semantic sqrt(163), scaled exponential Taylor partials, 16/15 geometric budget, six exact doublings, reciprocal cross and positive order cancellation. JInvariantBishopCM163SharpRootEnclosureExact (120e21329bfe; follow-up 0eee68ee28eb) consumes original signed E4/E6 terms and tails, bounds the positive magnitude of the discriminant and clears the guarded quotient. No CM root assumption. Independent exact rational replay of the numerical inequalities gave offset enclosure approximately [-1.136e-9, 9.323e-10]. Replay script scripts/check_paper9_native_sharp_enclosure.py (f784098a1485) reads the native literals; script itself pending local execution, not a kernel receipt.
- Existing LiteralTerminalExact (3b3d5f51a453) now supplies allRawFromDiagonalAndRay and periodFromDiagonalAndRay, constructing Sharp.enclosure internally. Two explicit analytic input witnesses remain: original diagonal zero and OriginalRayResidual.
- C1: transferred exact PR #1552 donor files from fe44b21d43dc3fd0a817e972ad834d93ca80cf7d (f084e50f36d5, 0a2e3a305e51). JInvariantBishopPuncturedShellSummabilityExact (d29870d56b6a; 6c7ca28a3104) derives all-index shell bounds from reciprocal-square/Basel comparison; constructs real and imaginary G4/G6 shell convergence and absolute shell convergence. Actual change of exhaustion, normalized lattice/Fourier identity and Hecke product remain open.
- C3: JInvariantBishopCM163ReciprocalGeometryExact (8307f93093a5) implements homogeneous reciprocal maps, fixed point quadratic, disk conjugacies, multipliers and four signed product jet coefficients. JInvariantBishopCM163NormalizedCrossAlgebraExact (313a969430cd) implements raw cross algebra and cancellation of the ray factor w^4 alone, plus formal first-jet coefficient readout. Actual analytic Taylor limit/product extraction on the original ray remains open.
- C0: original Machin/Cayley finite phase and recurrence donors are present. Analytic exp(2i atan) identification at both original Machin inputs remains open. Not solved by the sharp radius enclosure.

Remaining implementation in dependency order: (1) original atan/exp analytic identification; (2) unconditional shell rearrangement, normalized Fourier equality and degree-41 Hecke product/pole removal; (3) derive diagonal vanishing and original ray analytic coefficient vanishing from that product and the existing geometry/quotient jets. Feed both into allRawFromDiagonalAndRay. Lean production chain is unchanged this pass. Native source elaboration/axiom audit and acceptance remain deferred. Do not mark unconditional RawCross or GMP acceptance. Classical identities retain original attribution; DASHI contributes constructive enclosure, native geometry and proof transport.


### 2026-11-27 — Native S/T summation transport, normalization and actual atan quadratic remainder

SOURCE-WRITTEN, UNCOMPILED. Continues C0/C1 on the actual Bishop carrier. No new postulate, generic infinite-sum model, or synthetic atan. Kernel and CI deferred at operator direction.

| Commit | Implemented source |
|---|---|
| 382d5cb2a45b / 81a66f119edf | JInvariantBishopSquareShellReindexExact: signed rotation and inverse, square/shell permutations, guarded finite summand fold and four actual S limit transports |
| 86c8a66e7351 / 78eda8602cdf | JInvariantBishopSquareExhaustionExact: origin omission, exact square/shell partition and prefix identity, membership-based remainder and absolute-tail sandwich |
| 0ac6e41dc519 | JInvariantBishopShearExhaustionExact: T and inverse, Q_n subset T(Q_2n) subset Q_4n, cofinal absolute-tail limit transport |
| 7d0104dc8d78 / 74e1b7c7cfc0 | JInvariantBishopLatticeGeneratorSummandExact: integer embedding, actual upper-half-plane generator actions, denominator laws, reciprocal uniqueness and summand transformation |
| 51ad849c0090 | JInvariantBishopLatticeGeneratorModularityExact: finite sum transport and actual G4/G6 global S/T laws |
| 5d6d3db7bc4e | JInvariantBishopLatticeNormalizedGeneratorsExact: explicit 45/pi_M^4 and 945/(2*pi_M^6) normalized lattice values and S/T laws |
| 5584f431b98e / acfa73186b57 / 1938e51aca72 | BishopOriginalMachinAtanSecondOrderExact: actual signed finite atan quotient and increment, odd slice bound, exact half-radius potential, original-limit quadratic remainder |
| 989c47263039 | scripts/check_paper9_lattice_generators_atan_potential.py: local exact finite/symbolic replay |

C1: S preserves the actual finite square and shell membership; T is not falsely treated as a finite shell permutation. The cofinal shear uses actual absolute convergence of all four real/imaginary weight-4/6 components. Zero padding is solely a finite sum representation of the omitted origin, not a reciprocal at zero. The normalized E4/E6 lattice values use the original Machin real and its positive inverse. Generator modularity is written on the convergent source only; Fourier identification remains genuinely unpaid. Do not instantiate the old total sum over arbitrary (possibly divergent) lattice functions.

C0: for x,x+h in [0,1/2], the actual signed finite atan has a second-order increment factor. At radius r=1/2, the unweighted power first and second quotient recursions Q_n,T_n and p_n=r^n satisfy B_n=2T_n+4Q_n+8p_n=T_n+B_(n+1), with B_0=8 and nonnegative B_n. The reciprocal-weighted odd slice is bounded by this budget. Pass the finite remainder inequality to the original atan limits and original derivative geometric limit to obtain |A(x+h)-A(x)-h d(x)| <= 8|h|^2. The actual d(x) cancellation (1+x^2)d(x)=1 is already supplied by BishopOriginalLogAtanDerivativeLimitValuesExact. This is the source-written uniform quadratic increment, not yet the Cayley identity.

Local execution: 164 finite square/shell/reindex batches (radii 0..40), 2 symbolic denominator identities, 400 exact rational potential iterations including odd-slice bounds; 566 checks passed. The committed replay repeats that diagnostic, not an Agda kernel proof.

Remaining native maximum cut:
1. Use the original atan quadratic increment and native complex exponential small-increment factor to derive normalized Cayley endpoint identity at the two original Machin arguments, then feed the existing phase consumer.
2. Prove actual Fourier row evaluation and axis normalization (including the required even zeta evaluations) on the concrete normalized lattice limits, then degree-41 Hecke product/pole removal and literal packet identification. Generator laws are now source-written; do not reimplement generic S/T geometry.
3. Derive original diagonal zero and actual reciprocal-ray analytic quotient jet / cross coefficient vanishing; feed the two existing terminal witnesses to allRawFromDiagonalAndRay.
4. Native and Lean elaboration/kernel/axiom acceptance and actual GMP trace/floor acceptance remain deferred. No unconditional native RawCross claim. Preserve classical authorship and original donor provenance.


### 2026-11-27 — Original Machin analytic endpoint and finite Lambert fibre

SOURCE-WRITTEN, UNCOMPILED. No CI, native kernel, Lean kernel or production GMP replay invoked.

- 72f89361d553 / b03590932bf8: restore missing original imaginary-axis and addition helpers in BishopSetoidComplexExact; the actual configured native product and parity consumers are reused.
- ed7767ae40da: recover BishopNatRealReciprocalSquareBaselExact from original donor 8e75c14b4a4d0572f594977a6ed106802ad16329, including reciprocal order and power lemmas needed by the existing mesh.
- 266c34d07e9d: BishopOriginalMachinAtanSmallPhaseExact: actual atan increment, nonnegative half-ball angle and original sine/cosine Taylor errors, no derivative interchange.
- 8ff8e2f0f6fd: BishopOriginalMachinCayleyConservedPhaseExact: for y=x+h, D=1+x^2 and N=1-x^2+2ix, normalize the actual phase by conjugate(N)/D. The exact first-order cancellation residual is 2h^2(1-iy); component increment bound 204h^2.
- f9678835ecbf / 346a4e525d2b: BishopOriginalMachinCayleyEndpointExact: clipped equal mesh with 16+n cells, fixed endpoint difference bounded by 204*x*h tending to zero; invert the unit Cayley factor and instantiate both original atan values. Also derive original quarter equality and first sine zero using existing consumers. No ODE uniqueness or mean-value premise. Configured Round11 source input retained.
- 4a62d817cd05: attach both actual endpoint proofs to JInvariantBishopCM163OriginalPhaseExact.qFromOriginalAtans. The selected CM phase no longer has caller-supplied atan/Cayley evaluations at source level.
- 40d0545a6d8f: JInvariantBishopLambertDegreeFibreExact: actual positive factor-pair scan, product degree readout and weighted complex fold; match the original 240 sigma3 and 504 sigma5 tail terms. This is finite regrouping, not infinite row evaluation.

Current residual cut:
1. C0: source implementation connected; elaboration and kernel verification outstanding.
2. C1: establish actual horizontal lattice row evaluation and axis even-zeta values on the original Machin carrier; transport absolutely convergent rows to the degree fibres, identify original normalized E4/E6, then actual degree-41 Hecke product and coefficient/pole removal.
3. C2/C3: derive original diagonal zero and original analytic ray residual; existing allRawFromDiagonalAndRay internally constructs enclosure and consumes these two witnesses. No unconditional native RawCross claimed.
4. All native and Lean source acceptance and GMP trace/floor acceptance deferred. Lean terminal unchanged this round.

Classical Machin, Cayley, Eisenstein and Lambert identities retain their source attribution; DASHI contribution here is the constructive finite mesh conservation, source-specific evaluation and degree-fibre transport.


### 2026-11-27 — C1 original Fourier row rational evaluation and signed dyadic refinement

SOURCE-WRITTEN, UNCOMPILED. No Agda or Lean kernel, CI or production GMP replay invoked.

| Commit | Implemented source |
|---|---|
| 127701b365c4 | JInvariantBishopDyadicFourierRowExact: guarded rational X(q)=q/(1-q)^2, X(q)+X(-q)=4X(q²), X(q)X(-q)=-X(q²), weighted P4/P6 dyadic identities |
| 549dd46611e4 | JInvariantBishopFourierRowFiniteTailExact: exact polynomial B3/B5 coefficient recurrences and all-cutoff cleared partial sum telescopes |
| 3c0bf97b38be | JInvariantBishopFourierRowLimitExact: actual original disk absolute convergence, polynomial-tail vanishing, guarded denominator cancellation and cleared row limits |
| 90184b387ddd | JInvariantBishopFourierRowRationalExact: match those actual Fourier limits to P4(X), P6(X) on the original complex carrier |
| 236995c3ebcc | JInvariantBishopOriginalDyadicRowTransportExact: original exponential product, actual q at positive-height points, both signed half-sheet maps and arbitrary-depth refinement |
| 900d13df9c90 / 5b5441284e68 / 368193010659 | JInvariantBishopComplexOriginQuadraticRemainderExact: literal factorial-series directional quadratic remainder with component budget M² exp(M), exact native exp increment factor, slope convergence on bounded null sequences |
| 09c66082522f | scripts/check_paper9_dyadic_fourier_rows.py |

Local SymPy replay: 53 exact assertions passed, including recurrence, finite telescope, rational row, two-sheet identities, repeated dyadic identity checks, q=-1 algebra and finite origin expansion. This is not kernel validation; the generated large ring-solver expressions also need elaboration/performance review.

The selected constructive row route is dyadic rather than an imported cotangent partial fraction authority. Write F4(q)=X+6X² and F6(q)=X+30X²+120X³. For N=2^m the actual row splits into N scaled half-sheet descendants with weights N^(-k). The origin directional factor now tends to the literal direction. To complete the row bridge, still prove the centered integer-residue enumeration, guarded reciprocal limit at each fixed nonpole lattice point, and uniform summable tail domination. The latter uses |1-r exp(i theta)|²=(1-r)²+4r sin²(theta/2), the original signed two-ball cubic sine lower bound and eventual lower bound on r for fixed height. Use existing absolute shell/Basel convergence for cofinal passage, not a formal exchange. At z=1/2 separately admit real-axis nonpole guards; q=-1 gives P4=1/8 and P6=-1/4, yielding the required even-zeta constants only AFTER the row bridge. No even-zeta proof is claimed yet.

Remaining C1: these lattice-row limit steps, axis normalization, infinite row/degree-fibre rearrangement, normalized E4/E6 equality, actual degree-41 Hecke product/pole removal and coefficient reflection. C2/C3: derive original diagonal zero and original analytic ray residual; feed existing terminal (which constructs sharp enclosure). C0 and Lean/GMP source acceptance remain deferred. No unconditional native RawCross claim. Classical dyadic distribution, Fourier and Eulerian polynomial identities retain their mathematical provenance; DASHI contribution is source-specific constructive proof transport. No new unrelated framework.


### 2026-11-28 — C1a: Karp/PNP signed finite-carrier weld and native fixed-summand limits

Source-written proof bodies on PR #1546; no Agda kernel or CI acceptance asserted.

- `2e7e6daede4e`, `20cfbfb7ade9`, `5316d93461b9`, `0f6c1a4f5df6`: `JInvariantBishopCenteredDyadicAddressExact`. Reuses the existing PNP `PNotEqualsNPExactResidualSummaryBitLowerBoundExact` Boolean vector/Fin codec and core BinaryWord carrier; directly calls Karp's `Karp21FinDecoderIndexBidiExact.reconstructCanonicalFin` for positive canonical reconstruction. Both directions of the signed address codec, integer readout, uniqueness, range-proof independence, and cofinal coverage are written. Low-first execution uses positive weights except for the final high bit; at depth m>=1 the actual interval is [-2^(m-1),2^(m-1)). No negative zero or sign-only compression.
- `05a28b3ef232`: `JInvariantBishopCenteredDyadicRowExact`. Actual original upper-half-plane walk is (z+j)/2^m; weighted binary fold and original rational row agree. The final split uses the negative half-sheet to centre the index. No claim that enumerating the fold is polynomial.
- `9c71ce2698fd`: `JInvariantBishopDyadicReciprocalLimitExact`. Derives reciprocal continuity from actual inverse pairs, including the eventual bound b_n<=2b for positive real inverse norms and the error identity. Uses v=-h/(1-q), d*v=1, d->z; v converges to the guarded reciprocal of z. No assumed complex reciprocal continuity theorem.
- `793fbcf0ce4a`: `JInvariantBishopDyadicScaledRowLimitExact`. Y=q*v^2=h^2 X; h^4 F4=h^2 Y+6Y^2; h^6 F6=h^4 Y+30h^2 Y^2+120Y^3. Limits retain signs and yield 6 V^4 and 120 V^6.
- `ae0910ed88c8`, `02ae00e24e7b`, `9a1d7e978d50`: `JInvariantBishopCenteredDyadicSummandLimitExact`. Attaches actual Machin exponential, positive height/nonpole guard, concrete dyadic null sequence, explicit norm radius and fixed integer shift; connects the exact conserved finite aggregate to the centred integer fibre. Fixed integer summand limits are source-written, not global lattice row equality.
- `9a8dcc44f773`, `ba4d5018dcb2`, `75d76bbd4eba`: `JInvariantBishopDyadicRowTailMajorantExact`. Actual phase identity |1-rho exp(2it)|^2=(1-rho)^2+4rho sin^2(t); signed half-angle coercivity under explicit geometric range hypotheses; radial floor from original exponential product; scaled inverse bound and actual rational-row polynomial majorants. If rho>=rho0>0 and the signed angle bounds give rho0(hJ)^2<=|1-q|^2, use b=1/(rho0 J^2), B=1/rho0. Both rows are bounded componentwise by (1+6B)b and (1+30B+120B^2)b respectively. NaturalTail attaches the original Basel reciprocal-square term.
- `8e5990ac1495`: `scripts/check_paper9_centered_dyadic.py`, exact independent local replay: 8190 address, 8190 affine chart, 8190 cofinal embedding, 5 symbolic algebra, 40960 rational majorant assertions = 65535/65535 PASS. These checks do not constitute Agda elaboration or kernel acceptance.

Donor provenance: existing DASHI binary branch owner and PNP finite codec, Karp canonical Fin decoder (Karp PR #1474; PNP Agda #1548 / Lean #119), standard-library finite-index lemmas. New signed dyadic lattice attachment and analytic limit proofs are DASHI extensions; classical Fourier, exponential and Basel identities retain their original mathematical provenance. This does not pay P vs NP's universal cost/progress obligation or modify the donor branches.

**Remaining C1a max-cut:** instantiate the explicit geometric tail hypotheses uniformly on the actual centred integer range, including the eventually small real shift and the sign-dependent angle bound. Then weld the conserved finite fold and fixed summand limits to the original lattice row by cofinal dominated summation, keeping the zero index separate. The half-integer real-axis specialization and even-zeta normalization are not yet paid. C1b infinite Lambert rearrangement and normalized E4/E6 equality, C1c degree-41 Hecke identity/pole removal, C2 original diagonal zero, C3 analytic ray residual, and terminal RawCross/GMP acceptance remain. All new native proof bodies are uncompiled; no CI invoked. Lean companion unchanged.


### 2026-11-28 — C1a upper-half-plane row max-cut

Source-written, kernel pending; no CI run. This cut completes the intended upper-half-plane horizontal row proof chain at source level; it does not establish Agda acceptance. The real-axis normalization and two-dimensional row rearrangement remain independent.

| Commit | Actual source implementation |
|---|---|
| 42209e0a1af8 / c621f2a7d6f2 | JInvariantBishopCenteredDyadicTailGeometryExact: h(suc n)*2^n=1/2; constructive dyadic depth and Archimedean index cutoffs; both actual signed leaves, radial floor and original disk norm, literal Basel majorants |
| 1ceb75f3fad1 | JInvariantBishopCenteredDyadicFoldReindexExact: existing binary word and finite unique-permutation owner; canonical signed interval pairs (+k,-(k+1)); exact integer coverage and fold transport |
| 1922a6fa8b6f5 | JInvariantBishopCenteredDyadicDominatedSumExact: actual finite prefix complement bound and constructive cofinal passage to a conserved target; no assumed target series convergence |
| b21b0ee73cd7 | JInvariantBishopCenteredDyadicRowClosureExact: componentwise cofinal convergence for original weight 4 and 6 Fourier rows using actual fixed-integer convergence, paired majorants, and exact conserved aggregate |
| d120ebe80d01 / 7ea75f3e3331 | JInvariantBishopCenteredDyadicLatticeReadoutExact: original lattice kernel on (1,j), exact reciprocal product and inverse-power normalization, unweighted paired lattice row convergence with explicit undo4/undo6 |

Geometry: h=2^-m, J=|j|, x=Re(tau). For h|x|<=1/8, hJ<=1/2 and J>=2|x|, set v=h(J+sgn(j)x), u=pi*v. Then 0<=hJ/2<=v<=5/8, u<=110/56<2, and hJ<=(2/3)u. The integer coordinate chooses the phase sign, so no decidability of arbitrary Bishop real signs is needed. With rho0=exp(-2*pi*Im(tau))>0 and rho>=rho0, the existing half-angle lemma gives rho0*(hJ)^2<=normSq(1-q). The previous tail polynomials now instantiate on both actual signed sheets. Pairing (+k,-(k+1)) avoids the extra positive endpoint and retains zero once. The majorant for k>=1 is C*(1/k^2+1/(k+1)^2), and the finite head is handled separately.

Cofinal passage: for arbitrary precision epsilon choose a fixed interior K past the summable-tail cutoff. Choose depth n after the actual finite-prefix convergence modulus; the original dyadic cardinal covers K. The moving complement is bounded by the difference of two convergent majorant prefixes, hence <=epsilon/2; the interior discrepancy is <=epsilon/4. Conservation identifies the original Fourier row as the fixed-lattice-prefix limit. No infinite-sum exchange is assumed.

New terminal source declarations: latticeRow4, latticeRow6 (original lattice kernel at horizontal coordinate 1); limits are (2*pi*i)^k/(k-1)! times the original rational Fourier row. The prefactor is canceled by an actual complex product identity. Zero and the imaginary sign are preserved. This is not yet the full double lattice or normalized E4/E6 theorem.

Independent exact replay: scripts/check_paper9_centered_tail_geometry.py; local 32467/32467 assertions (11 ranges, 20249 geometric bounds, 12205 pairing/positive majorant checks, 2 symbolic phase equations). No native elaboration, kernel or performance receipt. This replay tests finite/rational geometry, not the universal analytic proof.

Next maximum cut: (i) actual half-integer real-axis nonpole guards and same dyadic limit (or a proved vertical-boundary passage) to pay even-zeta normalization; (ii) absolute two-dimensional lattice shell to row/degree fibre rearrangement, original Lambert E4/E6 equality; (iii) Hecke-41 product and pole removal; (iv) C2 original diagonal zero and C3 analytic jet/ray producer; (v) RawCross and GMP. Reuse existing native shell, Euler and Hecke consumers. H1's outstanding coefficient regrouping/attachment and all prior kernel checks remain separate. Donor branches (Karp, Direct PNP, FRACDASH, Lean companion) unchanged. The signed finite codec and original finite permutation donors are retained; no computational independence or universal P vs NP progress claim.


### 2026-11-28 — RH donor reconciliation; C1a real-axis normalization and C1b positive-row attachment

Source-written, kernel pending. Audited the newest relevant RH PRs: Agda #1551 at 1a4fbab6d9af (original eta pair telescoping and triangle tails), #1533 at f2398bfa5266 (canonical dyadic nat-log source reduction), #1478 at fb374e50e59a (raw SeriesOf identity inventory); Lean #121 at 7f72b5d60486 (original admission, not an analytic shortcut), #116 at 7f8f4b7cde59 (explicit origin/variation residual), #113 at 5b22b8f86a42 (admission handoff inventory), and #108 at c0dcb1f8f624 (faithful source Dirichlet continuity). Inspected actual source bodies of the eta pair, triangle-tail, dyadic log, Lean Dirichlet continuity, Fourier terminal and RH admission owners. The relevant donor is the original finite-prefix/limit-order/same-source method, not any external RH claim or assumption. Existing Paper 9 branch already had RH canonical log inverse, source negative log powers and actual above-two completion.

| Commit | Actual new source |
|---|---|
| dbcc4ab3c6d6 | JInvariantBishopUniformBoundaryPassageExact: RH finite-tail identity and adapted uniform limit-order passage from actual convergent rows to the actual boundary prefix |
| 3f33a46872a4 | JInvariantBishopHalfIntegerBoundaryTermsExact: signed nonpole half-integer denominators; uniform norm-square and fourth/sixth component Basel budgets; actual fixed-term reciprocal limit and original-kernel readout |
| 6dfdc3aa0773 | JInvariantBishopHalfIntegerBoundaryFourierExact: vertical positive-height Machin q approaches -1, guarded boundary gap inverse is 1/2, X tends to -1/4; rational row limits |
| 45fa483f2485 | JInvariantBishopHalfIntegerBoundaryClosureExact: instantiate the uniform passage on both weights and both coordinates, with the original upper-half-plane row theorem and actual half-integer axis terms |
| a189ddef6b82 | JInvariantBishopEvenZetaNormalizationExact: literal positive Nat reciprocal power series, exact odd/even readout, uniqueness of original limits, cancellation giving zeta4 and zeta6 |
| cba19f7f85cf | JInvariantBishopEvenZetaRHSourceWeldExact: direct use of canonicalNatLogAllIndicesExpInverse and sourceExpNegativeLogSumIsReciprocalPower; originalZeta4, originalZeta6 and both imaginary-zero endpoints on RH's own actual above-two Dirichlet value |
| 63d4e05bd6f4 | JInvariantBishopNormalizedPositiveRowExact: all positive horizontal coordinates (m,j), q(m tau)=q(tau)^m, original lattice row term readout and zeta-normalized coefficients 240/-504 |
| f7b3971e5398 | scripts/check_paper9_half_integer_boundary.py: exact local rational/SymPy 6162/6162 PASS (512 half-integer, 1536 norm, 3072 power majorant, 1038 parity, 4 normalization assertions) |

The vertical path is tau=1/2+i*2^-n; no disk hypothesis at the boundary itself. For each signed pair (+k,-k-1) the two denominators have real components +/- (k+1/2). The norm square of either is at least (k+1)^2/4 uniformly including y=0. Thus the reciprocal norm square is <=4/(k+1)^2; weights 4 and 6 have componentwise bounds 16/(k+1)^2 and 64/(k+1)^2 per signed term. Uniform limit passage first sends each row prefix cutoff to infinity using its own convergence and the common majorant, then sends height to zero with fixed prefix. This does not assume convergence of the boundary series.

The boundary row limits are pi^4/3 and 2*pi^6/15; the axis readout is 2(2^k-1)*zeta(k). The explicit odd/even prefix identity and reciprocal-power even scaling prove the intended source endpoints zeta(4)=pi^4/90 and zeta(6)=pi^6/945. The original RH Dirichlet same-object transport consumes the canonical native log inverse and original exp terms, not an opaque zeta continuation. Positive horizontal rows now carry 240*zeta(4)*F4(q^m) and -504*zeta(6)*F6(q^m). Sign of weight six retained.

Remaining C1b: actual absolute two-dimensional square-shell-to-row rearrangement (including the horizontal-zero and negative-m reflection), infinite Lambert row/degree fibre rearrangement and normalized E4/E6 same-object identity. Existing JInvariantBishopLambertDegreeFibreExact pays the finite factor-pair coefficient readout, not that infinite interchange. C1c Hecke-41 product and pole removal; C2 original diagonal zero; C3 original analytic ray residual; native RawCross/GMP acceptance and H1 coefficient attachment remain. All new and earlier native modules still need local Agda elaboration, including ring-solver expressions and dependent-index transport. No CI invoked; no donor branches modified. No external RH or Clay acceptance inferred. Classical series identities retain their historical provenance; DASHI contribution is the original-carrier native attachment.


### 2026-11-28 — signed theta geometry and original half-phase analytic donor (parallel C1b route)

User-directed geometry-forward reuse; classical Jacobi theta identities, D4/Hadamard lattice geometry and Legendre invariants retain their original mathematical provenance. DASHI contribution is the explicit indexed signed shell BIDI construction and the native original-carrier coefficient/limit attachment. No new E8/ternary action identification or new classical modular identity is claimed.

Original owners inspected: AbelE8RootE4FirstCoefficientExact (actual generated-root length = literal E4 q^1 coefficient), AbelE8ThetaParityProjectorExact (all-index conditional signed count algebra), AbelE8HalfOddShellInvolutionExact (sign flip), TetracodeE8ExplicitMapExact (executable 24+216 root map receipt), JInvariantLambdaOrbitIntegerKernelExact (homogeneous Q and denominator), JInvariantBishopLiteralRamanujanExact (existing signed divisor/Cauchy differential route), JInvariantBishopOriginalDyadicRowTransportExact (actual Machin square and opposite half sheets), BishopAbsoluteCauchyProductSpecializationExact (native scalar absolute product), FiniteDivisorConvolutionIntegerRowExact (integer-to-Bishop row), and prior BSD EllipticCMJacobiThetaCheckedRowsExact (finite only, not a Jacobi product theorem).

| Commit | Source implementation |
|---|---|
| a2bf5fdd7aa6 | JInvariantThetaLegendreSignedGeometryExact: literal square/triangular exponent scans and native original integer Cauchy products; signed half-sheet Q,W invariance and V sign; first theta coefficients, E8 root and signed E6 coefficient crosswalks; cleared discriminant |
| de13a5ff8026 | JInvariantBishopThetaDiskExact: actual Machin half-phase t=q(tau/2), opposite sheet q((tau+1)/2), t²=q(tau); primitive positive-degree square/triangular count tails absolutely converge by the existing linear polynomial-geometric budget |
| Lean 712ffe07b160 | Integration/Paper9ThetaHadamardGeometry.lean: all-index D4 Hadamard norm-shell equivalence and inverse, parity split, flip; generic commutative-ring Q,V,W and theta polynomials |
| Lean c335955cc5c6 | same owner: finite shell injection, norm parity, Nat.card signed Jacobi shell identity Bcoeff=Acoeff+Ccoeff for every degree, zero mode included |
| ee6ae973948a | JInvariantBishopThetaCauchyProductExact: native complex absolute Cauchy product via the four scalar rows, exact weighted integer coefficient reflection, product and fourth-power Readout |
| 0226f7a4e250 | JInvariantBishopThetaCoefficientEvaluationExact: full primitive coefficient streams with zero mode and quadratic budget; positive/negative B and positive H^4 actual analytic Cauchy readouts |
| 289f8a7921c5 | scripts/check_paper9_theta_hadamard.py: local exact replay, 30987 counted checks PASS (10176 integer BIDI, 20352 half BIDI, 130 shell equality, 130 Jacobi, 130 E4/E6, 65 discriminant coefficient and four symbolic polynomial checks), t-degree 0..64. Diagnostic only; not a native kernel check. |

Geometry: t=e^(pi i tau), q=t². Let A=16t H(t)^4, H(t)=sum_{j>=0} t^(j(j+1)), B=theta3(t)^4, C=theta3(-t)^4, theta3(t)=1+2 sum_{j>=1} t^(j²). A and B first degree pairs are A=(0,16,0), B=(1,8,24); C=(1,-8,24). Q=a²-ab+b², V=ab(b-a), W=(a+b)(2a-b)(a-2b), with W(0,1)=+2, and 4Q³=W²+27V². On B=A+C these are E4=Q, E6=W/2, Delta=V²/256. The t-sign transformation (a,b)->(-a,b-a) fixes Q and W, negates V. Thus source coefficients 240 and -504 are independently computed from the signed geometry, with E4=112+128 root count and E6=72-576 signed cubic interference. No unsigned 504 root count assumption.

The all-index Hadamard donor is H4(x)=(a+b+c+d,a+b-c-d,a-b+c-d,a-b-c+d). H4²=4I, norm(H4 x)²=4 norm(x)². For integer x with odd coordinate sum, H4 x has odd entries and sum divisible by 4. Conversely an odd-entry y with sum divisible by 4 has H4 y divisible coordinatewise by 4, with exact inverse H4 y/4. First-coordinate sign reversal interchanges the two half-lattice parity classes without changing norm. Hence HalfShell(n) is explicitly equivalent to IntegerOddShell(n) + IntegerOddShell(n), and norm parity identifies the signed integer shell contribution. The Lean all-index Nat.card theorem is on these actual norm predicates, not yet on the Agda finite Cauchy coefficient history. This is a genuine independent Jacobi coefficient construction, not a modularity assumption.

**Remaining exact seams, no duplicate theta carriers:**
- GTheta1: use the existing integer row and actual finite exponent decomposition to identify Lean NormShell/HalfShell counts with the coefficient counts of theta3^4 and 16t H^4 (all indices); transport the all-index signed Jacobi result. The finite replay supplies independent diagnostics, not this theorem.
- GTheta2: on the native Bishop coefficient Readout, pay monomial shift for A and sign twist for C using the existing original signed-power/Cauchy owner. Then use all-index coefficient equality and uniqueness of limits to establish B=A+C for the actual theta values. The current full primitive and fourth-power readouts already have absolute convergence.
- GTheta3: identify theta Q and W/2 with the original analytic E4/E6, either by native theta S/T + weight-four/six modular uniqueness (Poisson/theta transform and cusp normalization), or by all-index arithmetic identities on the original coefficients. Finite degree checks are not enough; this step is not paid by the first root coefficient.
- Main C1b: original 2D lattice-shell-to-row and Lambert degree rearrangement remains independently live. The theta donor does not replace this analytic weld unless GTheta3 is established. Retain horizontal-zero row, negative-m reflection, explicit residual bounds and original normalization.
- C1c, C2, C3, H1 and native RawCross/GMP remain unchanged by this parallel donor. All new proof bodies require pinned local kernel elaboration; no CI invoked. No master, RH, BSD, Karp or PNP donor branch modified. Lean changes on research/paper9-original-eisenstein-derivative-20261125 only. 

### 2026-11-28 — absolute rectangular exhaustion / row-fold attachment

Preserve the parallel theta donor; this extends the original C1b lattice route.
- `a410d1487ade` CofinalSquareSandwich: unique finite exhaustion between original inner and outer squares inherits original limit via absolute prefix difference and epsilon/4 splitting.
- `627bc9ec887c` RectangleExhaustion: original filtered square list with horizontal radius n and vertical radius max(n,m), arbitrary cofinal schedule, iterated limit consumer via chosen finite-row modulus.
- `202e2d992208` RectangleRowFold: actual signed cutoff codec product, membership equivalence/permutation to original rectangle, finite nested horizontal fold.
- Remaining: connect actual positive paired row limits to this fold, including zero row and negative reflection; absolute Lambert row/degree interchange and normalized E4/E6; then Hecke41/diagonal/ray/RawCross. Native elaboration pending, not solved by finite tests.
- Local independent rational reference (not repository import): 256 rectangle cases, 71460 points, 16419 positive factor pairs; exact finite regrouping, nontrivial signed sandwich and degree partition checks. No CI. 


### 2026-11-28 — signed theta literal coefficient and original modular uniqueness cut

Implemented on this branch:
- `ce728d93a24b` — `JInvariantThetaIntegerTwistExact`: all-index sign character on the original integer Cauchy row, fourth-power twist, finite-support 16t monomial shift.
- `238640f06d3d`, `2eecbe7d634d` — `JInvariantBishopThetaSignedReadoutExact`: actual two Machin half-phase readouts A/B/C, signed integer-to-Bishop coefficient transport, Q/V/W polynomial readouts, and analytic Jacobi equality from the all-index native coefficient premise.
- `a48957a826cc` — independent exact replay `scripts/check_paper9_theta_signed_transport.py`. Local execution: 397/397 checks passed, degrees 0–64, including direct integer/half-integer shell counts, twist, monomial, Jacobi counts and seven symbolic polynomial checks. Not kernel evidence.

Lean companion branch `research/paper9-original-eisenstein-derivative-20261125`:
- `a5a7f2827011` — `Paper9ThetaShellCoefficientWeld`: source-written exact graded product fibre, signed square and odd triangular coordinate bijections, shell-to-literal convolution readout, all-index Jacobi coefficient conclusion.
- `25b189d4af53`, `ce961aa1a091` — `Paper9ThetaModularTransport`: original Mathlib two-variable theta functional equation, signed fourth-power S/T transformation, weight 4/6 slash invariance using the existing SL2Z generator owner.
- `3d38f2700a96`, `ba8ad7a52d51` — `Paper9ThetaCuspNormalization`: signed square/triangular analytic summand pairing, explicit geometric cusp bounds and unit limits.
- `eb2bd072f1c8`, `19c99b71edbb` — `Paper9ThetaEisensteinSameObject`: theta minus original E4/E6 as cusp forms, quotient by the existing eta24 cusp form, negative-weight constancy and S evaluation at 2i force zero. Intended terminal theorems thetaE4_eq_original, thetaE6_eq_original and thetaDiscriminantNumerator have explicit bodies with no new local postulate. This route does not require the quartic identity as a modularity premise.

All new Agda/Lean source remains uncompiled; pinned Mathlib v4.28 API/elaboration compatibility must be tested locally. No GitHub CI. No proof transfer from Lean to Agda is assumed. Classical theta/Poisson identities, modular uniqueness, and Legendre algebra retain their established attribution; DASHI contribution is the explicit signed transport and original-carrier attachment.

GTheta1: Lean shell-to-literal history source written; native Agda all-index Jacobi coefficient theorem remains the uninhabited input of jacobiFromCoefficients. GTheta2: native analytic readout and conditional transport written. GTheta3: Lean modular uniqueness source written; native Bishop modular transformation/uniqueness or original lattice Fourier equality still required. Lean shell histories and analytic functions also need their exact all-index summation/coeff identification if used as a single chain. Main C1b absolute square-shell/row and Lambert regrouping remains open independently; C1c Hecke, C2 diagonal, C3 ray, H1 and RawCross/GMP acceptance unchanged. Do not replace a native theorem by a foreign theorem name or finite receipt. Next priority: discharge native shell-count theorem or original lattice same-object weld, then attach actual Hecke/CM endpoint.


### 2026-11-28 — existing Walsh–Hadamard reuse; native affine shell and independent analytic Jacobi

SOURCE-WRITTEN, KERNEL PENDING. User-directed audit recovered master owners:
- `DASHI/Physics/YangMills/BalabanBooleanFourCubeWalshCharacterExact.agda` and `BalabanBooleanFourCubeWalshInversionExact.agda`: exact 16-point character inversion over rational values.
- `DASHI/Physics/Closure/NSTriadKNLuoPeriodicWalshParsevalExact.agda`: eight-coordinate unnormalised energy identity and normalized Parseval.
- `DASHI/Analysis/NonArchimedeanHadamardEnergyNormalizationExact.agda` and `NonArchimedeanHadamardTwistedSectorBidiExact.agda`: source-specific receipts for rational two-point similarity and explicit normalisation; not D4 integral-shell proofs.

Direct D4 donor remains the existing companion `Paper9ThetaHadamardGeometry.lean` and `Paper9ThetaShellCoefficientWeld.lean`. Classical Hadamard, Jacobi, Poisson and modular-form identities retain their historical attribution. No import of unrelated physical carriers or promotion of a receipt to a theorem.

| Commit | Native construction |
|---|---|
| Lean 34bcc6055e7f | `Integration/Paper9ThetaAnalyticJacobi.lean`: actual signed residual R=B-A-C transforms by -1 under T and -z² under S. R² has weight 4, vanishes at cusp, and existing cuspZero forces R=0. Actual E4 and E6 Legendre and discriminant numerator attachments. Independent of shell counts. |
| Agda d12680e31074 | `JInvariantThetaHadamardIntegralChartExact`: division-free integral charts of both half-coordinate sheets; exact inverseRead, norm and reconstruction. |
| Agda d0a1ddfa40a2 | Raw coordinate coverage with explicit parity witnesses, fourth coordinate oddness. |
| Agda 830067d624ce | Full dependent grade round trips using decidable integer equality; twoCopiesLeft and twoCopiesRight. |
| Agda a091b1318a89 | `scripts/check_paper9_hadamard_affine_chart.py`: local independent reference PASS, 35 symbolic equalities, 439230 scalar affine chart checks, all 65 shell-degree comparisons (0–64), 20185 integer and 20352 half-coordinate points. Not an execution of committed Agda/Lean proof bodies. |

Integral geometry: let integer chart (k,b,c,d) read (2k+1-b-c-d,b,c,d). Half-even chart (j,u,v,w) reads (2u+1,2v+1,2w+1,4j-(2u+1)-(2v+1)-(2w+1)). Half-odd adds 2 to the last coordinate. The Hadamard chart map is (k,b,c,d) -> (2k+1-b-c-d,k,k-c-d,k-b-d). Its inverse is (j,u,v,w) -> (u,u+v+1-j,u+w+1-j,j-v-w-1). First-coordinate reflection maps the half-even chart to (j-u-1,-u-1,v,w) on the half-odd chart; inverse (j-u,-u-1,v,w). All maps are integral, affine and reconstruct every coordinate, not merely the norm. Original theta histories are unchanged.

Revised GTheta max-cut:
- Lean analytic Jacobi, S/T modularity, cusp normalization, original E4/E6 and Legendre/discriminant identity now source-written; do not list as missing constructions. All remain kernel-pending. The independent literal series-evaluation attachment of Lean jacobiLiteral remains optional cross-check, not needed for signed residual rigidity.
- Agda native D4 chart geometry and dependent two-sheet equivalence now source-written. Remaining exact native finite proof: extract parity witnesses from arbitrary raw coordinates, establish unique bounded signed enumeration of each grade, read its counts into the existing square/triangular scans and rowZ Cauchy convolution, use the chart permutation to pay B_n=A_n+C_n. Then instantiate existing jacobiFromCoefficients without rebuilding analytic readout. No cross-kernel proof import assumed.
- Native Bishop theta-to-Eisenstein same-object or original lattice-Fourier route still needed. C1b infinite rectangle-row and Lambert degree regrouping, C1c degree-41 product and pole removal, C2 original diagonal zero, C3 original ray residual and H1 final coefficient grouping remain. No new progress asserted on these lanes in this cut.
- Native/Lean kernels and original GMP acceptance remain separate. No CI invoked; pinned source elaboration may require API repairs.


### 2026-11-28 — native all-index Jacobi and rectangular row limit attachment

SOURCE-WRITTEN, KERNEL PENDING. This cut supersedes the prior GTheta1/GTheta2 missing-producer inventory. No native compiler is available in this runtime; no GitHub CI requested or invoked.

| Commit | Source implementation |
|---|---|
| b539c6ac6fde / 549744032e44 / e4366e3988f3 | JInvariantThetaGradedCauchyCountExact: finite labelled grade histogram, exact pair/fourfold count on original rowZ, delta shift and degree-local congruence, explicit unit reflection. |
| 20cdf702eb40 / a2d6bc08b32e | JInvariantThetaBoundedScanReadoutExact: exact finite square and triangular scan reflection, cutoff stability, zero counted once, all-index B and H^4 count. |
| 0b69354722c7 / a20652bdc5db / 99c824c79a57 | JInvariantThetaIntegralParityExact: constructive parity on signed integers, norm-total parity transport, half-chart split, parity exclusivity and cancellation, exact sign history. |
| eed550672b2f / 65fb45bf24fe / 27ac1c558706 | JInvariantThetaRawCoordinateGradeExact: literal signed raw labels and balanced product, filtered list count for B_n and A_(n+1), actual raw norm readout and factor 16, successor-first triangular embedding. |
| 2b7e1fce6d75 | JInvariantThetaBoundedShellEnumerationExact: unique bounded integer and odd-coordinate label lists and actual grade soundness/completeness. |
| 43e6da3281ee / 9c4e16523c1b | JInvariantThetaRawHadamardTransportExact: actual orientation-indexed forward map, norm transport, restricted injection, constructive preimage for every odd-coordinate tuple. |
| f2e59f12f048 | JInvariantThetaJacobiAllIndexExact: explicit list permutation by existing unique-membership theorem; odd-degree A=B+B; even-degree A=0; negative coefficient twist; terminal jacobiAll for every n. |
| 99a603a73463 | JInvariantBishopThetaSignedReadoutExact.At.analyticJacobi = jacobiFromCoefficients Jacobi.jacobiAll. Actual original Bishop readout; no uninhabited coefficient argument remains in this intended terminal. |
| f49e88325231 | scripts/check_paper9_raw_jacobi_permutation.py, independent local Python replay of equivalent reference. 20352 forward and 20352 reverse point checks, 65 exact shell image comparisons, 195 original integer coefficient comparisons, 20185 integer and 20352 half-shell points. Additional independent finite graded Cauchy replay 840/840. These do not execute the Agda sources. |
| 78177f6ee69d | JInvariantBishopRectangleRowLimitAttachmentExact: actual finite list of row limits, max(n,m) schedule, exact rectangle-to-nested-row fold transport and cofinal limit consumer actualRowSum. It consumes individual row limits, not an assumed interchange or desired global identity. |

Geometry: for degree n>0, square-shell labels are actual signed integers, with zero unique; half-shell labels are actual signed odd parameters z mapped to 2z+1, with triangular grade j(j+1), j=z for z>=0 or j=-z-1 for z<0. The raw norm is exactly four times (sum of triangular grades + 1). Bounded lists are duplicate-free and complete on each grade; the odd-degree source retains a Boolean orientation tag. The forward map is injective on the actual odd-total source and has a constructive preimage for every target. Existing finite weighted reindex, list uniqueness, original rowZ, signed twist and Bishop readout owners are consumed. The even-degree half-shell is empty by norm parity. Thus the native intended terminal has no external Jacobi identity, count axiom, or finite diagnostic premise.

Remaining:
- GTheta1/GTheta2: source-written end-to-end; pinned Agda elaboration and kernel acceptance, including dependent with-abstraction, stdlib APIs, and solver performance. No new mathematical premise intended; do not call accepted until run.
- GTheta3: Lean theta-to-original-Eisenstein and analytic Jacobi are already source-written. Native Bishop original normalized E4/E6 identity is still genuinely required; choose the actual lattice Fourier route or native theta coefficient/uniqueness attachment.
- C1b: actual finite rectangle fold/limit consumer now written. Attach individual normalized positive rows to signed symmetric row prefixes (including zero endpoint and negative reflection), then absolute Lambert degree-fibre regrouping and native normalized E4/E6. The generic finite limit consumer does not supply the remaining row witnesses.
- C1c Hecke41 product/pole removal, C2 original diagonal zero, C3 original ray residual, H1 final coefficient grouping and RawCross/GMP acceptance remain. No change to these downstream lanes or Lean branch in this cut.

Classical Jacobi and Hadamard identities retain historical attribution; the DASHI contribution is the explicit integral signed source-specific permutation and attachment. All committed proofs remain uncompiled. No postulates, holes or termination overrides intentionally introduced by these new modules; transitive axioms audit and native acceptance still required.


### 2026-11-28 — original Bishop lattice/Fourier same-object cut

SOURCE-WRITTEN, KERNEL PENDING. Supersedes the missing-producer inventory for C1b and the lattice route of GTheta3. No new local axiom, desired Fourier identity argument, or infinite-interchange argument is introduced by the intended terminal. Native Agda acceptance and pinned API/elaboration repairs remain required.

| Commit | Native construction |
|---|---|
| db664c1322a3 | JInvariantBishopSymmetricRowChartExact: literal signed-coordinate decoder permutation, centered interval plus endpoint, positive pair readout, reflection permutation. |
| 7fd3a86a3c94 | JInvariantBishopRowEndpointNullExact: exposed endpoint dominated by the existing absolute shell, with eventual-null and centered-to-symmetric limit transport. |
| b8140e8c06c1 | JInvariantBishopEvenLatticeReflectionExact: actual simultaneous lattice negation and even reciprocal-power equality, including puncture. |
| 8a0043ae06cf | JInvariantBishopAxisRowExact: actual zero-horizontal row, zero at origin and twice the original even zeta limit. |
| c80cedba1f57 | JInvariantBishopAllLatticeRowsExact: positive, negative and zero rows consumed by the existing rectangle limit; actual G4Rows/G6Rows with axis plus twice positive row prefix. |
| fe89a202da83 | JInvariantBishopLambertDegreeChartExact: literal positive factor-pair keys, unique triangle and rectangle lists, exact cofinal inclusions. |
| d91bbe085c6a | JInvariantBishopLambertCofinalRegroupExact: finite majorized difference, sandwich, modulus-level cofinal limit, row-limit attachment. |
| adee37060c4c | JInvariantBishopLambertSeriesRegroupExact: actual complex pair term, positive degree majorant, exact divisor-fibre readout, q^(md) via existing phase power, actual individual row convergence and degree-to-row compiler. |
| 2a27e7a1ed9a | JInvariantBishopLatticeFourierSameObjectExact: instantiate weight 4/6 degree and majorant convergence from original series; attach positive-row values, original zeta and Machin pi inverse normalization; intended same4/same6, qE4S/T and qE6S/T terminals. |
| a5ba294dcb08 | scripts/check_paper9_signed_rows_lambert_cofinal.py: independent local exact rational/SymPy replay: 195 signed chart, 4 symbolic reflection, 2178 inclusion, 544 fibre/tail and 2 normalization checks PASS. Not Agda execution. |

The decisive cofinal geometry is triangle(n) ⊆ rectangle(n,max(n,m)) ⊆ triangle(n*max(n,m)); for any retained positive pair degree is m*d. Both real and imaginary signed differences are bounded by the positive degree-majorant tail, independently of the vertical cutoff. The actual E4/E6 degree budgets are supplied by the pre-existing polynomial-geometric majorants, not a newly assumed absolute double-series interchange. The weight-six minus sign is retained separately from the unsigned positive majorant. Normalization uses 2*zeta(4)=pi^4/45 and 2*zeta(6)=2*pi^6/945 on the original Machin object.

Current next cut: use the native qE4S/T and qE6S/T source terminals in the original j/modular transport, then degree-41 Hecke product, pole removal, diagonal and ray residual. GTheta3 direct native analytic theta-to-Eisenstein equality is not asserted; the alternative original lattice/Fourier route is now source-written. Existing Lean theta modular uniqueness is untouched. C2/C3/H1/RawCross/GMP and kernel acceptance remain outstanding. Static delimiter scan of all nine new Agda modules passed; no explicit holes, postulates or termination overrides found in these new files. This is not a typecheck or a transitive axiom audit. Agda and Lean unavailable in local runtime; no CI invoked.


### 2026-11-28 — native homogeneous j, Hecke chart/product and selected fixed-point weld

SOURCE-WRITTEN, KERNEL PENDING. Starting PR head 4af3b8cff082. This cut reuses the actual normalized Bishop q-series S/T endpoints, original Fin42 classical correspondence, literal integral generator correction tables and selected CM disk guard. No new local axiom or termination override intended.

| Commit | Native construction |
|---|---|
| 4862422a36c9 | JInvariantBishopHomogeneousKleinTransportExact: numerator and normalized Delta weight-12 transformation, nonzero-scale guard transport, reciprocal uniqueness and guarded quotient S/T invariance; no E4 nonzero requirement. |
| d045e5ac1513 | CM163Hecke41CorrectionWordsExact: exact SL2Z words for all original 84 corrections (not a PSL sign quotient), with literal matrix equalities. |
| a781f9ae40c8 | JInvariantBishopDiskSetoidTransportExact: original disk series extensional in q across radius and convergence witnesses, actual phase congruence and guarded j congruence. |
| 6d346b0df927 | CM163BishopHecke41ProjectiveRowsExact: original row evaluation, nonzero homogeneous scale composition, generator/word readout, point equality by cancellation. |
| 1f1b5feda459 | CM163BishopHecke41AnalyticChartsExact: actual affine charts, existing S/T correction equality, projective comparison and j chart transport on guarded domain. |
| 27f3e314ea8a | CM163BishopHecke41ProductExact: original foldFin product, exact permutation transport, fixed slice and diagonal invariance on guarded domain, homogeneous diagonal factor and zeroAt consumer. |
| 6ebd77ab75ab | CM163BishopHecke41SelectedFixedChartsExact: original Machin q phase to selected disk, guard transport, two actual reciprocal fixed chart identities and unconditional-on-other-chart-guards clearedDiagonalZero; quotientDiagonalZero consumes AllGuards. |
| dd4943d665fc | scripts/check_paper9_hecke_native_projective.py: independent exact local SymPy 1.14 reference replay, 252 integer determinant/edge/word checks, 5 homogeneous algebra checks and 5 CM quadratic/fixed-chart checks, plus 2 permutation and 2 integer product assertions. Not an Agda execution. |

The original CM point satisfies tau^2+tau+41=0. Thus A_1 tau=S tau and A_0 tau=S(T tau); both obtain the original j value by native modular transport and selected guard. No need to invert the other 40 factors to prove the cleared diagonal zero. This does not yet identify that cleared diagonal or the quotient product with the integer class polynomial. Fixed-chart zero and polynomial diagonal zero are separate facts.

Re-audit of original nonvanishing donors: DeltaNormalizedWeight12SameObjectExact has generic normalization and eta24 transport and records the pinned Lean eta24 same-object theorem, not a native Bishop inhabitant. IbrahimDedekindEtaDeltaJNonvanishingSnowballExact and IbrahimDeltaRedirectWeierstrassEllipticLatticeSnowballExact are typed source/availability frontiers, not concrete native global guard proofs. LeanDeltaFinalMinCutParityExact is an older conditional parity receipt; no automatic proof import. Keep the pinned Lean analytic product/nonvanishing and weight-zero rigidity donors for the next native cut. Do not repeat the already-paid quotient algebra or finite chart correction geometry.

Revised max-cut:
- C1b original Eisenstein modular transport: source-written, kernel pending.
- C1c native j numerator/denominator covariance, guarded chart/product S/T invariance, selected fixed chart and cleared diagonal zero: source-written. Remaining global literal Delta apartness (eta product same-object, or quantitative fundamental-domain guard and constructive orbit reduction), native holomorphic residual pole-removal/weight-zero rigidity, analytic ramified coefficient reflection for the original diagonal and fixed slice. Lean donor already has source-written product/remainder/rigidity consumers, with finite coefficient premises still unpaid.
- C2 integer polynomial diagonal evaluated at selected original j: open, not implied by the homogeneous fixed factor alone. Use existing original packet shift, root enclosure and native terminal after product-to-polynomial equality.
- C3 ray residual: open; keep original signed jet and two reciprocal multipliers, no replacement derivative carrier.
- H1 final coefficient grouping, RawCross/GMP, all native acceptance: unchanged. No CI. Agda/Lean absent locally. Static delimiter/no-hole/no-local-postulate/no-termination-override scan passed for the seven new Agda modules; actual committed 84 correction words were independently parsed and multiplied back to the actual original table. This is not a typecheck or a transitive axiom audit. Long literal correction words (max 692 generators) may require elaboration/performance repair.

Attribution: classical modular and Hecke geometry remains classical; the existing Diamond–Shurman, Broeker–Lauter–Sutherland, Serre, Miyake and Apostol source attribution retained. DASHI contribution is the explicit same-carrier homogeneous/correction transport and source-specific attachment. No Lean branch change in this cut.


### 2026-11-28 — recover native Ramanujan and construct global Delta apartness via reciprocal Euler recurrence

SOURCE-WRITTEN, KERNEL PENDING. Starting head 283e0213c83f. Correct the earlier H1 inventory: FiniteDivisorConvolutionSigmaFoldExact (groupGrade, factorPower, fibrePower, omegaPower), FiniteDivisorConvolutionRamanujanIntegerExact (c11, c13, c33, sigma7, c15Scaled, convSym), and JInvariantBishopLiteralRamanujanExact (ramanujanE/X/Y) already supply explicit native all-index signed coefficient proof bodies. JInvariantBishopCM163HyperMajorantsExact.rawFromCM already consumes those, and JInvariantBishopCM163LiteralTerminalExact.allRawFromDiagonalAndRay consumes the actual diagonal and ray inputs. H1 was not an unwritten producer. Kernel acceptance is still separate.

| Commit | Source implementation |
|---|---|
| 264715fd513c / a7408c97e0ae | JInvariantBishopRamanujanDeltaUnitExact: actual literal Ramanujan coefficient and Euler Leibniz transport to DDelta=E2*Delta, normalized shift U=Delta/q, inverse formal geometric series V, U*V=1, positive/negative Euler flows and normalized recurrence uniqueness, literal Junit=X^3*V. |
| 4511988868f6 / e2e5eb3f830b | JInvariantBishopEulerRecurrenceRadiusBoundExact: finite absolute-prefix mass majorant, Cauchy row uniform bound, Archimedean threshold induction for both normalized recurrence directions. |
| bd855c52b9cc | scripts/check_paper9_ramanujan_delta_unit.py: independently executed exact integer/rational/SymPy replay, committed blob 656e721154cca6d1ab556b34847c4ca271be0134 equals local git hash. 1542 Ramanujan, 514 divisibility, 514 Delta flow, 1024 normalized recurrence, 2052 independent Euler-product/inverse/J relations, 6152 rational radius controls and 1 symbolic flow check: 11799 counted PASS. Not native execution. |
| a4c0d2aabc46 / c21a9f7c6bea | JInvariantBishopRamanujanDeltaDiskConvergenceExact: original sigma1 quadratic bound, existing polynomial-geometric majorant, pinned Bishop Archimedean witness, larger radius interpolation and geometric absolute convergence of both U and V on every original unit disk. |
| f9ed9e299784 | JInvariantBishopRamanujanComplexReadoutExact: real-coefficient complex weighted Cauchy row attachment, absolute series multiplication/subtraction, normalized constants and monomial readouts on original complex carrier. |
| 79f937de8ad9 | JInvariantBishopRamanujanDeltaNonvanishingExact: inverse product norm-square positive witness, actual E4/E6 discriminant readout, U*V=1, Delta=q*U, normalized Junit=q*j, globalGuard on original Machin phase, allGuards on original Hecke charts, unconditional-on-external-guards productS/T, diagonalS/T and selectedDiagonalZero. |

Exact geometric bound: let 0<=r<rho<1 and let B be the positive convergent majorant mass of 24*(n+1)^2*rho^(n+1). Choose M with M+1>=B using the existing Bishop Archimedean witness. For either signed normalized recurrence f, take C_f=sum_{k=0}^M |f_k| rho^k. Strong induction at n>M gives n |f_n| rho^n <= B C_f <= n C_f, hence |f_n| r^n <= C_f*(r/rho)^n on every degree. The source intends absolute convergence of both formal reciprocal directions; original Cauchy product reads U*V=1; Delta=q*U and original nonzero Machin q give global apartness without eta product identification, orbit reduction or external Delta nonzero premise. This is a source-written proof chain, not a kernel receipt. The finite check independently compares Euler factors, not an assumed analytic Euler-product identity.

Revised max-cut:
- H1 already source-written in existing literal Ramanujan producer; do not recreate. H2-H4 native CM/RawCross consumer remains conditional on actual selected polynomial diagonal and ray residual; no new missing grouping premise.
- C1c global literal discriminant apartness, original normalized J series, quotient Hecke product and selected product diagonal zero: now source-written. Remaining native holomorphic pole-removal/weight-zero rigidity and actual analytic-to-integer coefficient reflection for diagonal and fixed-slice products. The selected Hecke product zero is NOT the integer polynomial diagonal zero until the same-object polynomial weld is supplied.
- C2 actual integer polynomial diagonal at original j, C3 original ray residual, final native RawCross/GMP acceptance and kernel/transitive axiom audit remain. Reuse original packet, root enclosure, signed jet and existing Lean rigidity/coefficient donors.
- Five new Agda modules static delimiter/no explicit holes/postulates/termination override scan PASS; corrected natural addition namespace ambiguity. Agda/Lean not installed locally; no CI invoked. Source may require pinned API, elaboration and performance repairs. No Lean branch changes.

Attribution: classical Ramanujan differential equations, discriminant and Euler products remain classical. DASHI contribution here is the existing native signed divisor-shear coefficient route and its explicit same-carrier recurrence-bound, inverse-unit, complex evaluation and Hecke guard attachment.


### 2026-11-28 — actual ramified Hecke product and formal cyclotomic norm Euler weld

SOURCE-WRITTEN, KERNEL PENDING. Starting head 2d38dd5e44e8. Reopened existing native RamanujanDeltaUnit/DeltaNonvanishing, original Hecke Fin42 products, chart phase, actual Machin global sine sign, original literal packet/shift, and Lean Paper9HeckeProductAssembly, Paper9HeckePoleRemoval, Paper9ActualTaylorUnit, Paper9IntegerSectorWeld/FiniteResidualCheck/ExecutableCM163, Paper9ActualCMRoot/ActualCross and Paper9NativeFiniteAcceptance. The Lean eight by-decide gates and universalRawCross already have source bodies; no duplicate Lean carrier or new acceptance premise. H1 remains existing source, not an unwritten producer.

| Commit | Native implementation |
|---|---|
| ed896ad5aad5 | CM163BishopHecke41RamifiedPhaseExact: actual Machin phase t=q(tau/41), zeta=exp(2*pi*i/41), integer exp-power, zeta^41=1, t^41=q, finite chart q=zeta^k*t, infinity chart q=q^41 and every finite chart q_i^41=q. |
| cbd79fd262b9 | CM163BishopHeckeProductAlgebraExact: original foldFin product distributivity, last chart split, phase exponent sum 820=41*20, odd sign normalization. |
| baf5af0a16d5 | CM163BishopHecke41NormalizedProductExact: actual normalized J=q*j readout on each original guarded chart; all 42 factors split; diagonalQ/diagonalT and sliceQ/sliceT with exact powers 82/3362 and 42/1722 and both minus signs. |
| 948e50feaaa6 | CM163BishopHecke41PrimitivePhaseExact: forty actual nontrivial phase-gap apartness witnesses, via existing Bishop Machin global sine sign and pi shift. For k=1..20, 2k/41 in (0,1); for k=21..40, (2k-41)/41 in (0,1) and the sign is reversed. No decimal approximation or primitive-root premise. |
| 897c0a2d4446 | CM163BishopHecke41SectorFilterExact: all-degree mod41 power reduction, primitive residue gap, geometric telescoping, rootTraceZero and coefficient sector cancellation. |
| 40381ef3a44b | scripts/check_paper9_native_ramified_sector.py: executed twice using exact original GMP helper. Local/remote script blob 6288189a50d9f08d5917ccf0fcf9923ddbaf0780; helper blob 95012a4dfa03de5c2eab49c42123b29f1f8f9c74 matches final local replay. PASS 3363 trace sectors, 40 primitive algebra checks, 40 signed rational angles, 3323 normalized discriminant and J coefficient pairs, 3363+1723 Euler residuals, 83+43 norm coefficients, 83+43 descending column coefficients. Regenerated exact original signed-hex 126 coefficient packet blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4; both shifted constant/linear zeros, nonzero slice quadratic, half-unit dominance, quadratic 41*p2=163*s2 and original signed cubic jet PASS. This is independent finite arithmetic execution, not a native proof or analytic equality. |
| 871d2283bdba | CM163BishopHecke41FormalCyclotomicNormExact: actual componentwise complex Cauchy product, sum-of-products readout, commutativity/associativity/unit proofs via the existing real formal ring solver, rotation endomorphism twistMul, cyclic first/last factor rotation rotateNorm, all-index covariance and offSector. No external covariance premise for the formal norm. |
| a98de1312b43 | CM163BishopHecke41FormalNormEulerExact: real formal inverse from existing geometric construction, literal logarithmic derivative, complex Euler Leibniz and twist commutation, finite normFlow, actualNormFlow and exact finite traceRead/traceOffSector. |
| ea34147209ff | CM163BishopHecke41LiteralNormalizedCoefficientsExact: literal Junit, degree-41 expand, shifts 40/1640/1681, actual hDiag/hSlice and gDiag/gSlice, both actual norm Euler identities and off-sector proofs, literal normalized Horner column and residual definitions using original Packet.diagonal/slice. |

Geometry: q=t^41, H_d(t)=J(t^41)-t^40 J(t), H_s(t)=J(t)-K t. Diagonal normalization is q^82 F_tau(j(tau))=(q^40 J(q)-J(q^41))*prod_k H_d(zeta^k t). Fixed slice normalization is q^42 F_tau(K)=(J(q^41)-K q^41)*prod_k H_s(zeta^k t). The actual chart normalization proof uses Jvalue at original chart points. Its identification with evaluation of the new literal formal complex coefficient series is still unpaid. In the formal Cauchy ring, rotation is a multiplicative endomorphism and shifts all 41 factors; the last factor wraps to the first. Primitive apartness then cancels every nonzero residue coefficient of the cyclic norm. For each real unit h, the literal log derivative L=(D h)*inverse(h) is defined without analytic logarithm, and the formal norm obeys D Norm=(sum_k twist(zeta^k,L))*Norm. Off-sector trace vanishes via geometric telescoping. Actual hDiag/hSlice and their trace/norm flow are instantiated.

Revised native max-cut:
1. C1c original guarded products and ramified normalization, primitive phase and formal norm covariance/Euler trace: SOURCE-WRITTEN. Remaining finite coefficient weld: exact on-sector trace = 41*L_(41m), Cauchy grade restriction reindex and cancellation of 41, reduced recurrence uniqueness/actual integer packet prefix reflection (the entire independent finite replay now passes; not kernel evidence). Reuse finite divisor/grade and ring owners rather than rebuilding. Need actual literal Horner column normalization/evaluation, absolute sparse degree expansion and signed shift/phase coefficient evaluation, complex Cauchy product convergence on the actual ramified t disk, and cancellation of the first 3363/1723 coefficients as a continuous tail with explicit modulus. Native invariant weight-zero rigidity remains genuinely unpaid; Lean has its pinned analytic consumer and executable acceptance source. No claim that native rigidity follows from finite coefficients alone.
2. C2 actual integer polynomial diagonal at selected j; existing selected product zero, half-unit enclosure and packet dominance consumer already available, attach only after actual product-to-polynomial equality. C3 original signed ray residual remains; reuse original two fixed charts, exact shifted packet, original first/second quotient jets, and existing Lean symmetric actual cross/reciprocal disk derivative consumers. No independent derivative carrier.
3. H1-H4 and RawCross downstream original consumer remains as previous ledger; kernel replay, transitive axiom audit, GMP production acceptance pending. No CI invoked; Agda/Lean not installed locally. Eight new Agda modules passed static delimiter/no-explicit-hole/no-local-postulate/no-termination-override scan, not a parser/typecheck. All new source and earlier dependencies may require pinned stdlib, setoid elaboration and performance repairs.

Attribution: classical Hecke, Ramanujan, cyclotomic norm/log derivative and Machin identities remain classical. DASHI contribution is explicit native same-carrier ramified geometry, sign-based phase apartness, original Cauchy rotation and Euler/trace source attachment. The independent checker adapts the existing eight-predicate replay and existing GMP helper. No Lean branch change.


### 2026-11-28 — reduced real norm, exact integer prefix reflection and actual normalized complex series evaluation

SOURCE-WRITTEN, KERNEL PENDING. Parent 9ed193f8429a. Reuse BishopFiniteEvenOddCauchyReindexExact, BishopFinSumSeriesBridgeExact, finite Cauchy row/ring, literal Ramanujan D1Meaning/actualX/actualY, original Euler uniqueness, integer rowEmbed, native literal packet and existing Lean acceptance rather than duplicating them.

| Commit | New native source |
|---|---|
| 1f92c88d8811 | CM163BishopHecke41ReducedCauchyExact: stride block zero-skip, finite prefix reduction, exact 41m-41i=41(m-i), on-sector real and complex Cauchy reduction, inverse sparse reconstruction. |
| 4b19fb452931 | CM163BishopHecke41ReducedNormFlowExact: on-sector trace is 41 times actual L_(41m), original complex norm initial coefficient one, positive 41 cancellation, real and imaginary Euler flow, imaginary zero by existing Euler uniqueness, actual real norm uniqueness and sparse reconstruction. |
| 5adb362fac6c | CM163BishopHecke41IntegerPrefixCertificateExact: literal signed integer candidate U,J,L,N construction; native bounded decidable residual predicates (multiplication rather than unchecked divisions); original signed integer packets, depth 3322/3362/1722 and degree 82/42. |
| a7cb2f297ce0 | CM163BishopHecke41FinitePrefixReflectionExact: original integer rowEmbed, unit prefix uniqueness and Euler prefix uniqueness, signed E4^3-E6^2 normalization, J, L and reduced norm certificate reflection. |
| 6cfe3de3e25d | CM163BishopHecke41PacketPrefixWeldExact: exact original J-depth transports to both H streams, actual log and reduced norm prefix attachment; candidate initial norm coefficient established from builder head preservation rather than reducing all coefficients. |
| 135d00017946 | CM163BishopHecke41SparseRingExact: sparse subring closure, exact delay/monomial and power restriction. |
| a3d5ef836a4c | CM163BishopHecke41LiteralResidualReflectionExact: original normalized descending columns, denominator-one packet witnesses, actual infinity factors, integer product prefix and all off-sector zeros; diagonalZero/sliceZero through degrees 3362/1722 conditional only on the concrete finite gates. |
| 4afb24e2be1f | CM163BishopHecke41ConvergentSeriesExact: sparse absolute convergence and arbitrary-cutoff constructive modulus, complex coefficient Eval, product/phase evaluation, real coefficient embedding, delay and sparse expansion readout. |
| e47c7f3b1405 | CM163BishopHecke41ActualSeriesEvaluationExact: all 41 finite factors use the actual normalized J readout at the original chart, finite norm Cauchy evaluation and actual infinity factor; actualDiagonal/actualSlice bind convergent normalized series to the original guarded Hecke products with the exact t powers. |
| e5675b953a26 | CM163BishopHecke41NativeFiniteAcceptanceExact: separate intended local kernel gate entrypoint using from-yes on the three closed integer decisions. Not executed, not claimed as kernel acceptance. |

The reduced recurrence is m N_m=sum_{i=1}^m L_(41i) N_(m-i), N_0=1; the imaginary coefficients solve the same real linear recurrence with zero head and are therefore zero by the existing uniqueness theorem. Finite J reflection uses the original discriminant shift and unit product; L reflection uses the original H*L=D H product rather than a second inverse series. The actual packet residual proof reopens every ramified degree: multiples of 41 from the checked integer normalized column, all other residues by the native sparse-ring proof. Actual series evaluation uses the original 42 chart values, including all 41 signed phases, original q powers, and exact normalized infinity factor.

Execution: reran the EXISTING scripts/check_paper9_native_ramified_sector.py locally with timeout 90 in this turn. PASS 3363 trace sectors, 40 primitive and 40 signed-angle checks, 3323 normalized discriminant/J coefficient pairs, 3363/1723 Euler residuals, 83/43 norm and 83/43 column coefficients, exact original packet blob 17ed967d83d1aacafdb0f19d7bd81e6afc5887a4, shifted diagonal/slice, dominance, quadratic and signed cubic jet. Local Git hashes of replay and GMP helper match prior committed blobs 6288189a50d9f08d5917ccf0fcf9923ddbaf0780 and 95012a4dfa03de5c2eab49c42123b29f1f8f9c74. This repeats independent exact arithmetic verification, not execution of the new Agda definitions. No new detached script. Static delimiter/no-explicit-hole/no-local-postulate/no-termination-override checks passed for the first nine new modules. Agda and Lean executables unavailable; no CI. New proof bodies and previous imports may need API/elaboration/termination/performance repairs. The reference native list-based integer candidate builder is not optimized; large closed from-yes reductions may require verified efficient integer arrays or checkpointed proof reflection before kernel acceptance. No claims of native acceptance or theorem promotion.

Revised max-cut:
- C1c native actual formal cyclic norm, reduced real recurrence, finite integer packet residual reflection, actual normalized Hecke product convergent evaluation: source-written. The concrete finite gate entrypoint must be compiled and verified. Remaining analytic attachment: evaluate the original normalized descending column on the actual t phase, subtract its evaluation from the actual normalized product, factor the residual into t^(3363) or t^(1723) times an explicit continuous/bounded absolute tail at the cusp. Then use original nonzero t to cancel t^(3362)/t^(1722). Native invariant weight-zero rigidity still genuinely unpaid. Lean companion already owns pinned pole-removal and all eight finite-gate consumers; no changes there this cut.
- C2 selected actual integer diagonal and C3 signed ray residual remain open until the actual analytic product-to-packet equality, then reuse existing half-unit isolation, original selected fixed charts, signed jet and RawCross/GMP downstream consumers. No inference of analytic equality from finite matching alone.
- H1 remains existing Ramanujan source; final native kernel, transitive axiom audit, original RawCross/GMP production acceptance pending. Classical Hecke, Ramanujan, cyclotomic norm and Bishop convergence attribution preserved; DASHI contribution is explicit same-carrier coefficient/phase/finite residual weld.


### 2026-11-28 — literal normalized polynomial, uniform cusp factor and selected root weld

SOURCE-WRITTEN, KERNEL PENDING. Parent ad6c982d4bdf. Reopened existing literal packet shift/Horner/half-unit root, real-slice j, actual selected fixed chart, absolute Cauchy row, original real limit order and complex norm-square upper envelope owners. Rechecked Lean companion branch research/paper9-original-eisenstein-derivative-20261125 at 34bcc6055e7f198eae40605cf56a8f80bff97c15: Paper9HeckePoleRemoval owns jHolo, productHolo, invariantZero, tTendsto and both ramified replay consumers; Paper9ActualCross owns rest polynomial/slope, actualTZero and actualRawCross; Paper9NativeFiniteAcceptance has eight by-decide bodies and universalRawCross. No native Lean execution or cross-kernel authority promotion in this cut.

| Commit | Construction |
|---|---|
| 8760320428e3 | CM163BishopHecke41PolynomialEvaluationExact: actual complex normalized descending column, real coefficient addition and scalar/power evaluation, recursive homogeneous clearing q^d P(j)=sum c_k q^k J^(d-k), both literal t^3362/t^1722 column evaluations. |
| ece8c38cb727, f82bcfccd37a | CM163BishopHecke41CuspTailFactorExact: exact finite zero-prefix removal, absolute shifted series at the original nonzero phase, monomial padding Cauchy transport, same-series limit uniqueness and residual factor. Direct prefix-drop proof and pinned constant convergence API correction. |
| 21eaf30fdded | CM163BishopHecke41CuspResidualExact: actual diagonal/slice minus literal polynomial, absolute residual readout, exact t^3363/t^1723 factorization and cancellation of only original nonzero phase powers, S/T invariance of uncleared residual. Finite prefix gates remain explicit. |
| 8be7e609c6f6, 1ed0e42bf563 | CM163BishopHecke41UniformCuspBoundExact: choose the actual selected CM ramified phase as fixed reference r. Absolute component sums at r majorize both shifted tails at every t with normSq(t)<=normSq(r), via t/r in the closed unit disk, original norm-square upper power envelope and finite prefix/limit order. Evaluation at zero from the same shifted coefficients; no inverse of the variable cusp phase in the bound. Ordered-setoid direction review correction. |
| fd6c5d611c62 | CM163BishopHecke41CuspLimitExact: explicit zero-cusp sequential limit consumer from uniform residual bound and any sequence of actual ramified phases tending to zero within the fixed disk. |
| e45ffa92f9ff | CM163BishopHecke41SelectedRootWeldExact: original selected complex j equals real guarded j; literal complex polynomial read to original real descending Horner, existing selected fixed chart product zero, half-unit root isolation and RawCross consumer from selected residual equality and original signed ray. No new independent root assumption. |
| fc24d135eb0e | scripts/check_paper9_cusp_factor_geometry.py: executed locally under timeout 90; PASS 360 exact rational checks (40 Gaussian-rational homogeneous clearing through degrees 42/82, 120 finite zero-prefix and pole cancellation including 1722/3362, 200 closed reference disk component bounds). Local hash-object and committed blob both e323804a192b66c184cc20df9f815e14ffca4cd9. Independent regression, not actual packet re-execution or native proof. |

Exact residuals: R_d=F_tau(j)-P(j), R_s=F_tau(K)-S(j). Native source constructs, conditional on the concrete integer gates, t^(3362) R_d=t^(3363)G_d and t^(1722) R_s=t^(1723)G_s, then R_d=t G_d, R_s=t G_s. Each G is the original shifted coefficient stream. On the fixed disk the component bounds are |Re R|,|Im R| <= (|Re t|+|Im t|)*M, with M the sum of absolute real and imaginary reference coefficients. The cusp limit does not depend on any divergent variable reciprocal. At selected CM, R_d=0 implies the original real Horner polynomial vanishes, and the already-owned sharp half-unit enclosure/dominance produces the exact original CM root.

Remaining cut, re-audited:
- C1c native coefficient reflection, actual product and polynomial evaluation, uniform cusp residual bound and S/T transport are SOURCE-WRITTEN. Kernel acceptance of these and earlier modules is unpaid. Native holomorphy/complex differentiability of the actual absolute series and upper-half-plane charts, q-parameter cusp convergence/compact modular quotient or equivalent weight-zero rigidity remain genuinely unpaid. The new zeroAlong theorem is conditional on actual phase tending to zero in the reference disk; it is not an all-upper-half-plane equality. Master searches for maximum modulus, holomorphic/modularPolynomial/WeierstrassIsogeny/Vélu and valence formula did not identify a native theorem body supplying this endpoint; older geometric receipts are not proofs. Lean pinned analytic owner remains the alternate route, not an automatic Bishop theorem. Need native kernel check/axiom audit and exact same-object bridge if using Lean authority.
- C2 selected root consumer is now source-written from actual R_d(Fixed.p)=0; no outstanding separate root isolation or polynomial evaluation. Global identity remains the needed producer.
- C3 original signed ray remains open natively. Lean Paper9ActualCross supplies the rest-polynomial/slope architecture. Reuse actual selected 2-chart reciprocal geometry, existing quotient first/second jets and original literal shifted coefficients rather than assuming the ray. The new selectedRoot allRaw consumes actual selected residual and OriginalRayResidual.
- H1 existing Ramanujan source; native RawCross/GMP production acceptance and transitive axiom audit pending. No CI used. Agda/Lean unavailable locally. Six new modules passed static delimiter/no-explicit-hole/no-local-postulate/no-termination-override scan; not typechecking. All new and old sources may need elaboration, API, termination and efficiency repair. Classical Hecke, Ramanujan, complex series, cusp rigidity and Horner attribution retained; DASHI contribution is explicit same-carrier finite/analytic coefficient and uniform cusp weld.


### 2026-11-28 — original complex cross, sequential signed jet, strict-disk actual j derivative

SOURCE-WRITTEN, KERNEL PENDING. Parent c3d29506de31. Reopened the native CM163ReciprocalGeometryExact (actual alpha,beta, N0/N1/M0/M1), CM163QuotientJetExact (original coefficient a,b), literal packet shift, finite complex power-difference/binomial, BishopUniformLimitSequentialContinuityExact, BishopDirichletUniformBaselTailsExact, actual polynomial-geometric summability and original dyadic squareQ owners. Lean Paper9ActualCross, Paper9ScalarCross and Paper9DiskGerm inspected at the existing branch, especially actualRawCross, normalizedActualCross, actualTZero, actualThreeBranches and actualDiskCorrection. No new duplicate abstract derivative authority.

| Commit | Native implementation |
|---|---|
| 5381255043a3 | CM163BishopHecke41ComplexPacketShiftExact: complex Horner/ascending packet shift, literal diagonal and slice double-zero factorization without dividing by the centered j. |
| 9212c783131b | CM163BishopHecke41ActualCrossExact: actual Fin42 product, first two reciprocal branches, forty-factor rest and telescoping slope, exact raw cross from actual residual vanishing; normalized cross cancels only w^4, not a colliding chart factor. |
| 99da3e6bc0a7 | CM163BishopHecke41UniformSeriesContinuityExact: arbitrary summable budget uniform tail-to-limit cutoff, sequence-indexed three-leg convergence, actual finite complex prefix and same-reference disk continuity, including origin. |
| 31fcf030bfcd | CM163BishopHecke41SequentialJetExact: division-free sequential factor jet, continuity, add/sub/mul/coordinate rules, exact derivative uniqueness by nonzero coordinate cancellation, literal ascending polynomial jet. |
| 6e4e52528d1c, 97a91f71f17f | CM163BishopHecke41SignedRayExtractionExact: original reciprocal N/M coefficients, literal complement jets, w*T continuity-only jet, actual normalized cross first coefficient equals literalResidual at original QJ.a,QJ.b. Explicit actual branch germ and center slope inputs remain. Corrected scalar solver grouping. |
| 1737c6f50ef6 | CM163BishopHecke41RestSlopeLimitExact: finite rest/slope continuity, exact center coefficient extraction from reverse fixed-slice values along a nonzero null sequence. No derivative of the forty factors. Reverse fixed-slice producer is not assumed closed. |
| 774d1d938a1b, 33b37c3b02db, e4be1963c927 | CM163BishopHecke41PowerDifferenceSeriesExact: finite telescoping power wing Q_n(u,v), exact increment, component bound 2n on closed unit disk, summable first-moment quotient series, uniform quotient continuity, actual same-series increment factor and diagonal derivative coefficient readout n f_n u^(n-1). |
| ee96535a4353, 43580123c922 | CM163BishopHecke41StrictDiskDerivativeExact: construct first coefficient moment by strict inner/outer phase contraction and existing polynomial-geometric summability; original coordinate derivative factor and quotient limit. Pinned nonnegative API correction. |
| 77df42893af6 | CM163BishopHecke41ActualJLocalDerivativeExact: actual dyadic reference around each original point using inner=q(tau/2), outer=q(tau/4), outer^2=inner and inner^2=q; native relative norm envelope and original J=q*j readout, guarded j increment/quotient limit and continuity for sequences in the inner disk. Actual first derivative in q coordinate source-written, not global upper-half-plane holomorphy. |
| 4ea4dcd75916 | scripts/check_paper9_cross_derivative_geometry.py: local timeout 90 execution PASS 550 checks (24 complex Horner shifts, 80 cross, 80 slope, 180 power-wing, 120 derivative, 60 moment, six symbolic reciprocal/signed residual). Local and committed Git blob both 9c06d5778a981d9b850a058413d70264aa620e46. Independent finite regression, not native execution and not a replay of actual packet certificates. |
| 5637ea22afff | Paper9ExactCMModularJetCertificates.md updated with latest native and Lean source states, superseding stale H1 inventory; no theorem promotion. |

Revised max-cut: original C1 actual residual identities remain the substantive global gate, now with same-carrier actual q-series local factor derivative and uniform cusp bound source-written. Need prove actual exp phase local differentiation/composition and upper-half-plane chart continuity, attach strict interior sequence admission, global native compact fundamental-domain/weight-zero maximum principle (or an equivalent genuine theorem), and phase cusp approach. Existing Lean Mathlib rigidity is separate authority, not an automatic Bishop proof. C2 selected-root consumer already source-written. C3 actual finite normalized cross, first-jet coefficient extraction, continuity-only rest slope and center slope consumer are now source-written. Remaining producer is reverse fixed-slice symmetry (construct the full degree-42 correspondence polynomial, e.g. via generic fixed-Y principal part and 43-point interpolation then reverse root duality and distinctness; or reuse/attach original Lean symmetry with exact carrier bridge). Also pay actual second derivative and q-to-reciprocal-disk normalized germs: diagonal quotient coefficients -> original Euler jets, quotient second jet, actual exp and disk pullback, alpha/beta branch transport on the original chart. Use existing reciprocal geometry, QJ, original selected root and literal packet; do not rebuild these or add arbitrary A,B. Actual rest slope continuity can consume chart continuity; no forty-factor derivative. Native kernel acceptance, transitive axiom audit, finite certificate performance and original RawCross/GMP production acceptance remain. No CI invoked. Local Agda/Lean unavailable. Nine new modules passed static delimiter/no-explicit-hole/no-local-postulate/no-termination-override scan at reviewed versions (not a parser/typecheck); new and earlier proof sources may need pinned API, elaboration, termination and performance repair. Classical attribution retained.


### 2026-11-28 — full bivariate prime-41 coefficient symmetry and actual complex phase second jet

SOURCE-WRITTEN, KERNEL PENDING. Parent 28cb9ec858b4. Reopened existing original normalized Hecke product (already parameterized by arbitrary complex Y), literal fixed-slice formal norm/Euler owner, actual series evaluation, integer prefix checker, selected reciprocal fixed charts, rest-slope limit, original complex origin quadratic remainder and original exp factorial/native weld. Do not rebuild the 42 chart geometry or treat analytic symmetry as an independent premise.

| Commit | Construction |
|---|---|
| b4d6d41e0360, bdaa38f1e33b, 8fe5cae4d6ed | scripts/paper9_hecke_packed_mul.cpp and check_paper9_full_hecke_symmetry.py: full prime-41 43-by-43 integer coefficient matrix from original J recurrence, positive Kronecker packed convolution, exact cyclic trace/Newton elementary recurrence, infinity chart and triangular monic principal-part extraction. |
| 042cfba28ba4 | CM163Hecke41FullIntegerMatrixExact: native integer candidate, trace/Newton recurrence, separately accounted e41 negative mode, full normalized q^42 columns, triangular extraction, Newton/column/symmetry/original packet gates. Native gate inhabitation and efficient evaluation remain pending. |
| 9d7e302e31a6, 85d3c8d2bc79 | CM163BishopHecke41ComplexExpSecondJetExact: original factorial coefficient stream, actual absolute unit-disk reference, shifted second tail, exact exp(z)=1+z+z^2 R(z), uniform sequential R(z)->1/2 from same original coefficients; normalized slope jet. Shifted-prefix and norm-square assembly correction. |
| 0a411c55938d, 49026796ceea | CM163BishopHecke41ArbitrarySliceSeriesExact: general real Y specialization of actual normalized cyclic norm and infinity factor, original chart J values, existing reduced norm Euler machinery, finite residual tail factor from its own 1722 zero prefix. Corrected unit owner and normalized series signature. |
| fac82cec1d42, befef1b06332 | CM163BishopHecke41MatrixSymmetryExact: finite sum Fubini, matrix symmetry from bounded integer equality gate, literal slice readout, actual reverse selected slice from common FullIdentity, selected chart guard congruence, cancellation of only the nonzero test coordinate squared, original S3 center-slope consumer from nonzero real null samples. |
| fadc82562277 | CM163BishopHecke41SecondJetCalculusExact: nested division-free first-quotient jets, exact scale/add/sub/mul, reparam and chain rule, actual complex exponential and original phase q two-jet along actual exponent increments. |
| 04c676ecf87f | Paper 9 draft updated with exact finite verification and remaining analytic boundaries. |

Execution receipt: initial pure Python packed multiplication attempt timed out at 90 s. Exact GMP-backed implementation completed in 2.54 s under timeout 90. PASS 1722 Newton exact divisions, 1849 symmetry comparisons, 126 original diagonal/slice coefficients via SHA-256 digest comparison, degree 82 diagonal, original signed CM ratios. Local script Git blob 3f7b41b7521e7d519b30da60741c0a2dfa116d72 and helper 30bd71e5f93e1fa3ede0a85ca36f7342c7f0660e match exact committed blobs. Original packet blob eb41e2c937d89dfb8cf2f90d1f31e69b945ad5e0 retrieved via GitHub connector; independently computed SHA-256 of comma-separated signed decimal coefficient streams: diagonal 85132a72355a35b15add35de7941526ef7800f3fdb3daf22559b354343f263f9 and slice 3391a057a0fe7f6f6ff9151e6fbc5e826d7e3be89776145c2e58d21857b4ea96. Local replay used --digest-only; direct file comparison is the default repo checkout mode, not executed locally. Full candidate matrix digest (ascending row-major) a00e5f1bab9bf4efb1580e58957650daa87dea09f8c01d285c09f78d703dcc8b. Hashes are regression receipts only; native theorem consumers require exact equality proof gates.

Revised critical path: C1 full arbitrary real-specialization actual convergent normalized product source is written; build the coefficient reflection from Newton or the existing norm Euler recurrence over the polynomial parameter (or 43 distinct integer specializations with exact finite interpolation), and attach the full principal-part residual to native cusp removal and weight-zero rigidity. This single actual product identity also pays reverse fixed slice via finite matrix symmetry, without a separate analytic generic-distinctness/symmetry theorem. C2 original selected root consumer unchanged. C3 reverse fixed-slice complement and S3 center-slope consumer source-written conditional on common full identity, finite exact symmetry/slice gates, actual selected root and nonzero null test sequence. Actual exp second jet and original q phase source-written; remaining actual second-order J/j series divided differences with summable second moment, identification with original Euler a,b, reciprocal disk inverse/chart and branch transport, strict disk admission and actual slope continuity. Native global compact quotient/weight-zero rigidity and kernel acceptance still open. Five new modules passed static delimiter/no-explicit-hole/no-local-postulate/no-termination-override scans at reviewed versions; not parser/typecheck. No Agda/Lean available locally, no GitHub CI. Source may need API, elaboration, termination and efficiency repairs. Classical Hecke, Newton, exponential and modular theory attribution retained. No full native period/GMP endpoint assertion.


### 2026-11-28 — outstanding-producer reconciliation (read-only source audit, no kernel execution)

Audited PR #1546 at f2cf029028e8 against current master fad22a838ab8 (638 ahead, 74 behind; reverse compare 55 files, none in Moonshine/Bishop/Paper9 paths) and Lean branch research/paper9-original-eisenstein-derivative-20261125 at 34bcc6055e7f. Historical PR #1529 remains open at d8956bb9ba27; historical directory enumeration was capped, so no exhaustive historical absence claim. No new theorem or local numerical run in this audit.

* Native original Euler jets are NOT missing: JInvariantBishopEisensteinEulerJetExact.AtDisk supplies arbitrary degree e4/e6 weighted absolute convergence and readouts; JInvariantBishopCM163QuotientJetExact supplies actual selected coefficients a,b with q0/q1/q2 and first/second. Remaining same-carrier analytic weld is identification of the nested incremental quotients with these existing weighted readouts (including factorial 1/2 in the second Taylor coefficient), not a new derivative-coefficient stream. Use the existing strict disk power-wing and original Euler weighted majorants rather than reconstructing the quotient algebra.
* Native reciprocal geometry is NOT missing: JInvariantBishopCM163ReciprocalGeometryExact already gives cmQuadratic, reciprocalMultipliers, multiplierTrace, forwardFixed/reverseFixed, forwardDiskCleared/reverseDiskCleared and N0/N1/M0/M1. The remaining pullback is guarded undisk admission and composition with the actual analytic two-jet. In the original convention p=MachinPi*sqrt(163), A=-2*p*a and B=A+2*p^2*b. The signed ray extraction and literal terminal are existing conditional consumers.
* Native finite diagonal/fixed-slice reflection and cusp limits are NOT missing as proof source: CM163BishopHecke41NativeFiniteAcceptanceExact already defines unitChecked, diagonalChecked, sliceChecked and both residual prefix zero theorems; CM163BishopHecke41CuspLimitExact has diagonalZeroAlong/sliceZeroAlong. Keep the exact zero-phase convergence premise and native kernel boundary. Do not regenerate these finite packets. Full matrix extension only needs all-column reflection/attachment; the matrix symmetry consumer still requires exact SliceGate (reflect PacketGate including finite sum reindex and integral rational embedding). A possible smaller route is arbitrary-specialization unit-pivot elimination plus source symmetry, as the Lean route below demonstrates; full 43-by-43 matrix is an independent finite certificate, not a necessary new analytic construction.
* Lean already has the full alternative analytic source route: Paper9ActualJSourceJet.jQEuler/jExtDeriv/jFirstDeriv/jExtSecond, Paper9OriginalCMChartWeld.centeredJTaylor, Paper9DiskGeometry.diskTauLocal/forwardUndisk/reverseUndisk, Paper9DiskGerm.actualNormalizedGerm/actualThreeBranches/chartContinuous/actualDiskCorrection; Paper9UniversalMonicSlice.triangularExist/existsSliceCoefficients/universalSliceEval/universalSliceLead/symmetryFromSeparatedImage and Paper9SeparatedCusp.actualSymmetry; Paper9ActualCross.sliceIsCMRootPoly/sliceShiftIsRest/actualTZero; MoonshineLevelOneWeightZeroPinned.levelOne_weight_zero_const and Paper9HeckePoleRemoval.invariantZero/normalizedResidualZero/diagonalFromRamifiedReplay/sliceFromRamifiedReplay. Do not list any of these as missing Lean implementations. They are source-written, not verified here. Lean Paper9NativeFiniteAcceptance.universalRawCross and Paper9GMPWindowAcceptance.actualPrefixLimit/gmpWindow/floorFromRaw already exist; first priority is actual kernel acceptance and transitive axiom audit, not another proof architecture.
* Genuine native global mathematical gate remains a constructive same-carrier weight-zero rigidity theorem or an explicit verified semantic bridge to the pinned Lean result. Master JInvariantKleinConstructionGluingBidiExact explicitly lists missingAnalyticFundamentalDomainCarrier and is a boundary ledger, not such a theorem; principal strip modulus is not compact quotient rigidity. Native cusp transport, strict local admission and original exponential/series analytic attachment must feed the actual theorem. Neither finite residual checks nor matrix symmetry alone imply global analytic equality.
* Implementation order: (1) accept/repair existing Lean endpoint DAG and native modules on pinned kernels when available; (2) native actual Euler increment coefficient identification + guarded reciprocal disk composition, using existing owners; (3) native arbitrary specialization reflection and constructive rigidity or verified carrier bridge, then select existing reverse-slice/center slope and root consumers; (4) original signed residual -> allRawFromDiagonalAndRay -> existing period/RawCross/GMP. Keep prior local arithmetic receipts distinct from native acceptance. Do not claim final proofs or no axioms from textual scans. No GitHub CI.


### 2026-11-28 — second divided-difference actual limit and relaxed modular reduction

Source-written, kernel pending. Starting head e6a0de7c21e6. No CI. Reused original PowerDifferenceSeriesExact, StrictDiskDerivativeExact, UniformSeriesContinuityExact, SequentialJetExact, SecondJetCalculusExact and original Bishop polynomial-geometric convergence. No replacement carrier.

| Commit | Construction |
|---|---|
| 444058a0f5e4 | CM163BishopHecke41SecondPowerWingExact: T_0=0, T_(n+1)=Q_n(v,w)+u*T_n; exact Q difference factor, equivalent retained-index monomial wing, finite prefix and actual series limit factor, nested actual series Jet2 constructor. |
| 42f78657f06c | CM163BishopHecke41SecondPowerWingLimitExact: componentwise bound via recursive triangular budget B_0=0, B_(n+1)=4n+B_n; summable quadratic budget yields both absolute second-wing series and uniform sequential continuity, constructing the actual Jet2 with existing first-wing evaluation. |
| 755670dc8a2ac | scripts/check_paper9_second_wing_reduced_disk.py: exact finite SymPy/Fraction regression. |
| 7fc5315d90c0, ba0a9b1ae9a0 | CM163BishopHecke41StrictDiskSecondMomentExact: quadratic budget bounded by 2*n^2, degree-two polynomial-geometric shrink from the actual outer evaluation, same original normalized series, inverse-inner affine transport of the first and second coefficients back to the original q coordinate (second scales by inverse-inner squared). |

Local acceptance: timeout 90 python check_paper9_second_wing_reduced_disk.py completed in 2.70 s. 39 symbolic polynomial checks (factor, triangular monomial readout, diagonal binomial), 360 exact rational wing checks, 800 rational S/T reduction cases with determinant and actual Mobius endpoint checks, 300 exact rational Poisson lower-bound cases, 30 symbolic disk-phase Euler coefficients; 1529/1529 PASS. Local git blob 320cd384f58b4daba5515b7bc89cca0dd037a15a equals committed blob. This is not native compilation or continuum acceptance. First two new native files passed delimiter/no-explicit-hole/no-local-postulate static scans; source may require API, elaboration, termination or performance repairs. Third module kernel pending.

Corrected second-jet frontier: the second-wing factor, actual limit construction, quadratic-moment shrink, and normalized-to-original phase transport are now source-written. Remaining finite all-index diagonal identification in native carrier: T_n(u,u,u)=binom(n,2)u^(n-2), then shift the actual series and identify its q-coordinate first/second Taylor coefficients with original Euler a,b (Euler second = q^2 f''+q f'; do not confuse b with the Taylor coefficient). Attach original J=q*j quotient or original E4/Delta quotient with guarded reciprocal, actual exponential phase, and existing reciprocal disk pullback. Local finite diagonal checks are not the native equality.

#### Smaller native rigidity max-cut

Reopened actual Lean MoonshineLevelOneWeightZeroPinned.levelOne_weight_zero_const proof: it uses a reduction into Im>=1/2, q-radius exp(-pi), and disk maximum modulus, not an explicit full compact modular quotient construction. Preserve classical attribution. Native constructive alternative:

1. For a Bishop upper-half-plane point x+iy, approximate x to 1/10 and round the rational approximation to nearest integer k, so T^{-k} gives |x-k|<=3/5. Approximate y to 1/20; compare rational approximation to 11/20. The two overlapping branches certify either y>=1/2 (done) or y<=3/5 (invert). No exact real boundary comparison.
2. On inversion branch |z|^2<=18/25, and S:z -> -1/z gives y_new=y/|z|^2 >= (25/18)y. Keep the actual SL2Z word, determinant, positivity and invariant value. Construct finite fuel from a positive rational lower bound l<=y_initial: choose N with (1+7N/18)l>3/5; Bernoulli gives (25/18)^N l>= (1+7N/18)l. Thus the inversion branch cannot persist. Need native located approximants, actual S/T action and invariance, height-bound and fuel attachment; rational model regression is not a proof of this general step.
3. Use actual q chart and period/inverse-q admission, including the origin cusp extension. Radius r0=exp(-pi)<1; show every nonzero q in the unit disk is represented and invariant value is attained within the reduced disk. Do not confuse q^42-normalized residual with weight-zero residual after pole removal.
4. Choose r0<R<1. For the actual holomorphic residual F(q)=sum a_n q^n, construct M=sup_{|q|<=r0}|F(q)| via uniform series and finite nets (no selected exact maximum needed). Reduction supplies global bound M. On circle |zeta|=R, normalized Poisson kernel P_z >= c=(R-r0)/(R+r0)>0 for |z|<=r0. Poisson reproduces F(z), and the exact variance decomposition gives M^2-|F(z)|^2 = integral P_z (M^2-|F(zeta)|^2) + integral P_z |F(zeta)-F(z)|^2 >= c R^(2n)|a_n|^2 for every n>=1 by Fourier orthogonality. Near-supremum approximants force every nonconstant coefficient zero; existing cusp zero removes a_0. Need actual same-carrier Poisson reproduction and positive quadrature limit, circle Fourier orthogonality, located supremum and coefficient uniqueness. Existing finite Parseval donors NSTriadKNLuoTorusTrigonometricParsevalExact / NSTriadKNLuoFiniteParsevalExtractionExact are potential reuse, not continuum theorem admission. This route is classical analytic disk rigidity with constructive approximations, not a new claim of modular rigidity from finite data.

Continue two routes in parallel: native strict disk Euler identification -> actual original disk germ; native reduced-disk rigidity or verified Lean semantic bridge -> original Hecke identity and fixed-slice. Full matrix reflection, root/center slope consumers, signed residual -> original RawCross/GMP and both kernel acceptances remain P0. No theorem status promoted beyond source-written/finite local regression.


### 2026-11-28 — original Hecke reuse, second local j jet, full matrix specialization reflection

Starting ad1449e23b5d. Source-written, kernel pending. Reopened original classical prime-41 lattice specialization/generator transport and product/cusp residual owners, cyclotomic norm Euler and reduced norm recurrence, generic FinitePrefixReflection, PacketPrefixWeld and LiteralResidualReflection. Also reopened master P11AristotleHeckeCrossPollinationEverything, MatchedDihedralHeckeCrossPollinationEverything and DeltaAnalyticHeckeObservationSameObjectExact. Characteristic-11 Brandt/deck geometry, abstract correspondence congruence and selected tau(3^k) recurrence are distinct donors; not substitutes for the characteristic-zero analytic p=41 product. Do not rebuild S/T generator transport or cyclic norm.

| Commit | Implementation |
|---|---|
| 8516854f5038 | CM163BishopHecke41SecondWingDiagonalExact: all-index diagonal T_(n+2) is the triangular count 1+...+(n+1) times u^n, using original first-wing diagonal and scaleRight. Actual coefficient readout source-written. |
| de0dc8f2a053 | CM163BishopHecke41AffineQuotientJetExact: repeat the cleared quotient increment on the actual first slope, using guarded q only (not q-q0); nested two-jet with convergent inverse. |
| ef3e2089e41a | CM163BishopHecke41ActualJLocalSecondJetExact: consumes original dyadic inner/outer phase references, actual Junit evaluation and q*j=J; actual j two-jet along admitted null sequences. |
| ef1071af9dea | CM163BishopHecke41ArbitrarySliceResidualExact: general real parameter and degree-42 rational column; normalized t^1722 residual, original tail cancellation and uncleared S/T invariance. |
| a28e2151f587 | Exact local SymPy/Fraction regression, actual second-jet algebra and degree-42 parameter reconstruction/negative control. |
| 0cfb875c3764 | CM163BishopHecke41ActualJLogPhaseJetExact: compose existing actual q phase two-jet with actual j two-jet; first coefficient q*j1, second Taylor coefficient (q/2)*j1+q^2*j2. |
| bde6076450ad | CM163BishopHecke41IntegerSpecializationExact: exact descending 43-entry column of the SAME full candidate coefficient matrix at each integer y, matrix evaluation to polynomial equality, actual residual zero -> actual product equals matrix specialization. |
| 14ac5d3f0d30 | CM163BishopHecke41IntegerSpecializationReflectionExact: reuse the already generic Lit.At.reflectProduct, Ref.logRead, Ref.At.For.complexNormRead, Weld.normHead, Sparse restriction and original Cert.SectorGate. Arbitrary integer h=J-yt, g=expand(J)-y*q^41, candidateL 1722 and candidateN 42, exact Gate decision and zeroPrefix->poleRemoved proof source. No duplicate Hecke norm machinery. |

Local actual run: /usr/bin/time timeout 90 python check_paper9_actual_second_jet_hecke_parameter.py, 1.33 s, 1076/1076 PASS: 240 triangular binomial checks, 480 exact rational affine quotient/second factor checks, 240 Euler readouts including the Laurent exponent -1, 72 degree-42 interpolation probes at rational parameters including the signed CM center, 44 negative-control assertions (degree 43 vanishes at all 43 nodes but not at 43). Executed local Git blob ab95bc2924d99a0a707c18226b6859fa83b2a27e matches committed blob. These are finite regression checks on polynomial inputs; they are NOT replay of the 43x43 matrix, inhabitation of 43 SectorGate witnesses, analytic rigidity or native kernel execution. All seven new modules passed static parenthesis/no-explicit-hole/no-local-postulate scan; parser/elaboration/type/termination/transitive axiom and performance checks remain. Agda/Lean/lake unavailable locally, no GitHub CI.

Remaining exact analytic jets: actual guarded local j Taylor jet and log-phase composition now source-written. Identify the resulting q*j1 and 2*eulerTaylor2 with original selected real QuotientJetExact.a/b by actual E4/E6 Euler-stream and quotient readout, retaining all signs and the factor 1/2. Attach guarded actual undisk and branch transport (existing reciprocal Möbius geometry and signed residual consumers), not another derivative architecture. Strict disk membership of the actual sequence remains an explicit guard, not proved for every perturbation by this cut.

Remaining full Hecke route: use the SAME c (existing full candidate matrix with exact symmetry/packet gates) at y=0,...,42. Integer-specialization source now produces the precise exact per-parameter SectorGate and actual prefix reflection. Inhabit all 43 gates against the original J stream and actual candidate columns; the finite GMP reconstruction receipt is independent, not proof gate inhabitation. Need actual same-carrier reduced q-disk residual series, modular reduction, cusp extension, rigidity (or verified Lean bridge). Then each integer-specialization residual vanishes globally. Extend from 43 distinct integer nodes to every actual real parameter by degree <=42 polynomial interpolation: both the Hecke product (42 factors) and full matrix polynomial have degree <=42 in Y. Native interpolation theorem/attachment still open; the degree-43 negative control demonstrates why degree bound cannot be dropped. Direct real parameter reflection is an alternative, but a general real matrix column is not necessarily rational; do not silently instantiate the rational column interface with arbitrary real coefficients. The matrix reverse-slice consumer needs the all-real FullIdentity, not just equality at integer nodes.

Existing diagonal/fixed-slice route remains parallel: literal reflection, actual cusp tail and S/T invariance are source-written; same global rigidity gate shared. Existing Lean source route includes universalSliceEval, actualSymmetry, actualDiskCorrection, universalRawCross and gmpWindow; accept/repair existing DAG instead of duplicating. No terminal native signed jet/period/RawCross/GMP proof promoted. Classical Hecke, Fourier, divided differences, Taylor, Newton interpolation and CM attribution retained.


### 2026-11-28 — signed SSP/FRACDASH geometry of the degree-41 Hecke / 43-node parameter carrier

Starting 1e9ab252e134. Reopened master SSPRepresentationReductionRound9 (43 explicitly a non-Ogg control; five irreps of nine is distinct from the nine-cell permutation representation), HyperfabricPunctured27Projective13OrientationExact (26 <-> 13 x orientation), SSPPrimeLane369DepthWheelCantorBridge, SSPPrimeLaneSymmetryProfile, SSP15AffineC3TranslationExact, PolynomialVandermondeOrbitSignCharacterExact, SignedSSPProofCarryingExponentExact and FRACDASH master BRIDGE_CORRECTNESS.md (source -> signed IR -> paired-prime realization; require preserved observations, not a lossy quotient). The original 15 SSP/Ogg primes contain 41 but not 43. No exceptional prime classification is inferred. Projective ternary counts are (3^d-1)/2; retaining zero gives (3^d+1)/2, so 5 is pointed 9, 13 is punctured 27, 41 is pointed 81. The 43-node carrier has its own actual geometry: 1+42=1+2*3*7, not a ternary projective count.

Finite geometric weld: F43* is generated by 3 (order 42; 3^21=-1 mod43). On the original Fin42 chart row lines [1:k] (0<=k<41) and [0:1] (infinity), right multiplication by [[4,3],[1,4]] mod41 yields a regular 42-cycle starting at infinity. The matrix has determinant 13, nonzero and nonsquare mod41; its nonsplit torus is from F41(sqrt(3)), since 3 is a nonsquare mod41. This is a PGL2(F41) auxiliary indexing action, NOT an SL2Z generator or an assertion that chart j values are equal/opposite. Its orbit gives a chosen equivariant bijection F43* <-> P1(F41). Exponent CRT is e -> (e mod2,e mod3,e mod7), inverse 21a+28b+36c mod42; negation adds 21, leaving the C3/C7 coordinates unchanged. Thus a 7 x 3 x 2 signed fibre plus a distinguished zero parameter. C2 quotient has 21 nonzero axes; C2*C3 quotient has 7 nonzero base points, but both residual phases are necessary for arbitrary polynomial observations.

| Commit | Source/receipt |
|---|---|
| fecf431f1f15 | CM163Hecke41Signed43TorusExact: concrete finite encode/decode inverses on original Fin42 chart indices, cyclic unit readout, halfturn, projective row cross-product identities, exponent CRT coordinate, and original Prod.reindex product equality. The row-line chart identification follows the original lattice chart definitions; no new analytic equivariance claimed. |
| a6efa449afac | scripts/check_paper9_signed43_hecke_torus.py: local exact rational tests, 339/339 PASS in 0.87 s under timeout 90; Git blob 81bc7f94da3e8b269390f751f779802c289e89c0 matches executed bytes. |
| faefbddc1130 | CM163BishopHecke41SignedParameterProductExact: actual Bishop complex pair product at real parameter y, reconstructs both signed readouts of original finite Hecke factor fold, with cleared sum/difference and explicit origin. No division by y. |

Signed interpolation route: for the same degree<=42 residual P(Y), split P(Y)=E(Y^2)+Y O(Y^2), deg E<=21 and deg O<=20. Exact positive and negative evaluations at y=1,...,21 give E(y^2)=(P(y)+P(-y))/2 and O(y^2)=(P(y)-P(-y))/(2y); P(0) determines E(0). Use 21 nonzero axes with both sign channels plus origin, not 22 scalar observations. If both actual Hecke product and candidate matrix polynomial are proved monic of degree42, their residual has degree<=41, so E and O both have degree<=20; the 21 signed pairs suffice, and zero is a redundancy check. Native degree, monicity, interpolation, and matrix parity identification remain to be written/attached. Single F43 modular reduction cannot certify integer equality (43Y control), use exact Z gates or independent bounded multi-prime CRT with signed reconstruction, not finite-field interpolation as a substitute.

Euler-aware paired parameter ring: multiply (E,O)*(F,G)=(EF+Z OG, EG+OF), Z=Y^2. Existing q-Euler recurrence acts coefficientwise in the parameter and commutes with parity readout at fixed Y; the parameter Euler operator Y d/dY acts as (2Z dE/dZ, O+2Z dO/dZ). Reuse FormalNormEulerExact.dMul, ReducedNormFlowExact and finite reflection; the next mathematical implementation is a polynomial-parameter (or signed-pair) log/norm recurrence, exact coefficient readout and degree/monic proof, with 21 paired specialization witnesses as an alternate replay. The new signed fold gives the actual pointwise product readout, not yet the bivariate recurrence or the actual 43 SectorGate witnesses. Keep the q-Euler analytic j coefficient identification distinct: existing ActualJLogPhaseJetExact and QuotientJetExact.a/b still need same-source attachment. Shared cusp rigidity, reciprocal disk branch and final period/GMP/kernel acceptance remain P0. No CI or native kernel execution in this tranche; finite tests are not proof acceptance.


### Signed nonary codec generalization (2026-11-28)
Source-written `DASHI/Moonshine/SignedNonaryPrime43CodecExact.agda` (65bbd0dc2968) reuses Trit and Sign from BalancedTritBitFibre. Six = T × Sign, seven = centre + six, 43 = empty + one-letter + two-letter words. Nonempty words map bijectively to the existing Fin42 torus exponent using CRT e=36b+28t+21s mod42. The first letter (or absent first letter) is the seven-state base; final letter carries phase/sign. Sign flip on FINAL letter intertwines torus halfTurn, rotation of FINAL trit intertwines multiplication by 6 mod43. Both chart round trips are source-written. This is not simultaneous inversion on all letters: the latter has a different action. Empty is separately distinguished. Kernel pending.

General candidate programme: apply the same construction before comparison with SSP/Ogg. For any odd prime p, p=1+2m gives an antipodal signed residue chart; when p≡1 mod6, p=1+6k gives k signed ternary fibres, using the cyclic multiplicative group and a chosen generator. For p≡5 mod6 there is no multiplicative C3 subgroup: do not invent one. For p=19,37, a C3 factor is not necessarily a direct product with its residual quotient (9 divides p-1); preserve carry/cocycle. For p=13, projective ternary puncture gives (27-1)/2; p=5 pointed antipodal nine gives (9+1)/2; p=41 pointed antipodal 81 gives (81+1)/2. Keep projective, cyclic unit and tree actions separate. Cyclotomic pointed depth-two family Phi3(b)=1+b+b²: b=2,3,5,6,8 give 7,13,31,43,73; b=4,7,9 give composite 21,57,91. Neither this nor the sign quotient is an Ogg selector. Next: scan all candidates 2..71, including composites; compute orders, action kernels, fixed points and residual carries independently of Ogg; attach existing CandidateLevelRepresentationHeckeSquareExact and RamanujanTauCandidateFingerprintJ0To35Exact, then seek actual intertwiner, not equality of counts. No analytic Paper9 obligation is discharged by this finite codec alone.


### 2026-11-28 — native S3/369 Rubik hyperfabric reconciliation and prime normalizer family

This supersedes the interpretation (not the valid cyclic finite code) in the two preceding signed-43 sections. Reopened the original master sources TernaryEndomorphismConjugacyExact, TernaryPermutationS3LawsExact, IITJFineFourOneFourS3ZetaGaugeExact, IITJFineS3RegularMonsterCharacterExact (via original mixed-character owner ledger), Trialectic369RubikRefinementExact, RecursiveRadixHypervoxel, Base369Ternary27HypervoxelFabricGeometryExact, HyperfabricPunctured27Projective13OrientationExact, PointedTernaryBulkExact, Monster196884FibreInterferenceExact, Monster369TwistedTraceObservableCutExact, TernarySevenOggSSPComparisonExact, and docs/369-27-cube-geometry-modular-carrier-disambiguation-20261024.md. Original master/PR geometry and classical group/field theory retain attribution; no new proof of original Monster representation data. The spatial cube P3^3 has 27 sites, 6 faces, 54 bonds; recursive rank3 depth3 is 27^3, NOT a single cube. 6 as glued lines, 6 as T×Sign, 6 as regular S3 and 6 as C6 remain distinct structures. The signed bit encoding is not itself an abelian or nonabelian group claim.

The actual 9->6 value-S3 cut removes all three constant diagonal points; the remaining ordered distinct pairs are the original six ternary permutations (read at low and mid). The 9->7 map collapses the entire constant diagonal to an abstract point, rather than preserving the literal (0,0) under all value permutations. On T^n, three constant points form one three-orbit and every nonconstant word has free S3 orbit, giving 3^n=3+6((3^(n-1)-1)/2). This shares the exact projective count of the nonzero relative shell modulo antipode. n=9 yields 19680=3280*6, 19683=3+19680; the ten coarse marker channels give 196830=32800*6+30. Under C3 this is 65610 regular triples. Existing 196884=(5*2)*27^3+(3*2)*9 and 54=27*2=6*9 remain distinct carrier presentations. If 54 residual is C3-trivial, the character matches the original 3B weight-two restriction. The global value-S3 bulk reflection trace is 10. Any invariant 54-dimensional involution residual contributes at most 54 in absolute value, so this particular bulk plus arbitrary residual cannot attain either original Monster 2A trace 4372 or 2B trace 276 (Monster369TwistedTraceObservableCutExact). No promotion of the global value-S3 action to Monster normalizer; pursue original spatial mixed action and actual source-normalizer representation separately. This bound is an arithmetic deduction from the existing characters, not a new Monster character computation.

| Commit | Implementation |
|---|---|
| 4fe216137234 | SignedNonaryPrime43S3GeometryExact: original TriPermutation group BIDI with Hex, ordered distinct pair reads, 9->7 equivariant pointed quotient, actual cut/join (corrects earlier lossy split), original composition and inverse, explicit cyclic-vs-nonabelian obstruction, sign-dependent first-letter antipode and exact arithmetic reflection. |
| 227af0026306 | Same module: simultaneous two-letter value action <-> relative anchor gauge (h1,h2) -> (h2^-1 h1,h2), both inverse directions and equivariance; actual original projective row cross-product identities, full Fin43 pointed codec. |
| 803c7a106cd3 | scripts/check_signed_prime_s3_hyperfabric.py: 21848/21848 exact independent local checks, 0.92 s under timeout 90; Git blob 0cf0cd9345394a412f49f2655bb112dfac9730e0 matches executed bytes. Counts nonary55, torus212, diagonal432, prime_units40, prime_s31044, hyperfabric20058, controls7. |
| cf1123dc58a6 | SignedPrimeS3UnitOrbitExact: generic explicit residue enumeration and inverse search, native existing Cert.Through proof terms for both round trips and both generators on 342 nonzero labels across nine prime levels 7,13,19,31,37,43,61,67,73. Root cube and nontriviality source-written. |

Actual 43 normalizer: previous exponent chart e=36b+28t+21s. Twist first-letter base b to (-1)^s b modulo7 by the existing sign and trit antipode. The resulting chart is e=36(-1)^s b+28t+21s mod42. Native affine left rotation advances t, reflection negates t and flips s. Consequently R:e->e+28 and S:e->21-e, u=3^e gives R:u->6u and S:u->-u^-1. R^3=S^2=1 and SRS=R^-1. Original projective M=[[4,3],[1,4]] mod41: rotation M^28=[[31,17],[33,31]]; reflection D M^21=[[0,11],[10,0]], D=diag(1,-1). Both are actual projective permutations on the same finite original lattice-row indices. They are not claims of SL2Z invariance of individual analytic j-values. Preserve the cyclic chart as a distinct auxiliary arithmetic action; its old flip commutes with rotation. The pointed full chart keeps empty separate from the 42 nonzero units. Seven is pointed regular S3, not the seven functional-graph conjugacy classes of T^T or seven Ogg lanes.

Universal mathematical construction: for any prime p=6m+1 and primitive root g, z=g^(4m) has order3; choose a nonsquare a. R(u)=zu, S(u)=a/u give free S3 orbits (reflection fixed point would satisfy u^2=a z^k, impossible). Since z is a square, use even exponents 2j (0<=j<m) as orbit anchors and reflected odd exponents for the sign fibre. This handles p19 and p37 without assuming a direct-product cyclic CRT splitting. p43 uses a=-1, z=6, same arithmetic action as above; other cases use nonsquare primitive generator when -1 is square. For p≡5 mod6 no multiplicative order-three root; retain distinct antipodal C2 lane and possible richer ambient representation, not a fabricated six-state free field action. Non-Ogg primes and composite cyclotomic numbers remain controls. The finite proof-bearing scan is not yet an all-primes Agda theorem. Next P0 cross-programme: lift generic field action proof with primitive-root and nonsquare hypotheses; attach candidate-indexed representation/Hecke square and Ramanujan fingerprints without using Ogg membership to choose geometry; maintain explicit spatial/phase/normalizer distinction. A 43-state set action is not a projective plane over a field of order6.

Paper9 analytic max-cut remains: signed coefficient-pair Euler/norm recurrence, actual matrix/gate attachment (or monic signed interpolation), actual q-Euler identification, reciprocal disk, global rigidity and original period/GMP. These finite geometry welds do not discharge analytic gates. No native Agda or Lean kernel available locally; no CI. Explicit proof bodies and independent finite exact local regression are not kernel acceptance.


### Universal parameter / coefficient matrix weld (2026-11-28, continuation)
Reconciliation: comparison of current PR against master returned 669 ahead/74 behind and no Hecke41/Paper9 paths on master-side file list. This is not a merge; do not claim default-branch sync. Reopened actual FormalNormEulerExact, ReducedNormFlowExact, IntegerSpecializationExact, IntegerSpecializationReflectionExact, ArbitrarySliceSeriesExact, and companion Paper9UniversalMonicSlice, Paper9CyclotomicPacketReflection, Paper9SymmetricTauJet, Paper9HeckePoleRemoval. Existing actual norm Euler rule, sector restriction, zero imaginary stream, finite recurrence uniqueness, arbitrary complex analytic slice, monic degree42 and weight-zero rigidity are reused rather than reimplemented.

Companion Lean branch research/paper9-original-eisenstein-derivative-20261125 commits 624162af7fe0 and 99252febf48e: Integration/Paper9SignedUniversalMatrix.lean constructs a single polynomial-valued normalized factor H and infinity factor G over C[Y][q], phase scaling, cyclic norm, evaluation/contract commuting reads, triangular polynomial-valued row recursion, specialization equality with existing sliceC and actual original product. Signed reconstruction and 42-node residual interpolation (degree<42 premise) are source-written. Integer matrix consumer attaches via actual normalized row residual equations; those equations are not yet discharged universally. No kernel execution, no local runtime receipt for this tranche. Existing finite matrix script is separate evidence, not a native proof.

Next exact welds: (1) lift existing Euler rule coefficientwise to C[Y][q] and attach even/odd coefficient decomposition as polynomial maps, (2) prove actual normalized row degree bound <=42 from the 42 linear factors and triangle recursion, (3) establish integer matrix row residual by coefficientwise Newton or 42 signed-node gates plus monicity (do not use field F43 as integer interpolation), (4) derive full symmetry from original separated chart image or analytic infinite evaluation, (5) consume actual original cross/CM derivative/reciprocal disk and signed GMP window. The existing arbitrary complex analytic slice producer already closes rigidity conditional on its normalized prefix and is called by the new source; no new rigidity conjecture. Preserve attribution and explicit noncanonical symmetry actions. Native compile pending.


### Universal matrix symmetry and signed integer gate attachment (continuation)
Companion Lean commits 18d682c405c7 (Integration/Paper9UniversalMatrixSymmetry.lean) and bafcd58cd43a (Integration/Paper9SignedIntegerMatrixWeld.lean) reuse the actual separated-cusp source, not a fresh infinite-image assumption. Universal row degree <=42, actual leading coefficient and transpose symmetry are source-written. The signed integer matrix consumer now explicitly composes integerNormCast, mulCoeffTransport, integerColumnResidual, unit-pivot uniqueness, rowFromSigned and actualMatrix. NodeGate retains the three exact residuals and cast equalities; SignedMatrixGate requires the actual monic leading column and 21 positive plus 21 negative integer nodes. No proof by hash.

Agda PR commit 819f1556cd0f adds scripts/check_paper9_signed_integer_matrix_weld.py, reusing the original GMP packed convolution and full Newton matrix. Independently reconstructs log derivative by signed Newton-doubling inverse, reduced norm by denominator-cleared integer recurrence, and compares normalized infinity-times-norm against every specialized matrix column. 42*(1723+43+43)=75978 required equations, plus inverse/initial/monicity controls. Script committed, not yet executed in this tranche; no PASS or kernel claim. Local environment has SymPy but neither Agda nor Lean. Run timeout 90s python3 scripts/check_paper9_signed_integer_matrix_weld.py on exact checkout, checkpoint output after each pair. If runtime exceeds cap, shard by pairs or use a coefficientwise signed packed recurrence; do not weaken coefficient equality. Remaining P0: instantiate the native NodeGate with actual original integer J casts and finite residual witnesses (exact polynomial equality currently required, so ensure full normalized B cast is built, not only prefix); compile all new Lean/Agda source; connect original CM cross/reciprocal geometry and GMP window. Signed coefficient Euler transport remains independent reusable strengthening, not a prerequisite to the 42-node route. Existing Paper9ActualCross, Paper9NativeFiniteAcceptance and Paper9GMPWindowAcceptance are source owners, not kernel-certified by this commit.


### Signed matrix arithmetic acceptance (checkpointed 2026-11-28)
The checkpoint runner at 73c92a8d884f has completed all 21 signed pairs: 75978/75978 exact coefficient comparisons, 88.123155 s sum of pair processing durations (3.868988–4.622252 s per pair, excluding matrix setup). Reopened the completed local checkpoint and reran the checkpoint validator; all four Git blob fingerprints match committed sources. Structured receipt: Docs/support/reference/Paper9SignedIntegerMatrixCheckpointReceipt20261128.json. Arithmetic acceptance is complete; native kernel checks are deferred at user direction. The remaining mathematical path is original CM cross, reciprocal chart, signed period and GMP; do not treat native kernel availability as a blocker. No claim that a checkpoint is itself an analytic theorem.


### Original CM disk-to-period reconciliation and symbolic acceptance
Reopened Lean Paper9ActualCross, Paper9DiskGeometry, Paper9DiskGerm, Paper9ScalarCross, Paper9SignedCMPeriod, Paper9MobiusDiskPeriod, Paper9LiteralCross, Paper9NativeFiniteAcceptance and Paper9GMPWindowAcceptance. The entire conditional analytic route already exists: literalPrefixFromFiniteChecks consumes eight explicit finite checks, constructs actual selected CM root, original normalized disk germs, actualDiskCorrection, actualLiteralPrefixPeriod, and feeds actualPrefixLimit and floorFromRaw. Do not rebuild these as outstanding theorem bodies. The universal signed matrix is independent strengthening; the literal diagonal/fixed slice route already suffices for period. New exact symbolic checker scripts/check_paper9_cm_disk_period_weld.py (75b6edc52a76, corrected d736bf1825d3) locally executed with SymPy 1.14, committed blob 53e83409b15a4484ff1d52e8b50122539df98861 matched git hash-object. PASS 17/17. First run caught new checker general M derivative typo (2-t)(1+t); corrected to (2-t)(2+t), matching existing CM M'=163/1681 AB. Exact checks cover reciprocal Mobius conjugation, disk inverse, second Taylor germ, cleared cross zero/first modes, Euler correction 77265280/90856689, Chudnovsky weight ratio and positive squared normalization. No analytic convergence or root selection follows from symbolic checks alone. Next P0 audit and replay eight existing finite checks, actual literal source packet and root isolation; run original GMP acceptance against exact committed bytes and reconcile manuscript. Native kernel deferred per user; do not declare formal theorem verified.


### Original eight finite predicates: arithmetic replay 2026-11-28
New runner scripts/check_paper9_original_finite_replay.py at 6996b2057a53; local git hash-object matched committed blob 916d2c55a40667f740919e59f7933353e7520097. Under 90s timeout, 25.998 s: unit 6646/6646, diagonal 3529/3529, fixed slice 1809/1809, total 11984/11984 integer equations; piRoundOK, sqrtRoundOK, expWindowOK all exact rational PASS. Recurrence uses reconstructed matrix matching historical packet digests, not direct local packet bytes; --packet enables direct source comparison. Separately fetched actual Agda decimal packet eb41e2c937d89dfb8cf2f90d1f31e69b945ad5e0 and Lean hex packet 185fbf271b9089afc1ce123d2f53a21f5d89a6df, compared all 83+43 coefficients directly with BigInt, shiftOK and jetOK PASS on literal packet, dominance ratio <=1/1000000. Receipt Docs/support/reference/Paper9OriginalFiniteReplayReceipt20261128.json. Original 1722 Newton divisions, 1849 symmetry entries, 126 digest checks rerun in 3.364s; symbolic 17/17 rerun; signed checkpoint reopened 21/21 pairs. Eight predicates have corresponding exact arithmetic evidence, not native theorem acceptance. Next P0 direct local literal packet run, original exact-source GMP production with per-precision checkpoint, cross-check Machin/Chudnovsky floor and manuscript reconciliation. Kernel deferred; external comparator/SOTA still separate.


### Exact-source in-place GMP production replay
Original scripts/check_pi_gmp_codec_memory.cpp restored locally, git hash-object matched original blob 82027bc7acee4b4711f0ca1a2ed42dce1d60b8c5, compiled with g++ 14.2.0 -O3 -std=c++17 and GMP/OpenSSL. Direct executable, one run per precision under separate <=90s bounds (checkpoint wrapper b418bcb7ea8c not itself executed). All six historical hashes reproduced at 10k,100k,500k,1M,5M,10M. 5M 6.6502244 s / 132824 KiB; 10M 15.3168999 s / 264072 KiB. Receipt Docs/support/reference/Paper9OriginalGMPInplaceReplay20261128.json. No repeated timing or external SOTA promotion. Original quotient/cross-GCD backend replay, direct local literal packet replay, manuscript reconciliation and analytic/native proof checking remain distinct. User deferred Agda/Lean execution, no CI. Continue with matched quotient modes, independent Machin raw floor and production residual transport, then performance optimization.


### Exact-source quotient and cross-GCD matched comparison
Original quotient source blob 28f4657e5bdbfc27ebb7cc3690f6144590ba2d5e verified locally and compiled -O3. 4 precisions (10k,100k,500k,1M) x 4 modes x 3 repetitions = 48 executed runs; 16 configuration medians, every mode/precision matches historical hash, last reported attempts=1. Per precision external timeout 90s; direct original executable, separate retained stdout, not checkpoint wrapper. At 1M plain two/one floors 862.008/843.515 ms; cross two/one 993.142/1025.702 ms. Aggregate carrier bits 18472995 -> 9034322 (-51.09%), split cost increases from 358.668 to 616.781 ms for one-floor; division decreases 96.351 -> 76.914 ms. This is not a memory RSS comparison; no SOTA or universal speedup claim. Receipt Docs/support/reference/Paper9OriginalGMPQuotientReplay20261128.json. Both original backends have now passed intended precision coverage (6 in-place and 16 quotient configuration gates); checkpoint wrapper not executed. Next: selective cross-GCD threshold sweep and exact independent Machin floor, manuscript status reconciliation, native kernel deferred.


### Selective subtree cancellation P0
Wrapper scripts/check_pi_gmp_selective_cross.cpp at 345a5dea7bff includes original quotient source and calls certify(d,threshold,true,true). Local wrapper blob 0c98513d9f17489d65b0a4a295d994ab0aacde70, repository blob 0c98513d9f17489d65b0a4a295d994ab0aacde70; original blob verified 28f4657e5bdbfc27ebb7cc3690f6144590ba2d5e. Two separate <=90s batches at 1M: 13 exploratory thresholds plus 12 repeat runs, all 25 exact floor admissions first attempt, all hashes match. Three-run medians: plain 842.777ms, threshold128 909.703ms (9039413 bits), threshold16384 992.034ms (10130672 bits), full threshold2 1117.155ms (9034322 bits). Plain 18472995 bits. Threshold128 retains nearly all compression with lower measured median than full cancellation but remains slower than plain; no RSS or SOTA conclusion. Compiler warns renamed unused original main lacks explicit return; wrapper only calls certify, no original main execution. Receipt Docs/support/reference/Paper9SelectiveCrossSweep20261128.json. Next optimize cancellation by bounded prime valuation or size-adaptive selective schedule, independent Machin floor comparison, direct packet replay and manuscript reconciliation. Keep plain one-floor default pending measured Pareto improvement.


## Whole-programme closure cut — 2026-11-28

Reverse target: original Bishop chudnovskyReal ≃ bishopMachinPi, universal ExpandedCross, and exact production floor for each admitted precision. Independent performance target: improve measured time/RSS Pareto frontier, not an asserted global fastest algorithm.

### Owner reconciliation
Master fad22a838ab83 versus PR1546 at 45fbac66b8a9: 74 master-only commits, 690 PR-only; reverse comparison returned no matching Paper9/CM163/Machin/Chudnovsky/GMP paths in its returned file list (not exhaustive proof). PR1529 d8956bb9ba27 contained missing check_pi_prime_valuation.py and check_pi_selective_valuation.py; restored identical blobs in c37bc913d641 and b8207b785d87. PR1291 c68b44f37c89 supplies broader signed residual geometry; selected SSP15 basis is not all primes. Lean companion vs main 115 ahead/7110 behind at audit; no wholesale merge. Pin relevant source owners, verify interfaces before selective integration.

### Analytic reverse-solve
A0 terminal equivalence already source-written: BishopChudnovskyNativePeriodProductExact.periodToSameReal, periodToExpanded, sameRealToPeriod, expandedToPeriod; actualProduct and seriesApart use original objects. No new same-real definition.
A1 E4 terminal mincut: JInvariantBishopCM163E4JetPeriodExact.periodFromRootAndE4Jet requires negative selected Delta, positive selected X, actual root equality, sq Euler.H ≃ X, Flow, Correction. correctionToCross and crossToCorrection already supply bidi. NativeEulerLimitsExact.H/J₁/hConverges/jConverges/actualWeightedLimit already constructed. Do not reopen convergence.
A2 root: original diagonal and fixed slice, finite integer residuals, selected root weld, literal bracket/dominance; remaining actual Bishop modular rigidity and cusp bound attachment. Lean Paper9HeckePoleRemoval, Paper9CMExpWindow.rootFromOriginalFiniteChecks are source-written on pinned analytic carrier; no foreign proof import.
A3 flow: derive actual E4 square-root hypergeometric stream and first Euler derivative on same selected q via Ramanujan and ODE coefficient uniqueness; reuse NativeHyperODEExact, NativeFactorialEulerAttachmentExact, NativeEulerLimitsExact, JInvariantBishopEisensteinEulerJetExact. Required output sq H ≃ X and 6 Y J₁ ≃ H U, not arbitrary redefined H.
A4 correction: JInvariantBishopCM163DiskCrossCoefficientExact.signedJetFromLiteral takes actual first/second q jets, literal S2 apartness, A apartness, 41P2=163S2, 41P3-326S3=163κS2, and literalResidual=0. Its diskJet and signedJet already eliminate the scalar residual. Reuse ActualJLogPhaseJetExact.actualLogJet and actual reciprocal chart branches, identify real coefficient jets with QuotientJetExact.a,b, then apply signed correction consumer and E4 terminal. No new κ or desired-period premise.
A5 actual analytic rigidity: reduced disk via S/T height ascent and cusp boundedness; constructive Fourier/Poisson coefficient extraction and strict contraction to constant. Need actual q-descent, uniform disk bounds, quadrature limit on Bishop carrier, not merely finite root-of-unity tests. Lean actual weight-zero rigidity route is independent. A1-A5 proof bodies not all completed; no finite regression promoted to all-index theorem.
A6 same real/universal cross: once NativePeriod supplied, existing periodToExpanded and RawCoordinateWeldExact transport literal coordinates; no new cross-family hypothesis. Cofinal nesting is alternate route, not required if period route paid.

### Arithmetic implementation
C1 restored full and selective predictive factor-ledger owners. New scripts/check_pi_gmp_predictive.cpp (57c779bb140) ports full prime ledger, signed P/Q/T, exact divisibility and in-place joins. Untracked-prime selective variant must preserve residual; not yet implemented in C++.
C2 scripts/check_pi_geometry_closure.py (016aeb937599) reuses original Machin and Chudnovsky interval evaluators, independently admits strict common floor, and constructs/replays full valuation trace. Finite overlap alone not all-index equality.
C3 scripts/check_pi_gmp_predictive_trace.py (c93241eac6fd) reads actual postorder output, checks merge coordinates g,rq,lp, contiguous leaf coverage, root square and strict floor. Existing Lean Paper9GmpCertificate.reducedSound/evaluatesSound/prefixSound and Paper9GmpTraceChecker.checkedSound/sound already admit arbitrary positive exact cancellation, no gcd-maximality premise. Remaining native serialized parser adapter; optional trace storage costs measured separately.
C4 acceptance: exact source parity, compile and run each new script locally; negative controls tamper sign, divisor, leaf order, root, upper floor. Compare full predictive with original full GCD raw triple, not only SHA. Independent Machin common floor at 100,1000,10000 then scale; GMP 10k/100k/1M and 5M/10M as bounded feasible. Each invocation <=90s, checkpoint per precision/backend; no fabricated receipts. Existing six in-place, sixteen quotient and 25 selective admissions remain prior evidence; new code not executed yet.
C5 optimization: measure map allocation, exponent reconstruction, sieve, division, merge, serialization and RSS; balanced prime-power multiplication and bounded smooth ledger + residual GCD, retain sign. If predictive loses, retain plain default. Require repeatable matched timing, no external SOTA without comparator.
C6 direct local literal packet replay still outstanding; cross-repository exact 126 integer equality and prior matrix digest replay are separate. Reconcile checkpoint wrapper validation and source fingerprints. Manuscript distinguishes source-written, external arithmetic evidence, and kernel acceptance. User deferred Agda/Lean execution, no CI.

### Coarse-to-fine order
First compose terminal conditional interfaces on the original objects (A0-A6), then eliminate genuine producer premises rather than writing duplicate consumers. In parallel C1-C6 validate production and optimize. Stop only on explicit unresolved analytic producer or failed arithmetic test; record exact obstruction and next constructor. Classical Machin, Chudnovsky, Ramanujan, Hecke, binary splitting, valuation cancellation and modular rigidity retain prior-art attribution; DASHI contribution is same-carrier signed geometry and executable/proof weld.


### Predictive production closure replay
Exact local C++ blob f3218e6003877aace21a98cf9f6b4e4128ccccac and original quotient blob 28f4657e5bdbfc27ebb7cc3690f6144590ba2d5e verified; 10k/100k/1M all first-attempt floor admissions, historical hashes match, 90s bounds. At 1M 1321.25 ms and 9034322 bits; map ledger slower than plain. 10k actual postorder trace independently replayed by local harness: 716 leaves, 715 merges, exact raw P,Q,T equality with full GCD, five corrupted controls rejected (sign, divisor, leaf order, root, floor). Independent local reconstruction of original Machin and Chudnovsky rational evaluator equations admitted common strict floors at 100/1000/10000, overlap also checked. The committed Python wrappers were not byte-matched/run; native parser, large-precision predictive runs, optimization and analytic A1-A5 producer proofs remain. Receipt Docs/support/reference/Paper9PredictiveGMPClosureReplay20261128.json. No CI or kernel promotion.


### 2026-11-28 original same-source analytic closure cut (P0)

New owner: DASHI/Moonshine/CM163BishopOriginalSameSourceClosureExact.agda, commit 4fbbb9fc2e6b. The original CM producers are collected as ONE proof-relevant record parameterised by the same actual coefficient jets (a,b), Hecke packet (s,t,u,v), and hypergeometric chain derivative l. It intentionally does not manufacture existence of the record. Its fields are precisely:
1. Actual guarded root Reduction.CMRoot, sourced by SelectedDiskExact/RealSlicePeriodExact, which still needs original analytic CM modular rigidity and cusp enclosure at the actual selected q.
2. Actual original factorial limit square Reduction.HyperSquare, sourced by NativeEulerLimitsExact.H and E4 coefficient/ODE matching. No replacement H.
3. Same derivative l: X*l=Y*Euler.J1 and 6*Euler.H*l=U; clearedFromChain produces ClearedHyperJet. Source owners: NativeHyperODEExact, NativeFactorialEulerAttachmentExact, ActualJLogPhaseJetExact, EisensteinEulerJetExact. This is not achieved by separately assuming a freely chosen analytic flow.
4. Actual q derivatives a,b satisfying NativeJetReductionExact.FirstQJet/SecondQJet, genuine apartness of disk A and S2. Existing same-analytic-point series jets ActualJLocalSecondJetExact/ActualJLogPhaseJetExact must be specialised to native selected q; derivative coefficient readout is needed, not a second independent j.
5. Actual literal Hecke packet P2/P3 signed relations and analytic literalResidual=0 of the same reciprocal product. The finite 126 packet equality and 17 symbolic checks are supporting reference checks, not this original analytic product proof. DiskCrossCoefficientExact.signedJetFromLiteral eliminates s,t and transports the original κ sign; it supplies native SignedJet.
The module then COMPOSES actual producers with existing NativeJetReductionExact.clearedFromChain / periodFromThree and End.periodToSameReal / periodToExpanded plus RawCoordinateWeldExact.rawFromPeriod to derive the literal original Bishop same-real, universal expanded cross, and all-index raw cross. It additionally exposes correctionFromSigned/signedFromCorrection under the same selected cubic for bidirectional checking. This is source-written and not Agda-kernel-checked. None of the five proof-producing fields are claimed inhabited just by defining the record.

Reverse-solve exact priority:
A: original analytic Hecke product (construct real series equality on CM q, prove reduced residual=0) and Bishop root enclosure/rigidity;
B: actual q jets and E4/E6 coefficients at the SAME selected q, establishing the first/second derivative equations, not postulated values;
C: original hypergeometric ODE uniqueness and chain readout proving H²=X and derivative l for H and J1;
D: construct OriginalCMProducers fields and call sameReal/universalRawCross. Do not add a new endpoint theorem or arbitrary period equality. Strict positivity/apartness must be supplied constructively before cancellation.
Computational code and receipts remain independent: predictive GMP and original Machin common-floor checks cannot instantiate a real analytic field. Bounded local SymPy tests can validate coefficient identities only. No native proof run or CI.


### A4 producer reduced to one original Ramanujan differential owner — 2026-11-28
Cross-check of branch source shows JInvariantBishopCM163NativeJetReductionExact.FirstQJet and SecondQJet are EXACTLY the following two readouts at the same selected point, with X=E4, Y=E6, K=j, a=Dj, b=D²j, U=3D E4:
- X*a = -K*Y
- 6 X²*b = K*(3 X³ + 3 Y² - Y*U).

There is NO need to prove these as two unrelated analytic identities. Both follow from the same original Ramanujan derivation:
3 D E4=E2 E4-E6; 2 D E6=E2 E6-E4²; D Delta=E2 Delta; j Delta=E4³.
Differentiate j Delta=E4³, use Delta apartness, derive X*a=-K*Y. Differentiate that CLEARED equation and use the two Ramanujan identities to derive 6X²*b=K*(3X³+3Y²-Y*U); no inverse of X required. All equations are on original j and Delta, so this is a SAME-SOURCE closure. New source-written Lean Integration/Paper9OriginalRamanujanTwoJetWeld.lean (companion commit ffd1846d6cce86068e9cc42b11cb98abf8e6b372) contains the two actual algebraic derivations using linear_combination, plus a joint consumer. Its remaining input is original analytic differentiation/product rule at the selected Bishop q, not an assumed jet or second j.

New source scripts/check_paper9_original_jet_derivation.py (487e53e9c1d0) gives exact formal q-coefficients for original E2,E4,E6, Delta=(E4³-E6²)/1728, J=q*j via integer formal inversion, and both j-jets with signed Laurent normalization. Local equivalent SymPy 1.14 script at degree 256: 771 Ramanujan, 257 discriminant, 257 first jet and 257 second jet exact coefficient checks PASS; the two cleared polynomial syzygies PASS. Original disk/period SymPy script also reran 17/17 PASS. This does NOT prove Bishop termwise differentiation, q-domain analyticity or modular point admission. The committed Python source itself has not been byte-verified against the locally run variant; receipt Docs/support/reference/Paper9OriginalRamanujanTwoJet20261128.json.

Remaining A4 proof inputs now:
1. Use original analytic q-domain and radius witnesses from JInvariantBishopEisensteinEulerJetExact, JInvariantBishopUnitDiskEisensteinCompletionExact, JInvariantBishopRamanujanDeltaUnitExact, and ActualJLocalSecondJetExact; show termwise Euler differentiation (or reuse its existing native theorem), product rule for j Delta=E4³ on that original disk.
2. Specialize to the literal negative-real selected CM q, with actual negative Delta apartness (RealSlicePeriodExact.AtNegativeDelta.nz) and map q-jets to real components; do not assert missing derivative from finite coefficient checks.
3. Consume the now ONE Ramanujan jet result to fill OriginalCMProducers.firstQ / secondQ, retaining exact K sign and U normalization. Finish the actual reciprocal Hecke literalResidual and hypergeometric H²/chain; then instantiate OriginalCMProducers and obtain NativePeriod/same-real/universal cross.
No new period proof, new j, new q or independent first/second jet assumptions; kernel execution deferred by user.


### Source-owner correction after exact Lean audit — do not rebuild actual analytic j jets

The companion Lean PR already supplies stronger original analytic producers in Integration/Paper9ActualJSourceJet.lean: jQEuler proves D j(q) = -j(q)*E6(q)/E4(q) at actual q under norm(q)<1, q≠0, E4(q)≠0; jFirstDeriv and jExtSecond prove first/second derivatives of the ACTUAL j extension through the original exponential q chart. Integration/Paper9E2CorrectedClosure.lean.originalRamanujanSystem and Integration/Paper9HypergeometricQTransport.lean.ramanujanQ own the original Ramanujan q-system. Integration/Paper9ThetaEisensteinSameObject.lean.thetaE4_eq_original/thetaE6_eq_original own genuine same-form theta↔Eisenstein identity by cusp zero, not finite comparison. All these are source-written; kernel not run here.

Our new Lean OriginalRamanujanTwoJetWeld.firstJet/secondJet supplies an optional *cleared-denominator* projection onto the Agda original NativeJetReductionExact.FirstQJet/SecondQJet coordinates. It is NOT a replacement proof of differentiability: the existing actual q analyticity, jQEuler and jExtSecond already pay that on Lean's carrier. Remaining original Agda/Bishop transport: identify the selected actual q from SelectedDiskExact with the complex exponential of tau (phase!), show source E4/E6 and q-jets on that original disk, attach the already-paid analytic derivatives to the Bishop real-slice coefficient definitions with apartness, and use the signed Hecke reciprocal residual at the same j. DO NOT assume that Lean's proofs have automatically furnished Agda proofs.

CRITICAL NORMALIZATION: Lean jFirst / jExtSecond use the complex upper-half-plane derivative scaleD=2*pi*i, while Agda NativeJetReductionExact.FirstQJet and SecondQJet use Euler q derivative D=q*d/dq. Preserve explicit scaleD powers and the actual disk ray p used for the w expansion. In Paper9ActualJSourceJet.lean the local p for the tau coordinate is pi*Im(tau), whereas Agda NativeJetReductionExact.p=pi*sqrt(163) for log q ray; at tau=(-1+i sqrt163)/2 these differ by factor TWO. Check source geometry/log(q/q0)=-2*p*w/(1-w) before porting; do not silently identify the two p's. The exact coordinate conversion is part of the remaining same-source weld.

Conclusion: A4 original j derivative algebra and companion analytic derivative owners exist; the open cut is exact cross-carrier specialization and q/tau normalization. Focus actual CM-root/Hecke residual and hypergeometric H²/chain remaining producers rather than duplicating j derivative code.


### 2026-11-28 — selected phase, denominator and original actual analytic owner reconciliation

Actual Bishop selected q: JInvariantBishopCM163SelectedDiskExact.q = complex(-Radius.machinQRadius imag,0), imag=canonical sqrt163/2, tau=(-1+i sqrt163)/2. JInvariantBishopCM163TailGuardExact ALREADY PROVES xPositive, yPositive and negativeDelta and constructs Root = Selected.AtNegativeDelta negativeDelta. Therefore REMOVE "negative Delta sign", "positive original X/Y" and "guarded j existence" from outstanding. Remaining original root producer = equality of this Root.j to literal -262537412640768000 by original all-index CM modular/Hecke rigidity and constructive selected phase. Do not conflate all-index analytic rigidity with finite 126 packet or source-written universal result.

New DASHI/Moonshine/CM163BishopSelectedQScaleTransportExact.agda (99ace933c55e) writes the actual dimension-preserving equality 2*piMachin*Im(tau)=piMachin*sqrt163. The original RadiusGuardExact.exponentShape ALREADY supplies the right-hand radius exponent. This same p is used in NativeJetReductionExact and DiskCrossCoefficientExact. DO NOT equate it with the half-scale piMachin*Im(tau). All algebra is source-written/kernelless.

The older K05-PI owner DASHI/Analysis/BishopMachinCayleyHalfPhaseToFirstZeroExact.agda has OriginalMachinCayleySameObjectEvaluation and sourceMachinFirstPositiveZeroFromSameObjectCayley, consuming a Round11 imaginary-exp product. The original Cayley rational phase is already transported into the same Bishop complex carrier. The STILL OPEN producer is evaluation of original Bishop complex exp/atan at those Machin arguments, and compatibility with original q(tau), NOT a new sine/cosine law or generic e^(i*pi) axiom. Original complex-exp construction/equality: AbelBishopOriginalComplexCarrierWeldExact.originalBishopExpSameSource and BishopComplexExpFactEqualsNativeExpExact.originalBishopExpFactEqualsNativeExp. The Maple/Mathlib classical exp phase is a reference only.

Exact reciprocal Möbius fixed point / multipliers already owned by JInvariantBishopCM163ReciprocalGeometryExact: tau²+tau+41=0, f=-41/(tau+1), g=(-41-tau)/tau, alpha=(-81-i sqrt163)/82 and beta its conjugate, alpha*beta=1, alpha+beta=-81/41, N0/N1/M0/M1 literal signed coefficients. New scripts/check_paper9_selected_q_phase_geometry.py (014ed7de6916) local equivalent SymPy reference PASS for fixed points, derivatives, product/trace, 2*piImag scaling, q(w)=q0*exp(-2p w/(1-w)) first/second Euler pullback. Script itself not locally byte-verified; receipt Docs/support/reference/Paper9SelectedCMPhaseScaleGeometry20261128.json. No Bishop exp phase or Hecke root promoted.

Existing companion analytic ownership is even stronger than previous inventory:
- Paper9ActualCMPoint.cmQPhase, cmQSmall, selectedHyperAtCM and selectedFirstJetAtCM already supply Mathlib/Lean actual q, original hypergeometric E4-root identity and first derivative AT THE CHOSEN CM POINT, on that same carrier.
- Paper9ActualJSourceJet.jQEuler, jExtSecond and Paper9HypergeometricQTransport.ramanujanQ already supply actual analytic q-jets; Paper9SelectedCMDomain.goodSelected / originalBands supply X nonzero at that CM q.
- New Integration/Paper9SelectedOriginalQJetAtCM.lean (companion caf9f7e38725) specialises true jQ to the same cmQPhase point and bundles existing selected hypergeometric identity, original first root derivative, first and second j Euler readouts. It is source-written and NOT kernel checked.
Hence the remaining Lean analytic "first derivative" and hypergeometric identity need not be reproved. What remains across Lean->Agda is typed same-source identification of selected Bishop q with the actual complex exponential, q-Euler vs tau derivative scaleD=2*pi*i, and transport of real-slice coefficient jets without swapping Mathlib Real.pi for Bishop Machin real. The original Bishop H must be shown equal to the selected analytic hypergeometric series *as an original Bishop real* via existing coefficient uniqueness, not simply equated to Lean rootF. The actual all-index Hecke product derivative supplies literalResidual=0; the packet and five-coefficient algebra are already paid.

Coarse terminal remains existing OriginalCMProducers -> periodFromThree -> nativePeriod -> periodToSameReal -> expanded/raw cross. Focus proving the actual phase bridge, actual selected CM root and signed original Hecke residual; at parallel cut, Bishop same-real hypergeometric H² and chain from original factorial series. Do NOT create another conditional endpoint theorem. No kernel/CI execution.


### Original Bishop Machin two-point phase actually terminates at selected negative CM q

Source ownership corrected again: original Bishop imaginary exponential multiplicativity is ALREADY source-written at BishopMachinCayleyNativeProductFirstZeroExact.originalNativeImaginaryExpProduct (and BishopK04dK05NativeProductDischargeExact.sourceImaginaryProduct). Original assembly from the TWO ACTUAL atan values is ALREADY source-written in BishopMachinTwoPointCayleyCompositionExact.nativeCombinedCayleyFromTwoOriginalAtanValues. Do not count either product or quarter assembly as a fresh input. The exact independent source producer cut is only:
- TwoPoint.OriginalAtanFiveCayleyEvaluation inputs: exp_B(2 i atan_B(1/5)) ≈ embedded (12+5i)/13.
- TwoPoint.OriginalAtan239CayleyEvaluation inputs: exp_B(2 i atan_B(1/239)) ≈ embedded (28560+239i)/28561.

Original existing Gaussian rational composition: [(12+5i)/13]^4 * conjugate[(28560+239i)/28561] = i, with the 4th power (-239+28560 i)/28561 and exact sign. This is already proven by BishopMachinExistingCayleyReuseExact; scripts/check_paper9_machin_two_atom_cayley.py is a byte-matched local exact audit of these numbers, all signed negative controls and Cayley differential polynomial, receipt Docs/support/reference/Paper9OriginalMachinSelectedQPhase20261128.json.

New BishopMachinSelectedImaginaryPhaseWeldExact.machinImaginaryPhaseFromTwoOriginalAtans and CM163BishopOriginalQPhaseFromCayleyExact.FromTwoOriginalAtans.originalQ compose the original source products, K05 first-zero/trig endpoint, Bishop native exponential radius, the exact factor-two normalization, and explicit componentwise equivalence from BishopSetoidComplexExact to BishopComplexSeriesConvergenceExact. The target is exactly the preexisting selected q=complex(-exp_B(-π_M√163),0), not a newly chosen q or external Mathlib π. The source phase uses exp_B(-π_M√163+iπ_M) with the actual selected tau; no free phase at tau input after the two atom evaluations.

Another important source-owner reuse: BishopOriginalMachinAtanFiniteDerivativeExact.originalMachinAtanFinitePartialFactorDerivative proves literal finite atan derivative; BishopOriginalMachinAtanDerivativeGeometricWeldExact.originalAtanFiniteNativeDerivativeResidual proves (1+x²)*partial' = 1-(-x²)^N for all N; BishopOriginalLogAtanDerivativeLimitValuesExact.originalAtanSourceDerivativeLimitIsReciprocal proves convergence of the literal derivative series to reciprocal (for each original half-ball x); BishopOriginalMachinAtanUniformHalfBallTailExact.originalMachinTwoPointUniformApproximation proves actual source function-tail control. Thus DO NOT re-prove term derivatives or derivative-series pointwise limits. Genuine last analytic producer for a UNIFORM atan-to-Cayley theorem: derivative-of-original-limit interchange on compact sub-half-balls, origin normalization (via Bishop original exp factorial) and a constructive uniqueness/integration argument for the same first-order ODE (1+x²) F'=2i F with F(0)=1. Both Cayley and exp_B(2i atan_B x) obey the same ODE if the source differentiation laws hold. One general proof pays both x=1/5 and x=1/239. The precise remaining source control is the uniform quotient/tail interchange; BishopFactorDerivativeInterchangeExact already defines the reuse pattern but does NOT supply universal interchange automatically.

The new Agda files are source-written and have NOT been elaborated in a native Agda toolchain; no proof status promoted by the symbolic regression. All unsafe-import-sensitive new source files have --safe removed pending pinned Agda dependency/type checking. Pending further review: correct same-carrier identification of full 2π_M i tau with -π_M√163+iπ_M through the original Cartesian complex algebra; all-index Hecke root/product and Bishop hypergeometric factorial-series H²/chain remain major analytic producers. Avoid adding another conditional period consumer.


### 2026-11-28 — original Bishop q(tau) phase resolved conditionally from precisely TWO original atan evaluations

Audit recovered pre-existing actual source constructors:
- BishopMachinTwoPointCayleyCompositionExact.OriginalAtanFiveCayleyEvaluation / OriginalAtan239CayleyEvaluation, the only still uninhabited source evaluations;
- BishopMachinTwoPointCayleyCompositionExact.nativeCombinedCayleyFromTwoOriginalAtanValues, proving full original rational quarter-Machin phase from those two, without separately assuming the imaginary exp product;
- BishopMachinCayleyNativeProductFirstZeroExact.originalNativeImaginaryExpProduct (native signed-factorial Cauchy product), with the real first-zero/sine/cos endpoints and original parity already owned;
- BishopOriginalMachinAtanFiniteDerivativeExact, BishopOriginalMachinAtanDerivativeGeometricWeldExact (all-N native finite factor derivative + geometric residual), BishopOriginalLogAtanDerivativeLimitValuesExact (actual source derivative-series limit), and BishopOriginalMachinAtanUniformHalfBallTailExact (original uniform atan function tail). DO NOT count any as missing.
- BishopOriginalExponentialGlobalDerivativeFromOriginExact already reduces global original real exp differentiation to its origin derivative, rather than demanding a new all-point derivative theorem.

Native conditional phase chain now source-written (not kernel checked):
1. BishopMachinSelectedImaginaryPhaseWeldExact.machinImaginaryPhaseFromTwoOriginalAtans: e_B^(i*pi_M)=-1 from TWO atomic evaluations with pre-paid native product and quarter alignment.
2. CM163BishopOriginalQPhaseFromCayleyExact.FromTwoOriginalAtans.originalQ: source Bishop exp(-pi_M sqrt163-i*pi_M) equals the existing selected CM q exactly, using original negative-argument sine/cos parity, native real exp and existing radius identity; no Mathlib Real.pi.
3. CM163BishopSelectedTauExponentExact.literalExponentSigned: the actual ORIGINAL Cartesian exponent of tau=(-1+i sqrt163)/2 is 2*pi_M*i*tau = -pi_M sqrt163 - i*pi_M, **not plus i*pi_M**. Earlier plus phase was a WRONG literal argument, despite exponential period equivalence; fixed in current source. FromTwoOriginalAtans.actualBishopCMQ uses the source expCongruent and component readback to show the exponential of the literal 2*pi_M*i*tau agrees with JInvariantBishopCM163SelectedDiskExact.q. No newly chosen CM point/real.
4. scripts/check_paper9_machin_two_atom_cayley.py latest blob 45c3ec9b4958be664583c8535d3ed8f88b2351d6 executed byte-identical locally, exact Q[i] signed identities, 3 negative controls, polynomial Cayley first-order ODE, selected tau NEGATIVE imaginary argument and negative control, signed q-ray second order PASS. Receipt Docs/support/reference/Paper9OriginalMachinSelectedQPhase20261128.json (refresh if needed).

Minimal analytic K05-PI completion path from this state: establish an ORIGINAL Bishop uniform derivative-of-limit interchange for atan_B(x), via the existing all-N finite factor derivative, geometric residual, derivative-series convergence and uniform tails; combine the original complex exponential derivative/source Cauchy product and constructive ODE uniqueness to show exp_C(2i atan_B x) = (1+i x)/(1-i x) on original Bishop |x|≤1/2. One uniform theorem pays x=1/5 and x=1/239, removing both atomic premises. The necessary complex exp derivative might itself require source-origin Taylor quotient, so do not infer it from uncompiled real exp results. Alternative: direct constructive power-series coefficient-uniqueness and absolute Cauchy product, paying same 2 atomic values without derivative interchange. Both are proof routes, not established kernel theorems.

Remaining actual Paper9 large cuts AFTER phase are still genuine: Hecke modular polynomial analytic root at CM163, same-source Bishop H² / hypergeometric E4 and derivative, signed all-index Hecke two-jet residual. The phase construction DOES NOT imply these other producers or NativePeriod automatically. No Agda/Lean execution/CI.


### 2026-11-28 — original Bishop Machin arctangent derivative-interchange narrowed to one uniform SECOND defect bound

Recovered source owners are stronger than prior gap accounting:
* BishopPowerFirstOrderDifferenceFactorisationExact.powerDifferenceFactorisation and powerDerivativeIsDifferenceQuotientAtZero provide the ORIGINAL Bishop finite power quotient, division-free at h=0.
* BishopOriginalFiniteLogQuotientSecondOrderExact.originalPowerQuotientSecondOrder supplies the ORIGINAL power second quotient recursively, for all exponents and all Bishop x,h. No new second-order power law necessary.
* BishopOriginalMachinAtanFiniteDerivativeExact owns true signed original atan term/partial factor derivatives. BishopOriginalMachinAtanDerivativeGeometricWeldExact owns actual derivative == geometricPartial(-x²,N), not a generic approximation.
* BishopOriginalLogAtanDerivativeLimitValuesExact.originalAtanSourceDerivativeLimitIsReciprocal pays the actual derivative-series limit on the Bishop half-ball; BishopOriginalMachinAtanUniformHalfBallTailExact supplies original function uniform tails; neither is to be re-proved.

New DASHI/Analysis/BishopOriginalMachinAtanQuotientSecondOrderExact.agda source-written, not Agda elaborated, assembles an ALL-N original signed finite quotient and second-order defect from these owners:
  Q_N(x,h) = Σ_{k<N} (-1)^k/(2k+1) * powerDifferenceQuotient(x,h,2k+1)
  S_N(x,h) = Σ_{k<N} (-1)^k/(2k+1) * sourcePowerSecondQuotient(x,h,2k+1)
  A_N(x+h)-A_N(x) ≃ h Q_N(x,h)
  Q_N(x,h) ≃ A'_N(x) + h S_N(x,h)
  Q_N(x,0) ≃ A'_N(x) = geometricPartial(-x*x,N).
No division by h or fake derivative at x=0; all signed odd reciprocal factors original.

scripts/check_paper9_original_atan_quotient.py blob 7808ee48b2a1e313f22b46dc66f749b71f8dfeb8 is byte-for-byte locally executed: 2096 exact rational identities PASS including power differences (degrees 0..64), source atan finite quotients n=0..32 at eight signed half-ball (x,h) pairs, h=0, original signed derivative and SECOND defect, sample |S_N|<=8/9 and 3 sign/denominator negative controls rejected. Receipt Docs/support/reference/Paper9OriginalMachinAtanQuotient20261128.json. The 8/9 is only sample tested, not a proven all-index Bishop bound.

THE NEW EXACT ANALYTIC MINCUT (instead of generic derivative-limit interchange):
  prove for all N and all Bishop x,h with |x|,|x+h|<=1/2, |S_N(x,h)|<=8/9,
  by bounding each original quotient second power term with the finite
  polynomial difference and summing k*(1/2)^(2k-1), whose geometric weighted
  infinite sum is 8/9. This is a finite/compact-uniform polynomial
  inequality; no mean-value theorem or second source-defined atan.
  Then Q_N(x,h) differs from A'_N(x) by <=(8/9)|h| uniformly in N;
  combine the already-owned source uniform A_N tails and native derivative
  series convergence to construct the actual original Bishop atan
  factorDerivativeAt x with derivative geometric limit. The remaining
  comparison to Cayley requires original complex exp source derivative at
  its argument, normalization at zero, and uniqueness of
  (1+x²)F'=2i F, F(0)=1. Both x=1/5 and x=1/239 follow from the SAME
  one-parameter theorem. Do not introduce two pointwise derivative axioms.

The signed chosen complex exponent is now proved SOURCE-WRITTEN in
CM163BishopSelectedTauExponentExact.literalExponentSigned:
  2*pi_M*i*((-1+i sqrt163)/2) = -pi_M sqrt163 - i*pi_M.
FromTwoOriginalAtans.actualBishopCMQ composes that genuine literal
argument with the two-atom original Bishop complex exponential, via
componentwise same-Bishop-real carrier transport, to the existing
JInvariantBishopCM163SelectedDiskExact.q. Previous +i*pi_M argument was
NOT the literal 2*pi_M*i*tau; it is only period-equivalent after phase
evaluation. Current script check_paper9_machin_two_atom_cayley.py
blob 45c3ec9b4958be664583c8535d3ed8f88b2351d6 byte-matched locally
and passes negative imaginary exponent and incorrect positive argument
control; refreshed receipt Paper9OriginalMachinSelectedQPhase20261128.json.

Acceptance classification: new Agda all-N theorem and phase composition are source-written, not native Agda kernel accepted; local exact rational checks do not supply all-N Bishop inequalities or the actual exp/atan derivative-limit. Do not promote to unconditional original Machin q phase or Chudnovsky same-real; original Hecke CM root, original Bishop hypergeometric identification and all-index signed Hecke residual are still independent analytic source obligations. No CI used.


### 2026-11-28 — K05-PI native signed half-ball radius bridge (P0, larger cut)

Recovered paid owner: BishopFiniteSeriesAbsoluteBoundExact.finiteSeriesAbsoluteBound already supplies ALL-N original Bishop finite triangle; BishopOriginalFiniteLogQuotientUniformModulusExact.sourcePowerSecondQuotientMonotone already supplies nonnegative-endpoint native second-quotient radius order. Reuse those along with original K04d powerDifferenceFactorisation, originalPowerQuotientSecondOrder and original Machin odd reciprocal/sign magnitude theorems. NO new abstract norm, power series, or selected atan.

Committed new original Agda source (all kernel pending):
- BishopOriginalMachinSignedSecondTriangleExact.originalSecondAsActualFiniteSeries, originalCoefficientAbsolute, originalSecondTermAbsoluteOdd, originalSignedFiniteSecondTriangle and originalSignedFiniteSecondAbsoluteCoefficients: all original Nat-indexed S_N, original signed odd 1/(2k+1) and native finite sum. An incorrect even-index alternative was removed before final commit.
- BishopOriginalMachinSignedPowerRadiusExact.originalZeroStepAbsoluteRadius and originalSignedSecondBelowAbsoluteEndpoints: inductively compare all signed power quotients with original nonnegative absolute endpoints |x| and |x+h| via the exact K04d recurrence; originalSignedSecondBelowHalf then consumes existing LOG second-quotient radius dominance. This works for negative original inputs and h=0 in the source proposition.
- BishopOriginalMachinSignedSecondRadiusEnvelopeExact.originalSignedFiniteSecondBelowRadius: native ALL-N composition of source triangle + original odd coefficient + signed power radius, proving |S_N(x,h)| <= sourceRadiusBudget N at |x|,|x+h|<=1/2. SourceRadiusBudget is the LITERAL Bishop finite sum of original sourcePowerSecondQuotient(1/2,0,2k+1)/(2k+1), not a postulated constant or cross-carrier approximation.
- Companion Lean Integration/Paper9MachinSecondDefectMajorant.lean (f5c306d05484bd8ac13426490aaba32ac7f28028) source-writes the exact all-N rational identity B_N=sum_{k<N}2k/4^k=(8/9)*(1-(3N+1)/4^N)<=8/9, coefficient count and native-recurrence-shaped rawPowerZero/rawPowerSecond equal-endpoint formulas. No claimed Lean kernel acceptance.

Exact algebra: T_m(x,y)=sum_{j=0}^{m-2}(j+1)*x^j*y^(m-2-j), y=x+h. Thus for |x|,|y|<=1/2, |T_(2k+1)(x,y)|/(2k+1)<=k*(1/2)^(2k-1)=2k/4^k. This is a finite triangle/radius inequality and remains valid at signed/zero endpoints. Original Bishop source-level proof is constructed in the modules above, subject to native typecheck; the remaining scalar transport is to prove for ALL k sourceRadiusTerm k = R._⋆((2*k)/(4^k)) on the SAME Bishop carrier, using original Nat/odd reciprocal and bishopHalf=_⋆(1/2), then finite sum/rational order embedding B_N<=8/9. Do not assume or introduce 8/9 as a premise. The Agda source modules have NOT been native checked, and source-written inequalities are NOT kernel theorems yet.

scripts/check_paper9_machin_second_defect_radius.py exact Git blob d760fe5aa361d9b7e914616ae8aa36977517ec70 byte-matched and executed locally: 2,666 exact checks PASS across 100 formal power quotient/second coefficient recurrences, 1,001 exact rational closed-form budget stages and 8 signed endpoint pairs x 33 stage lengths. Receipt Docs/support/reference/Paper9MachinSharpSecondDefect20261128.json. This does not prove Bishop order or native executable proof.

AFTER native all-index radius budget: use existing original uniform atan function tails and original derivative-series geometric convergence to construct factorDerivativeAt of actual Bishop atan; then prove a SINGLE exact analytic exp_C(2i atan_B x) Cayley equation for the original Bishop x in compact half-ball via original complex exponential origin derivative and ODE uniqueness; specialize x=1/5,1/239; consume existing TwoPoint -> SelectedTauExponent -> original selected q route. Parallel P0 analytic cuts remain CM Hecke all-index root, signed reciprocal literalResidual and original Bishop factorial E4 hypergeometric H²/derivative. Keep all branches advancing rather than waiting on a missing cross-repository type coercion. No CI.


### 2026-11-28 — K05-PI original half-radius rational readback and native derivative budget

New DASHI/Analysis/BishopOriginalMachinSecondRadiusRationalReadbackExact.agda is source-written, kernel pending. It reuses literal K04d sourcePowerSecondQuotient and the original qPowEmbeds to prove the finite first/second quotient recurrences on the SAME Bishop carrier and their exact unnormalised rational readback by structural induction. Rational recurrence:
 qZero(0)=0, qZero(n+1)=qZero(n)/2+(1/2)^n;
 qSecond(0)=0, qSecond(n+1)=qSecond(n)/2+qZero(n);
 qRadiusTerm(k)=qSecond(2k+1)/(2k+1);
 qRadiusBudget(N)=sum(k<N,qRadiusTerm(k)).
Proof functions qZeroEmbeds, qSecondEmbeds, qRadiusTermEmbeds, qRadiusBudgetEmbeds use existing Bishop rational power and sum transport, not a second real or analytic limit.

Lean companion Integration/Paper9MachinSecondDefectMajorant.lean at 349b0b84900b97d8b60088acc88ef020bf05dd28 adds sourceHalfRadiusTerm_eq_radiusTerm and sourceHalfRadiusBudget_le: the same rational recurrence gives qRadiusTerm(k)=2k/4^k and qRadiusBudget(N)=8/9*(1-(3N+1)/4^N)<=8/9 for ALL N. This is PURE RATIONAL source-written algebra, not automatically an Agda theorem and not kernel-run.

New BishopOriginalMachinSharpUniformDefectConsumerExact.agda (74fa1359cb3c) explicitly isolates the ONE native Agda rational proof producer OriginalRationalBudgetOrder, precisely the Q._≤_ inequality qRadiusBudget(N)<=8/9 on Data.Rational.Unnormalised. GIVEN that concrete arithmetic witness, existing original Bishop signed finite triangle, signed second radius envelope and exact rational finite readback yield all-N |S_N(x,h)|<=8/9 and |Q_N(x,h)-original geometric derivative polynomial(x,N)|<=|h|*(8/9) for |x|,|x+h|<=1/2, including h=0. That record is NOT YET INHABITED; do not mark the bound unconditionally proved. The next P0 step is to port the rational Lean induction into native Agda using existing rational Q.*≡*, Nat/Signed solver, Fractions.natFractionLe and canonical order transport, then typecheck all new sources.

scripts/check_paper9_original_half_radius_readback.py exact Git blob 8cbb6f11d18baba7e85065e33aa7668532a6370d matched locally executed /tmp/p9_half_budget_test.py and passed 5,120 rational recurrence/readback tests over 1,024 stages, 2 deliberately corrupted controls rejected. Receipt Docs/support/reference/Paper9OriginalHalfRadiusReadback20261128.json. Prior 2,666 algebraic checks remain separate. Neither proves native Agda analytic derivative of limit. After the rational order and native checking, reuse original uniform atan tails, derivative-series convergence and source exponential/Cayley ODE to discharge the two actual Machin evaluations. Parallel analytic CM Hecke root, original Bishop factorial hypergeometric H/J1, signed all-index Hecke residual still open. No CI or native acceptance claimed.


### 2026-11-28 — original Bishop finite Machin second-defect closed at source level by positive slack and direct term normalization

This replaces the earlier *uninhabited* broad OriginalRationalBudgetOrder and per-term normalization records with explicit source-writing. Do not leave them listed as unchecked separate mathematical problems.

1. DASHI/Analysis/BishopOriginalMachinPositiveSlackBudgetExact.agda: all-N constructive Nat p_0=1,p_(n+1)=4p_n, slack_0=0,slack_(n+1)=4slack_n+9n and p_n=(3n+1)+slack_n, hence slack<=p. Owns powerFourDecomposition, positiveDenominatorNonZero, positiveCrossOrder, positiveBudgetBelowEightNinths, positiveBudgetStepCross and positiveBudgetStep. The exact positive unnormalised rational B_n=8slack_n/(9p_n) <=8/9 is derived from the existing Nat fraction-order theorem; no negative tail, arbitrary field or new analytic hypothesis. Existing Nat solver, NonZero constructors, and Q.*≡* used.
2. DASHI/Analysis/BishopOriginalMachinHalfRadiusTermNormalizationExact.agda: qZeroScaled=2n, qSecondScaled recursion s_(n+1)=s_n+4n, closed s_(n+1)=2n(n+1), and powerTwo(n)=2^n. Proves/attempts source-written qPowHalfNormal, qZeroNormalizes, qSecondNormalizes, even/odd source exponent normalization, oddPowerTwoIsTwiceFour and originalTermNormalizes for the actual Q coefficients qRadiusTerm(k) = 2k/4^k, preserving the exact odd 2k+1 before cancellation. Q.*≡* integer ring certificates cross-check.
3. DASHI/Analysis/BishopOriginalMachinRationalSlackToUniformDefectExact.agda: qRadiusBudgetEqualsPositiveSlack by structural induction using the positiveBudgetStep and originalTermNormalizes; originalBudgetOrder now *constructed* from one per-term shape and previous positive Nat inequality. The new HalfRadiusTermNormalizationExact.originalTermShape supplies that record (source-written) and CompletedFinite.Native wires to the original Bishop all-N |S_N|<=8/9 and |Q_N-original finite atan derivative|<=|h|*8/9. This is the actual original Bishop carrier; no proxy atan and no classical pi substitution.
4. Independent local exact Python Fraction replay: positive-slack 401 stages PASS, and SymPy four raw polynomial cross-product identities qZero/qSecond/odd/positiveBudgetStep all simplify to zero. Earlier 1024-stage qZero/qSecond and 5120 exact comparisons remain separate. Receipt Docs/support/reference/Paper9MachinPositiveSlackSourceClosure20261128.json; *no native Agda compiler available*, no kernel check and no CI. Source-written type signatures/tactics must be run and corrected before any "theorem proved" promotion. Existence of source term is not kernel acceptance.

Next K05-PI analytical P0: use existing original Machin half-ball function uniform tails, original geometric derivative-series convergence, and the now source-written finite quotient radius majorant to build the actual original infinite factor quotient q(x,h) by uniform Cauchy of finite q_N(x,h) and continuity at h=0, then the BishopFactorDerivativeAt field for original bishopAtanHalfBall. Control boundary point endpoints via a compact inner half-ball or one-sided extension; derivative cannot be asserted on all |x|=1/2 with arbitrary h inside without domain restriction. Then prove ONE original Bishop Cartesian exp/atan vs rational Cayley first-order ODE (with true source Cauchy-product derivative, origin value and constructive uniqueness), specialise x=1/5 and 1/239 to discharge the existing two atomic K05 source inputs. All-index Hecke CM j root, same-source Bishop hypergeometric factorial H/J1 square and shared Euler flow, and signed actual reciprocal Hecke product still independent open original analytic producers. Native same-real endpoint remains composed conditionally. Do not start new terminal wrappers or treat finite scripts as kernel/analytic proofs.


## 2026-11-28 — WHOLE-PROOF OWNER RECONCILIATION / NON-DUPLICATION CUT

**Repository audit provenance.** PR #1546 remains open, comparison with \`master\` is **767 ahead / 74 behind** at head \`f4bb9634e039d60c86fccaaf12693e55faf28808\`; companion Lean \`research/paper9-original-eisenstein-derivative-20261125\` vs \`main\` is **122 ahead / 7110 behind**. These are genuinely divergent branches, not evidence the audited theorem was superseded on either branch. Historical search alone is not a replacement for exact file inspection. No blanket rebase. The current HEAD after the implementation below supersedes that sampled audit HEAD.

### A. Machin phase — major previous gap reports are FALSE

1. \`DASHI/Analysis/BishopOriginalMachinAtanSecondOrderExact.agda\` ALREADY owns original finite signed odd reciprocal \`secondPartial\`, \`originalQuotient\`, \`termDefect\`, \`partialDefect\`, \`uniformSecondBound\`, \`finiteRemainderBound\` and **\`actualRemainderBound\`** for *the original Bishop arctangent limit*, using the original derivative-series limit and finite positive-radius mesh. It establishes an O(h²) actual remainder on original NONNEGATIVE \`x\` and \`x+h\` in the Bishop half-ball. Its constant is 8, not the later sharper 8/9. It does not by itself claim symmetric signed full-ball differentiability, but that is NOT necessary for the original positive 1/5 and 1/239 endpoints.
2. \`BishopOriginalMachinAtanSmallPhaseExact\` uses original value/derivative and sine/cosine Taylor bounds; \`BishopOriginalMachinCayleyConservedPhaseExact\` proves a conserved complex phase has O(h²) increments; \`BishopOriginalMachinCayleyEndpointExact\` uses original clipped equal meshes and a vanishing budget to prove **\`originalFive\`** and **\`original239\`** with EXACT types \`TwoPoint.OriginalAtanFiveCayleyEvaluation inputs\` and \`OriginalAtan239CayleyEvaluation inputs\` for each \`Round11.BishopCutset\`. It also writes \`originalQuarterEquality\` and **\`originalFirstZero\`**. These proofs are SOURCE-WRITTEN, not kernel-checked in this tranche; inspect the existing code before reporting them unpaid. In particular, ODE uniqueness and derivative-of-limit interchange are NOT independently necessary to the existing clipped-mesh original phase route.
3. \`BishopMachinCayleyNativeProductFirstZeroExact.originalNativeImaginaryExpProduct\`, \`BishopMachinTwoPointCayleyCompositionExact.nativeCombinedCayleyFromTwoOriginalAtanValues\`, \`BishopMachinSelectedImaginaryPhaseWeldExact.machinImaginaryPhaseFromTwoOriginalAtans\`, \`CM163BishopOriginalQPhaseFromCayleyExact.FromTwoOriginalAtans.originalQ\`, and \`CM163BishopSelectedTauExponentExact.FromTwoOriginalAtans.actualBishopCMQ\` already form the CONDITIONAL selected complex phase.
4. NEW DIRECT SOURCE attachment in \`CM163BishopSelectedTauExponentExact.FromOriginalBishopEndpoint\`: for an EXISTING \`Round11.BishopCutset\`, use \`Endpoint.originalFive inputs\`, \`Endpoint.original239 inputs\` directly to get \`actualOriginalCMQ\`. The two atomic phase obligations disappear entirely from this branch of the proof. Preserve signed exponent \`2*pi_M*i*tau = -pi_M*sqrt(163) - i*pi_M\`, not a positive imaginary argument.
5. **Remaining Machin native seam:** source/typecheck of the full endpoint/phase import DAG and a constructed canonical \`Round11.BishopCutset\`. The latter record contains the genuine \`BishopElementaryPowerSeriesData\` and configured source sine/cosine term definitions; \`BishopCanonicalNegativeLogSameObjectExact.canonicalNegativeLogRound11\` transforms an existing cutset but is NOT an unconditional constructor. \`BishopElementarySeriesTermsExact.asBishopElementaryPowerSeriesData\` and \`BishopMachinConfiguredTrigPiExact\` are relevant source owners for constructing a concrete cutset. Do not manufacture cutset evidence or silently import a classical complex π.
6. The separately developed sharper \`8/9\` branch (\`BishopOriginalMachinAtanQuotientSecondOrderExact\`, \`SignedPowerRadiusExact\`, \`PositiveSlackBudgetExact\`, \`HalfRadiusTermNormalizationExact\`) is a valuable optional symmetric-half-ball *numerical improvement*, NOT a gate to finishing the original Machin phase. Retain original source + tests, but freeze further micro-lemmas until kernel typechecking shows a need.

### B. CM163 Hecke/root — reuse already present machinery, identify the true analytic gate

Existing original Agda owners:
- \`CM163BishopHecke41FormalCyclotomicNormExact\`, \`LiteralResidualReflectionExact\`, \`PolynomialEvaluationExact\`, \`ActualSeriesEvaluationExact\`, \`CuspResidualExact\`, \`CuspTailFactorExact\`, \`CuspLimitExact\`, \`UniformCuspBoundExact\`, \`ActualCrossExact\`. The *actual product* and polynomial are already constructed as two sides of a same-source residual. \`CuspTailFactorExact.factor\` extracts a zero prefix as a power of the original uniformizer, while \`CuspLimitExact\` controls the normalized cusp residual under the existing uniform bound. \`ActualCrossExact.normalizedCross\` already transports the genuine product/polynomial cross through the signed reciprocal coordinates.
- \`JInvariantBishopCM163TailGuardExact.negativeDelta\`, \`xPositive\`, \`yPositive\`, and \`Root\` already construct the original selected real quotient and its apartness/sign; do NOT conflate this with identifying the exact algebraic root integer \`K=-262537412640768000\`.
Existing companion Lean owners:
- \`Paper9HeckePoleRemoval.normalizedResidualZero\`, \`diagonalFromRamifiedReplay\`, \`sliceFromRamifiedReplay\` are genuine original analytic *consumers* of the ramified cusp factorization, not independent universal modular-identity axioms.
- \`Paper9ActualCMRoot.cmRootFromDiagonal\` already supplies the exact selected value under the original \`diagonalGate\`, finite shifted coefficient conditions, dominance, and a dyadic real enclosure. \`Paper9ActualCross.actualRawCross\` and \`normalizedActualCross\` consume actual finite packet booleans and specified original local chart jets. **Do not** repeat these polynomial constraints as missing new theorems.
**True weld:** specialize ramified original uniformizer/residual and analytic cusp factorization to the selected Bishop q; produce actual all-index polynomial identity/diagonalGate, exact selected CM enclosure and compatibility of Bishop and companion complex objects. The finite 126 packet checks alone do not produce the all-index vanishing residual. Verify each analytic premise directly against the cited module *signature* before claiming it is already inhabited.

### C. Euler/hypergeometric/J-jets — existing selected point carries much more than a finite regression

Companion Lean already owns \`Paper9ActualCMPoint.selectedHyperAtCM\`, \`selectedFirstJetAtCM\`, \`Paper9ActualJSourceJet.jQEuler\`, \`jExtSecond\`, \`Paper9ThetaEisensteinSameObject.thetaE4_eq_original\`, and \`Paper9HypergeometricQTransport.ramanujanQ\`. \`Paper9SelectedOriginalQJetAtCM.actualSelectedHyperAndJets\` bundles the selected-point identity and cleared Euler j-jets (source-written, not checked); \`Paper9OriginalRamanujanTwoJetWeld\` is redundant as an *analytic differentiability* producer but useful for cleared algebra on the precise native Bishop fields.
Original Agda already has \`BishopChudnovskyNativeEulerLimitsExact\` (\`H\`, \`J₁\`, convergence), \`NativeFactorialEulerAttachmentExact\` (same factorial stream), \`JInvariantBishopCM163NativeJetReductionExact.clearedFromChain\`, \`periodFromThree\` and the original signed reciprocal disk jet/cross module \`DiskCrossCoefficientExact.signedJetFromLiteral\`.
**True weld:** actual original Bishop factorial H/J₁ at SAME selected q equals hypergeometric E4 root and derivative, retaining q-Euler vs τ-derivative \(2\pi i\) normalization. The cross-prover transport must be an explicit same-carrier identification; Lean's selected theorem is not an Agda theorem by declaration. The signed reciprocal Hecke two-jet residual also needs an actual all-index source proof, not only literal finite packet algebra.

### D. Terminal π / GMP — already-written consumers

\`CM163BishopOriginalSameSourceClosureExact.OriginalCMProducers\` explicitly collects the original CM root, hyperSquare, actual shared chain, first/second original q-jets and literal signed Hecke residual; \`NativeJetReductionExact.periodFromThree\` and \`NativePeriodProductExact.periodToSameReal\`, \`periodToExpanded\` consume it. Do NOT add another target π or conditional same-real theorem. A record *type* without a value does not establish its producer hypotheses.
Production: original in-place GMP and binary-split quotient receipts through 10M, predictive GMP through 1M, exact cross arithmetic, original Machin common floors through 10k and native production-trace replay described above. \`Paper9GmpTraceChecker.lean\` still requires an exact serialization parser/native checked receipt; current performance claims are local reference, not global SOTA. Distinguish full-GCD carrier bits, actual RSS, latency and decimal strict-floor gates.

### E. Coarse-to-fine EXECUTION ORDER / acceptance

- **P0 native source build**: selected Machin phase and existing endpoint DAG first, then CM actual residual/cusp modules, native factorial/Euler modules and terminal \`OriginalCMProducers\`. Run Agda and Lean with pinned source/vendor paths where available; no CI. This runtime has no \`agda\`, \`lean\`, \`lake\`, or cloned repo. GitHub contents comparison is NOT native proof acceptance.
- **P1 actual Hecke**: original ramified residual → uniform cusp domination → analytic zero residual → polynomial identity → selected exact root, with a source explicit signed reciprocal chart/jet.
- **P1 actual Bishop hypergeom**: exact factorial coefficients → actual convergent generating series → ODE uniqueness/analytic continuation on SAME selected Bishop point → E4 square/first Euler derivative → signed correction.
- **P1 terminal**: construct the *value* of \`OriginalCMProducers\`, call existing \`nativePeriod\`, \`sameReal\`, \`universalRawCross\`; check that the theorem is genuinely all-index and no assumed target equality sneaks into any producer.
- **P2 arithmetic**: execute committed Python full trace reader and strict independent common-floor wrapper byte-for-byte; check corrupted sign, divisor, leaf order, square-root witness and strict upper floor. Matched speed/RSS before enabling predictive mode.
- **Negative controls**: no phase substitution of classical \`Real.pi\`, no positive-\(i\pi_M\) literal argument, no finite packet→universal cusp inference, no uninhabited cutset, no hidden \`postulate\` or \`sorry\`, no uncompiled proof promoted as kernel checked.

**Prior-art attribution:** Machin 1706, classical modular form/Hecke and Chudnovsky theory, Bishop–Bridges constructive analysis, Murray's Agda work and pinned viktorcsimma/bishop, Mathlib original analytic operators. DASHI contributions are source-native signed coordinate transports, exact reproducible finite certificates and proof-assistant-specific composition. Existing \`ProofLevel=machineChecked\` constants are module-declared and are not an external execution receipt for newly written modules.


### 2026-11-28 — P0 SAME-SOURCE PHASE × HECKE CUSP COARSE WELD IMPLEMENTED

New implementation \`DASHI/Moonshine/CM163BishopOriginalPhaseHeckeCuspWeldExact.agda\` (commit \`88fc9a083300d972d044b264911129a7c2a4fc01\`) threads the SAME \`Round11.BishopCutset\` through:
- \`CM163BishopSelectedTauExponentExact.FromOriginalBishopEndpoint.actualOriginalCMQ\`, which now consumes \`BishopOriginalMachinCayleyEndpointExact.originalFive/original239\` directly, with **no fresh arctangent/exponential/Cayley proof obligations**, at \`2π_M iτ = -π_M√163 - iπ_M\`;
- \`JInvariantBishopCM163TailGuardExact.negativeDelta/xPositive/yPositive\` on the selected original negative-real q;
- \`CM163BishopHecke41CuspLimitExact.At.diagonalZeroAlong/sliceZeroAlong\` on ONE original selected cusp path, retaining \`UnitGate\`, \`DiagonalGate\`, \`SliceGate\`, reference-disk inclusion and cusp phase null convergence as exact typed obligations;
- \`CM163BishopHecke41CuspResidualExact.At.dS/dT/sS/sT\`, the existing original S/T invariance of BOTH residuals.

The source module does **not** pretend that two original cusp limits imply global Hecke identities. New exact negative control \`scripts/check_paper9_modular_cusp_rigidity_negative.py\` (commit \`8ddbe5a1f530986da5c1b2dddea91bd5ca1eb8af\`) expands \`1/j = q -744q²+356652q³-140361152q⁴+…\` from original E4/E6/Delta integer series through degree 80. It is a genuinely nonzero, modular-invariant MEROMORPHIC function with zero cusp limit; poles at elliptic j zeros defeat the naive conclusion. Formal arithmetic locally PASS. Therefore the true global proof must establish pole-free holomorphic modular residual, constructive bounded compactification/rigidity, THEN all-point d=s=0, selected exact root and reciprocal signed two-jet; finite packet and cusp-local bounds cannot substitute. The local negative control was executed from equivalent code but committed bytes were not executed byte-identically.

Exactly matched source-owner audit saved in \`Docs/support/reference/Paper9WholeClosureSourceOwnerAudit20261128.json\` (commit \`b8fd859e0e59aff64581c103b3f12725c18e2ff0\`). It records false-open items, original and companion precise constructors, original geometry/phase/Hecke/factorial source producers, attribution and runtime evidence. Searches did NOT identify a standalone original Bishop pole-free modular rigidity theorem; this is negative search evidence, not a mathematical absence proof.

**Priority correction**: STOP spending P0 on speculative infinite atan derivative/ODE uniqueness; original clipped-mesh endpoint and actual remainder are already source-written for the relevant positive values. Keep sharp 8/9 line as optional, kernel-checkable improvement. Allocate next proof blocks in parallel:
(1) Hecke pole-free global rigidity and actual selected j integer root;
(2) SAME-Bishop hypergeometric H/J₁ → E4 square and Euler chain at original q;
(3) actual signed reciprocal Hecke jet residual from original product;
(4) precise Round11 cutset construction and native Agda/Lean typecheck;
(5) original trace serialization and strict decimal floor production acceptance.
Recompute provenance against master/PR heads; avoid wholesale rebase. Source-written does not mean typechecked; no native compilers and no GitHub CI here.


**Exact-source regression update:** `check_paper9_modular_cusp_rigidity_negative.py` committed blob `b4dbc22c0c3e54a452c9729d6d0aa54a378af725` was locally reproduced byte-identically (`git hash-object` match) and executed at degrees 80 and 256: both exact formal products PASS, with `1/j` zero at cusp and nonzero q-germ. This is a negative control proving the necessity of pole-free global rigidity; still not an Agda or Lean kernel execution.


### 2026-11-28 owner correction #2 — Lean global holomorphic modular rigidity IS ALREADY PAID

Exact companion source inspection overrides earlier overly broad statements about a missing general modular rigidity theorem. \`Integration/Paper9HeckePoleRemoval.lean\` ALREADY proves \`jHolo\`, \`productHolo\`, \`polynomialHolo\`, \`invariantZero\` (using pinned \`Integration.MoonshineLevelOneWeightZeroPinned.levelOne_weight_zero_const\` on weight-zero cusp forms), \`diagonalIdentity\`, \`sliceIdentity\`, \`normalizedResidualZero\`, \`diagonalFromRamifiedReplay\`, \`sliceFromRamifiedReplay\`, and \`actualCMDiagonalRoot\`. This is the correct global theorem on the **Lean/Mathlib analytic carrier**. Do NOT request a fresh Lean maximum-modulus or compactified modular curve theorem. The exact negative control \`1/j\` remains valid: it violates the global holomorphy hypothesis; it cannot invalidate or replace the existing correct \`invariantZero\`.

Also existing \`Integration/Paper9HeckeFiniteRemainder.lean\` owns \`Rem\`, \`remSub\`, \`remMul\`, \`remProd\`, \`remMonomial\`, \`remWeaken\`, \`diagonalNormalized\`, \`sliceNormalized\`, \`normalizedColumnEval\`, \`residualGermToCusp\`. New companion commit \`7228c73b32615bdfd21d20a288c583ce4d8de1bf\` adds \`bothActualHeckeIdentitiesFromRamifiedGerms\` (3363 diagonal and 1723 slice orders, same actual polynomial P and original fixed K) and \`actualCMPolynomialRootFromRamifiedGerms\`. These compose genuine continuous germs + ramified source readout with ALREADY PROVEN source-written global weight-zero rigidity and CM diagonal root consumer. This is a coarse whole-branch endpoint, no new analytic axiom; the hypotheses are exact finite analytic germ obligations, NOT evidence that those germs have been supplied. Lean file not typechecked in this tranche.

**Actual P0 gap (more precise)**: instantiate the TWO exact \`Rem 3363\`/\`Rem 1723\` hypotheses from original \`Junit\` factorial/Hecke normalized Laurent streams and their 82/42 source integer packet gates. The Agda owners \`CM163BishopHecke41PacketPrefixWeldExact.At.UnitGate\`, \`DiagonalGate\`, \`SliceGate\` are TYPES, not automatically inhabited values; \`CM163BishopHecke41LiteralResidualReflectionExact.At.diagonalZero/sliceZero\` prove the required 3362/1722 coefficient vanishings GIVEN gates. Need finite gate construction, actual analytic germs and original Bishop-to-Lean coefficient/carrier parity. Once those are in hand the existing Lean theorem yields global identities and actual CM polynomial root; then \`Paper9ActualCMRoot.cmRootFromDiagonal\` still requires its exact dominance and half-unit enclosure. For fully original Bishop native proof, the corresponding global holomorphic rigidity transport remains open despite Lean ownership.

Do not conflate diagonal coefficient count 82, ramified zero orders 3363, and proof of all-index coefficient correctness. Preserve exact 41-fold phase geometry. Do not promote sources without native Lean or Agda kernel execution.


### Exact Lean finite-gate producer inventory (2026-11-28 final check)

\`Integration/Paper9ExecutableCM163.lean\` ALREADY defines the original INTEGER recurrences and arrays \`u,j,ld,nd,ls,ns\`, and the decidable \`unitOK\`, \`diagOK\`, \`sliceOK\`; \`unitDown\`, \`diagonalOfCheck\`, \`sliceOfCheck\` already consume their \`=true\` evidence. \`Integration/Paper9CM163LiteralPacket\` holds the literal 83/43 integer coefficient arrays. \`Integration/Paper9ActualCross\` consumes the same booleans and separately \`jetOK\` for the signed reciprocal jet. The flags are **defined**, not proved true by merely evaluating an external Python counterpart; the file explicitly comments out \`#eval (unitOK,diagOK,sliceOK)\` and disclaims native-decide acceptance. Native proof that the actual booleans are true, with bounded computational reflection/compiled checker or source-proved integer certificates, is the sharp finite-gate completion. Do not recreate the integer recurrence arrays or import an untrusted external receipt as a Lean proof. If expensive, checkpoint and evaluate flags separately and retain exact source SHA.

Cross-repository original Bishop gates are \`CM163BishopHecke41PacketPrefixWeldExact.At.UnitGate\`, \`DiagonalGate\`, \`SliceGate\`: source-written finite coefficient reflection consumers, not automatically equivalent to those Lean booleans. Actual source witness transport remains mandatory.

This final check gives a practical whole-programme order: verify the 3 finite gates, attach actual \`Rem 3363\`/\`Rem 1723\` normalized germs, consume already-written Lean global Hecke/root and Agda Bishop cusp sources, attach original factorial Euler/H/J₁ and signed reciprocal jet, then instantiate original \`OriginalCMProducers\` and run kernel + production acceptance. No new analytic consumer or π endpoint definition.


### 2026-11-28 — native finite gate acceptance SOURCE FILE written (Lean companion)

\`Integration/Paper9NativeOriginalFiniteGateAdmissions.lean\`, commit \`d1368c0205b79e01de6f2edbc3b2e2b05f5b1602\`, defines **ordinary kernel** \`by decide\` proof candidates \`originalUnitOK\`, \`originalDiagonalOK\`, \`originalSliceOK\` from the exact original \`Paper9ExecutableCM163.unitOK/diagOK/sliceOK\`, then consumes pre-existing \`diagonalOfCheck/sliceOfCheck\` to obtain native original finite diagonal and slice certificates. It does NOT use \`native_decide\`, a Python-issued Boolean, or a new integer carrier. It deliberately fails if any actual flag is false. It has **not** been compiled. Source-written flags, especially the 3322-unit computation, may exceed available resource limits; validate each with 90s local checkpoints and record logs. If resource-bound, decompose the original integer recurrence proof into certified chunks instead of asserting the Boolean.

This finite-gate source is parallel to the already-written \`Paper9HeckeFiniteRemainder.bothActualHeckeIdentitiesFromRamifiedGerms\` on the true analytic residual. Even successful gate execution does not prove the necessary \`Rem 3363/1723\` continuous analytic normalized germ equalities or original Bishop–Lean carrier transport. Existing \`Paper9HeckePoleRemoval.invariantZero\` pays the Lean global modular step once these actual source producers are attached.


### Concrete BishopCutset input audit — do not assume canonical cutset exists

Source audit of the actual constructors recovers the precise entrypoint dependencies. \`BishopReciprocalCoefficientConstructionExact.asBishopReciprocalCoefficientData\` takes \`FactorialRecurrenceReceipt\` and \`UnnormalisedRationalCoefficientCodec\`; that module's declared receipt levels mark both inputs *conditional*. \`BishopElementarySeriesTermsExact.asBishopElementaryPowerSeriesData\` takes those coefficients and \`BishopElementarySeriesConvergenceProofs\`, likewise a nontrivial input record. \`BalabanBishopConfiguredTermIdentificationExact.ConfiguredConcreteTermDefinitions\` demands literal source sine/cosine signed factorial term equalities; its proof-level marks that source-definition input conditional. \`Round11.BishopCutset\` is exactly \`elementarySeries\` plus \`configuredDefinitions\`. \`BishopCanonicalNegativeLogSameObjectExact.canonicalNegativeLogRound11\` maps ONE existing cutset to another and does NOT instantiate a default; \`BishopConcreteTrigSeriesConvergenceExact\` consumes an existing cutset. Therefore the actual original Machin phase \`FromOriginalBishopEndpoint.actualOriginalCMQ\` is source-written *parametrically for a cutset*, not yet unconditional on a constructed canonical real-data package. Reuse the existing factorial denominator, codec and convergence owners; do not introduce an empty record or assume an original complex transcendental source.

The full priority is now (a) native pure-kernel finite gate admissions on Lean; (b) original analytic \`Rem\` 3363/1723 for actual Hecke normalized streams, then already-owned Lean global modular constancy; (c) construct the genuine Round11 canonical source coefficients and term/convergence records to instantiate the Bishop phase/cusp module; (d) reconcile Bishop original factorial H/J1 and selected complex root/jet, then inhabit \`OriginalCMProducers\`; (e) run Agda/Lean kernels and source-byte production GMP trace checks. The other sharper 8/9 uniform atan path is optional and not a blocker of the existing original positive-half-ball clipped-mesh Cayley endpoint.


### 2026-11-28 — literal H1 to original evaluated terminal cone

Reopened actual sources at d269fec0660a: FiniteDivisorConvolutionRamanujanIntegerExact (identity1..4, convSym, c11, c13, c33, sigma7, c15Scaled), JInvariantBishopLiteralRamanujanExact (ramanujanX/Y/E), JInvariantBishopFormalHyperClearedODEExact (hyperSquare/hyperClearedJet), JInvariantBishopCM163FormalEvaluationConsumerExact, NativeEulerLimitsExact and NativeJetReductionExact. The older H1 gap in the 26 November proof notes is superseded at source level by these actual all-index declarations; native kernel acceptance remains open. The formal and weighted two-cut frameworks already exist. Do not rebuild them or require a new ODE uniqueness theorem.

Commit 6dece4f6cc9b7d4851b70fac1ef4e16c08a65bb5 specializes the existing AtOriginalZ.WithMajorants consumer to literal Ramanujan producers: originalSquare, originalClearedJet, originalPeriod, originalSameReal, originalRaw. This bypasses the extra arbitrary chain-derivative l parameter in OriginalCMProducers using the existing direct cleared jet and periodFromThree route. No terminal equality assumed. Source-written, not compiled.

Remaining whole-cone inputs: zAbs and zEval at original q; two outer majorant convergence witnesses hm/jm; actual X/Y/3DX absolute convergence and same-object evaluations; CMRoot and SignedJet. H4 exact norm budget in Paper9WeightedTwoCutCompositionMaxCut20261126.md is 1517/4558 < 1/3, with actual norm bindings outstanding. Root and signed jet remain genuine analytic obligations, not finite scans. Concrete BishopCutset and actual Hecke normalized germs (3363/1723), finite gates and same-carrier transport remain parallel upstream requirements. Run local native cone, no CI; distinguish type errors from missing mathematical producers. Master head from PR metadata 5331203e67ffbd23478da44fae09844028623b4c; no exhaustive fresh master/donor file comparison in this tranche. Existing attribution retained.


### 2026-11-28 — whole-cone producer reconciliation and concrete elementary source

Fresh targeted audit at starting HEAD 108db7eff840: PRs #1552 fe44b21d, #1529 d8956bb9, #1551 c5458b64, #1533 f2398bfa, #1353 fad22a83, #1556 37307d97. Master compare from 5331203e: 55 returned changed paths, no targeted Bishop/Hecke/CM163/Modular paths. Default-branch searches recovered BishopExponentialSeriesConvergenceExact, BishopConcreteAbsoluteSeriesConvergenceExact (conditional on Round11), BishopOriginalExponentialUniformCompactTailExact, BishopCanonicalNegativeLogSameObjectExact and BalabanCMP109BishopRootFreeSeriesExact (local quarter-radius, not global). Not exhaustive history or a fresh Lean audit.

C0 source-written construction: BishopConcreteElementaryCutsetExact.agda (b77e11aa, ed8dedb9) selects literal signed odd/even factorial terms, original exp and canonical negative log; uses absRead and twoStep on the existing global factorial ratio bound to construct sectorAbsolute and concreteCutset. Configured sine/cosine definitions are refl. Legacy Set-valued metadata is not proof evidence. CM163BishopOriginalPhaseHeckeCuspWeldExact.ConcreteOriginal (a99a3859) instantiates the original phase/cusp cone. Kernel pending; no claim of accepted cutset.

H1-H4 source owners recovered: LiteralRamanujanExact; FormalHyperClearedODEExact; CM163LiteralRealSliceEvaluationExact (xAbs,yAbs,xEval,yEval,uEval and all Euler jet families); CM163LiteralNormBudgetExact (actual innerBound/discBound); CM163ReciprocalEvaluationExact (inverseBound,zBound,zNormSmall,zFromRoot); CM163HyperMajorantsExact.AtRoot (hMajorant,jMajorant,uAbs,rawFromCM). These replace the older open H4 norm/majorant inventory at source level. Do not rebuild. Native verification required.

C2/C3 reverse terminal: LiteralTerminalExact.periodFromDiagonalAndRay consumes only actual diagonal zero and OriginalRayResidual (sharp enclosure and quotient jets internal). SelectedRootWeldExact.rootFromResidual consumes actual d Fixed.p=0. SignedRayExtractionExact.rayFromActual consumes normalized nonzero coordinate sequence, three actual branch jets, finite rest slope limit and pointwise d/s zeros. ActualJLogPhaseJetExact.actualLogJet and ActualJLocalSecondJetExact.actualJ already construct local jets; ReciprocalGeometryExact owns alpha/beta pullback algebra; RestSlopeLimitExact.actualSlopeFromReverseSlice owns finite slope readback from reverse slice. Do not rebuild these.

Remaining mathematical max-cut:
1. Native finite unit/diagonal/slice gates and arbitrary target slice coefficients; Lean by-decide candidates are not Agda witnesses. Construct genuine ramified analytic remainder 3363/1723 and same-source normalized product; attach original pole-free modular rigidity (Lean existing owner, Bishop transport not established). Invariance plus cusp zero alone is insufficient (1/j negative control).
2. Construct actual cusp sequence inside the bounded reference disk; use concrete original phase and existing cusp limits. Lattice/Fourier identity source owners must be checked for exact same-carrier attachment, not assumed from numerical agreement.
3. Construct actual nonzero reciprocal disk ray, three normalized quotient branches, phase increments and second-jet coefficient transport to original QJ.a/b; all forty chart continuity and arbitrary reverse-slice center equality. Feed existing rayFromActual, not a fresh terminal theorem. Root and ray share same original residuals.
4. Native terminal same-real and universal raw cross; exact committed GMP source acceptance and matched runtime/RSS remain separate. Run local bounded kernel checks; no CI. All newly written source uncompiled, no new executed SymPy checks. Preserve historical attribution.

### Native gate admission cut
Commit 34455796c720 adds CM163BishopHecke41NativeGateAdmissionExact.agda: concrete original unit/diagonal/slice gates via from-yes of Cert.unitCheck/diagCheck/sliceCheck; expensive separate kernel target, not yet executed. Existing PacketPrefixWeld and CuspResidual diagonalFactor/sliceFactor then provide exact t times convergent tails on the actual original source. Remaining: actual cusp ray, global pole-free rigidity, arbitrary target reverse slice, actual reciprocal disk ray/jet binding. No CI or proof promotion. Default-branch search for Bishop modular weight-zero rigidity returned no relevant direct owner; Lean transport remains open. Native gate target may be computationally prohibitive; split admissions or proof-producing optimized recurrence if needed, never replace with unchecked Boolean.

### Reverse slice cancellation
Commit ae2394a4339a adds CM163BishopHecke41ReverseSliceCancellationExact.agda: productFactor, packetFactor, reverseSlice, centerSlope. The two actual fixed chart values at K factor the full Fin42 product as w² times forty-factor rest. The literal packet has the same double zero. Cancel only apart w², then reuse centerSlopeFromReverseSlice. Remaining inputs are chart values equal K (SelectedFixedCharts and SelectedRootWeld rootFromResidual, not a new root assumption) and actual reverse product identity at K+w (arbitrary-target global identity and symmetry, not supplied by the fixed-target residual alone). No inverse j chart or apartness of colliding branches required. Kernel pending, no CI or local execution in this cut. Next attach selected-root/chart transport, arbitrary-target polynomial identity, actual null ray and jet transport; global pole-free rigidity remains open.

### Canonical matrix-to-ray closure reconciliation
Recovered CM163BishopHecke41MatrixSymmetryExact.agda already owns selectedK/selected0/selected1, splitSelected, reverseComplement, originalCenterSlope and the finite matrix symmetry. Therefore ae2394a4339a is a redundant generalized comparator, not a missing canonical proof; retain for now without importing into production closure. Commit a8c3fc6c89be adds Closure in the canonical matrix owner: root derived from hd Fixed.p, slopeAlong derived from full identity and matrix gates, ray consumes actual branch jets and chart convergence, allRaw binds original terminal. No independent root/slope premise. Remaining: actual global full matrix identity, symmetry/slice finite gate witnesses, diagonal/slice residual zero, explicit real null test sequence, actual reciprocal ray and its jets. Kernel unrun; no CI; no claim of completed period.

### Whole-cone maximum cut (2026-11-28)
Audit PR1546 at cecf2129; master comparison from 5331203e returned 55 paths, no targeted Hecke/Paper9/Bishop jet/rigidity hits. Default branch searches holomorphic modular rigidity, Vandermonde interpolation, Bishop dyadic null found no direct applicable new owner; historical PR search incomplete (result parsing failed). Existing NativeFiniteAcceptanceExact duplicates new NativeGateAdmission (prefer canonical parameterized owner plus concrete instantiation). Existing IntegerSpecializationExact/ReflectionExact, SignedParameterProductExact, FullIntegerMatrixExact, MatrixSymmetryExact and ActualJLogPhaseJetExact recovered. Commit 90c6f170 adds exact decidable Newton/column/symmetry/packet gates (unrun); check candidate against literal packet before any promotion. Candidate coefficients are not assumed correct; negative e41 handling and leading terms require exact replay. Avoid recomputing full matrix per coefficient in eventual optimized proof-producing implementation.
Reverse solve: one FullIdentity at all real Y suffices for diagonal, slice and reverse via exact finite matrix specialization; obtain via degree<=42 polynomial identity at 43 distinct integer nodes 0..42 (or signed -21..21 to retain even/odd fibres). Existing specialization reflection removes poles at each node from exact gate. Remaining formal producers: (G1) exact finite matrix and node gate witnesses, (G2) actual normalized germ + holomorphic weight-zero rigidity for each node (Lean Paper9HeckePoleRemoval existing donor, same-carrier bridge required), (G3) polynomial uniqueness over Bishop complex with apart integer nodes and finite specialization transport; no density assumption on finite nodes; (R1) actual disk inverse tau=t+d*w/(1-w), positivity and local disk bounds, (R2) exact signed reciprocal chart S/T transport and log-phase increments, (R3) existing actual log jets composed with disk increments and matched to original quotient coefficients, (R4) all chart continuity and explicit apart real null test sequence; (T1) canonical Closure.ray/allRaw, LiteralTerminal, HyperMajorants and NativeJetReduction already source-written; (T2) original Machin same-real and native GMP acceptance. G and R producers can be built independently, then weld once; no new terminal wrappers. Preserve original classical attribution and source boundary. No kernel or CI executed. Full implementation remains open.

### Finite 43-node unisolvence acceptance cut (2026-11-28)
New scripts/check_paper9_hecke41_nodes.py (ad1f06fd) performs rational-arithmetic interpolation using 43 consecutive nodes -21..21 and 0..42, 6 deterministic degree-42 polynomial roundtrips at original CM K=-640320^3, zero and corrupted-node controls, a degree-43 vanishing counterexample, and a signed even/odd fibre check. An equivalent local version was actually executed: 10/10 algebra cases PASS; repository-committed variant itself was not downloaded and executed. This verifies the algebraic seam and its degree bound, **not** the 43 original Hecke specialization equalities, polynomial uniqueness kernel proof, analytic rigidity, or finite gate witnesses.
Commit 9a21447b exposes originalNewtonCheck and originalColumnCheck separately from originalSymmetryCheck and originalPacketCheck. Four gates must pass separately. Newton and column provenance cannot be inferred merely from a symmetric literal packet; no assumed matrix theorem. Resolve the exact orientation of Fin43 degree enumeration (Mat.expo versus M.slice) before asserting the matrix fixedSlice gate.
Geometry-forward construction: (1) actual original column reflection at nodes -21..21, (2) each node's analytic residue zero using the SAME original cusp/rigidity source (or produce global full identity directly), (3) finite-difference uniqueness of the degree<=42 Y-polynomial, (4) originalMatrix symmetry and packet gates, (5) existing MatrixSymmetry.Closure root/slope/ray, (6) original signed reciprocal disk parameter and second jets, (7) original terminal. Hard boundary: finite samples alone never prove a non-polynomial analytic identity; the degree-42 fact is about the parameter Y only. Preserve proof/not-run distinction; no GH CI.

### Newton zero-based index audit and exact regression (28 Nov 2026)
The first inspection of FullIntegerMatrixExact.nextE incorrectly assumed divPositive numerator d divides by d; commit d70545c8 was consequently WRONG and immediately reversed by d316d8ef. Actual owner CM163BishopHecke41IntegerPrefixCertificateExact.divPositive (+ n) d = + (n / suc d); the correct nextE numerator k divides by k+1 via this API. The canonical code at d316d8ef is restored and explicitly documents the API. Do not re-introduce the extra successor. New scripts/check_paper9_newton_gate_indexing.py commit 66631e4b audits this source contract and checks elementary Newton polynomials for degrees 1,2,3,5,7,41, plus off-by-one negative control. Independent equivalent local exact arithmetic: 19/19 PASS. Committed script itself not run against a fresh checkout; Agda checker/compiler not run. This is not a claim that all 41 Hecke q-series Newton gates pass. Next prioritize whether FullIntegerMatrix candidate matches its four gates; if not, repair candidate's Laurent indexing using original cyclic norm source before considering analytical promotion.

## P0 all-node coarse closure implementation — 28 November 2026

This is a **whole-proof backsolve**, not solvedness promotion. Current branch PR #1546 head 6b1d83fafb843e06ce159c2f64a4fe2cdcb2eba1; base master (a compare against PR base reported 75 new master commits, zero file-path hits by targeted Paper9/Hecke/CM163 filter). GitHub search for "CM163 Hecke" found only PR #1546. This is not an exhaustive historical PR content audit.

### Concrete newly implemented G2 owner
- `DASHI/Moonshine/CM163BishopHecke41AllIntegerNodesExact.agda` (commits abfb4fc3 and 6b1d83fa): instantiate the SAME `FullIntegerMatrixExact.originalMatrix` at each of 43 integral targets Y=0..42; construct a `Dec` of their dependent `Through 42` reflection gate; extract each witness by existing `IntegerPrefixCertificateExact.throughAt`; attach existing `IntegerSpecializationReflectionExact.For.zeroPrefix` and `poleRemoved`; factor the exact global `NodeZero` obligation; consume its witness in `IntegerSpecializationExact.For.actualIdentity`. All source-written, uncompiled, not assumed true. Node-zero still requires a sound global rigidity result and is NOT obtained just from finite prefix/vanishing cusp limit. This implementation does not make a 43-node equality proof into an analytic identity.
- Exact certificate boundary: `Cert.UnitGate` (already `NativeFiniteAcceptanceExact.At.unitChecked`), `FullIntegerMatrixExact.originalNewtonCheck`, `originalColumnCheck`, `originalSymmetryCheck`, `originalPacketCheck` and `AllIntegerNodesExact.At.nodes?`. These are independent decisions. Existing generator `divPositive numerator k` divides by `suc k`, as documented by d316d8ef.
- Avoid independent 43 arbitrary external Gate assumptions: use the single `NodeGates` object. Preserve the `For` module's original degree-42 column, exact original product and ramified phase. Do not replace `NodeZero` with `poleRemoved`.

### Existing constructors verified by source inspection
| Geometry region | Owner | Existing precise constructor / source boundary |
|---|---|---|
| Exact CM carrier and cusp | `BishopConcreteElementaryCutsetExact`, `CM163BishopOriginalPhaseHeckeCuspWeldExact` | `concreteCutset`, `ConcreteOriginal`, `ActualCuspRay`, `diagonalCuspZero`, `sliceCuspZero` (ray prerequisite remains) |
| Prefix and source gate | `CM163BishopHecke41NativeFiniteAcceptanceExact` | `unitChecked`, `diagonalChecked`, `sliceChecked` |
| Matrix arithmetic | `CM163Hecke41FullIntegerMatrixExact` | `candidate`, `originalNewtonCheck`, `originalColumnCheck`, `originalSymmetryCheck`, `originalPacketCheck` |
| Arbitrary Y | `CM163BishopHecke41IntegerSpecializationReflectionExact` | `At.For.gate?`, `zeroPrefix`, `poleRemoved` |
| Original analytic Y residual | `CM163BishopHecke41ArbitrarySliceResidualExact` | `At.For.residual`, `invariantS`, `invariantT`, `poleRemoved` |
| Finite 43 Y node unification | `CM163BishopHecke41AllIntegerNodesExact` | `NodeGates`, `nodes?`, `nodeAt`, `NodeZero`, `nodeIdentity` |
| Polynomial fibre | `CM163BishopHecke41SignedParameterProductExact` | `foldPositive`, `foldNegative`, even/odd signed parameter fibre |
| Original 2-variable reverse readback | `CM163BishopHecke41MatrixSymmetryExact` | `symmetric`, `fixedSlice`, `selected0`, `selected1`, `originalCenterSlope`, `Closure` |
| Analytic reciprocal map | `JInvariantBishopCM163ReciprocalGeometryExact` | `forwardDiskCleared`, `reverseDiskCleared`, `p0,m0,p1,m1` |
| Jet transport | `CM163BishopHecke41ActualJLogPhaseJetExact`, `SecondJetCalculusExact` | `actualLogJet`, `compose`, `actualPhase2` |
| Actual ray terminal | `CM163BishopHecke41SignedRayExtractionExact` | `rayFromActual`, exact signed `literalResidual` |
| Native period | `JInvariantBishopCM163LiteralTerminalExact` | `OriginalRayResidual`, `allRawFromDiagonalAndRay` |

### Exact remaining maximal welds (topological ordering, proof terms required)
**G finite**: verify all four original matrix gates and `nodes?` using actual integer witnesses. If any is no, resolve `FullIntegerMatrixExact.coeff` signs, negative e41 mode, `candidate` orientation, and `MatrixSymmetryExact.expo/sliceCoefficient` *first*. Do not convert Boolean or hash receipts into proofs.

**G analytic**: for each node y, `NodeZero`: start from `For.poleRemoved` and exact S/T invariance; show the residual is an actual pole-free holomorphic weight-zero modular function on the compactified quotient, with normalized cusp constant zero, or directly prove global equality via unique analytic (j)-polynomial. This is the critical still-unwritten mathematical theorem in Bishop Agda. A generic invariant function with cusp zero is insufficient (e.g. 1/j). Reuse source `Paper9HeckePoleRemoval` Lean companion where valid, but do not conflate Lean and Agda proofs.

**G polynomial**: explicit degree-42 `Y` bound for product from `SignedParameterProductExact.foldPositive`; degree-42 bound for matrix from `MatrixSymmetryExact.matrix`; constructive uniqueness across 43 distinct integer nodes, using integral apartness (Vandermonde product or forward differences); transport `nodeIdentity` to `FullIdentity` for all real Y. Exactly *this* interpolation is valid, not extrapolating in tau. Once FullIdentity exists, use same source to derive diagonal `d=0` and slice `s=0` by certified specializations/diagonal transport, not independent assumptions.

**R disk**: explicit original `tau(w)=tau_*+d w/(1-w)` and proof UpperHalfPlane membership/denominator apartness for a dyadic real w_n→0, w_n≠0; original reciprocal chart words become alpha*w and beta*w by `forwardDiskCleared`/`reverseDiskCleared`, not an assumed rotated-j identity. Build the actual exponent increment and prove its Inside/bounds for `ActualJLogPhaseJetExact.At.Around.actualLogJet`. Reuse one central j two-jet and reparametrize alpha/beta, rather than prove three independent Taylor series. Carry exact normalized branch identities, all chart convergence via original uniform series continuity, and the actual forty-factor slope from G. Then `SignedRayExtractionExact.rayFromActual` produces `OriginalRayResidual`.

**T terminal**: reuse `MatrixSymmetryExact.At.Closure.ray` and `allRaw`; canonical Chudnovsky raw and GMP same-real/scale budget owners, with independent local (not GitHub CI) verification. Do not treat source-written unexecuted Agda as kernel-proved.

### Fail-closed acceptance order
1. Local Python preflight scripts: `check_paper9_newton_gate_indexing.py`, `check_paper9_hecke41_nodes.py`, original `check_cm163_source_bound_jet.py`, and original pinned source scripts, with reproducible logs.
2. Agda smallest imports: `FullIntegerMatrixExact` → `IntegerSpecializationReflectionExact` → `AllIntegerNodesExact` → `MatrixSymmetryExact`; check finite gate reduction in isolated entrypoints, checkpoint if huge.
3. Agda global analytic/polynomial uniqueness producers independently, then disk-geometry/jet proof cone independently, then combined closure.
4. Native GMP original same-real and performance acceptance. No GitHub CI use. Keep no generated standalone chat files.
