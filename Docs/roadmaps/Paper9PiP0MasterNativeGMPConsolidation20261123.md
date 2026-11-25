
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
