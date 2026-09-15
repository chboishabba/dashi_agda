# YM / RH Finalisation Producer Atlas

Status: proof-search/navigation reference, not theorem authority.

Companions:

- `Docs/support/reference/YMRHPRRoundArchaeologyAudit.md` — chronology / PR / round survey.
- `Docs/support/reference/YMCMPWorkStatus.md` — Yang--Mills CMP paper-family completion boundary.

This document exists to prevent a recurring failure mode: treating the route currently in view as if it were the only construction in the repository, then re-proving machinery already owned by another route, carrier, round clock, or prover.

## 1. Operating rule

Before opening a new proof obligation, ask:

```text
1. What is the exact current consumer/output type?
2. What distinct producers/constructions of that consumer already exist?
3. Which producers are same-object, which need transport, and which are only analogous?
4. Which producers are current, alternate, diagnostic, historical, or disproved?
5. Which route is Pareto-nondominated on:
     - new analytic mathematics,
     - same-object debt,
     - source-acquisition debt,
     - cross-prover transport debt,
     - implementation size,
     - downstream fanout,
     - validation cost?
6. Only after that: prove or implement something new.
```

Search by **consumer/output**, not only by paper name, round number, or current module title.

A route that is superseded as a final proof may still be the cheapest donor for one coordinate. A route that proves a similar-looking scalar on another carrier does not pay the current consumer without an explicit same-object transport.

## 2. Construction status vocabulary

- `PRIMARY` — currently preferred producer/acquisition route.
- `ALTERNATE` — legitimate alternate construction of the same or a stronger consumer.
- `DONOR` — theorem/representation can pay a sub-coordinate after explicit transport.
- `DIAGNOSTIC` — useful obstruction/no-go/scalarization/search information; not a forward producer.
- `SUPERSEDED` — a later construction removed it as a prerequisite.
- `CONDITIONAL COLLAPSE` — shorter construction if a stronger package is inhabited.
- `BLOCKED BY SAME-OBJECT` — mathematics may be owned, but the exact carrier identity is unpaid.
- `BLOCKED BY ANALYSIS` — representation is ready; genuinely new estimate/theorem remains.
- `STATUS ONLY` — metadata/receipt without theorem-bearing transport into the current prover/carrier.

## 3. Yang--Mills: yes, there are multiple constructions

These are not necessarily disjoint complete Clay proofs. They are distinct decompositions/producers of overlapping endpoint consumers and should be compared before new work.

### YM-A. Literal backwards-compiler family

Historical compression sequence:

```text
Round63 implementation-shaped SU(2) backwards compiler
  -> Round64 ten-master literal Clay compiler
  -> Round65 seven-programme honest cut
  -> Round65 conditional four-package collapse
```

Key owners:

- `BalabanSU2ClayBackwardsCompilerExact.agda`
- `YangMillsClayTenMasterBackwardsCompilerExact.agda`
- `YangMillsClaySevenProgrammeBackwardsCompilerExact.agda`
- `YangMillsClayFourPackageBackwardsCompilerExact.agda`

Use: terminal dependency accounting and route comparison.

Current interpretation:

- ten-master: historical decomposition;
- seven-programme: honest broad cut from that era;
- four-package: stronger conditional collapse, not automatically authoritative.

Do not re-prove a seven-programme item merely because a later route renamed it; first check whether a stronger package already absorbs it.

### YM-B. Frozen A/B/C/D research-row construction

Later highest-alpha work froze four physical rows. This is a different research cut from the seven-programme/four-package compiler decomposition.

Canonical historical owner family includes:

- `BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda`
- `BalabanClayHighestAlphaRound90LeanCrossProverSync.agda`
- `BalabanClayHighestAlphaRound95MasterSyncExact.agda`
- `BalabanClayHighestAlphaRound101BidiCompletionCutExact.agda`

Rows, at the archaeology level:

```text
A  positive/tuned beta or Ward/response trajectory
B  marked-source locality / composite-stress geometric shell energy
C  same-density Heat/Doob / clustering / mass-gap route
D  short-distance/OPE/stress/asymptotic-freedom identification
```

Use: whole-problem research scoreboard.

Important: a row may have multiple producer constructions beneath it. Do not equate “row C is open” with “the current Heat/Doob implementation is the only way to pay row C”.

### YM-C. Source-native CMP119/CMP122 -> regular-E -> BC1 construction

Current consumer-minimal BC1 source route:

```text
finite beta history
  -> active density family
  -> published CMP122 Theorem-1 source witness
  -> active CMP119 regular-E Section-2 form
       E_k : Background -> Real
       + literal localization
  -> CMP109/CMP116 continuation
  -> BC1
```

Relevant owners:

- `Balaban1989ActiveScaleTheorem1BetaBridgeExact.agda`
- `BalabanCMP119RegularESection2PredicateRound246Exact.agda`
- `BalabanTheorem1RegularEContinuationRound247Exact.agda`

This construction supersedes “formalise all of CMP119/CMP122 again” and supersedes whole-`A_k` semantics as a prerequisite for the shortest BC1 path.

### YM-D. Whole-action / generated-action / stress construction

A different producer family retains the whole source action because downstream first variation and stress need provenance to one generated action/history:

```text
raw (rho_k, A_k)
  -> source-fixed A_k semantics
  -> generated action
  -> first variation
  -> localized D1 sum
  -> literal stress insertion
  -> Schwinger/common-metric endpoint
```

Key lineage:

- R214 density -> effective-action source semantics;
- R132--R144 same-generated-action/history spine;
- R107--R131 stress/Schwinger/common-metric export.

Use: unification / stress / common-metric provenance.

Do not force this route back into BC1 if regular-E already pays the BC1 consumer directly.

### YM-E. Path13 / Eq.(119) selected-source construction

BIDI source route around the literal side-13 periodic realization and CMP98 Eq.(119)/(120):

```text
Path13 physical SU(2) background
  -> literal side-13 periodic realization
  -> Eq.(119) / Eq.(120) source
  -> selected-background / Q(V0) semantics
```

This is a distinct physical source construction from the CMP119 regular-E lane.

Use: selected source/operator semantics and finite physical carrier work.

### YM-F. Finite quotient / wavefunction / Hamiltonian construction

Several generations exist:

```text
rooted gauge normal form / quotient carrier
  -> gauge-invariant wavefunctions
  -> physical same-measure pairing/null relation
  -> weak symmetry / null descent
  -> quotient Hamiltonian
  -> Hilbert completion/common core/self-adjointness
```

Later corrections select the gauge-invariant L2 subspace as the preferred physical carrier, so a full configuration-space gauge-orbit quotient is not mandatory for the selected route.

Use: mass-gap operator construction.

Do not reopen finite quotient machinery if the selected gauge-invariant-L2 route bypasses it for the current consumer.

### YM-G. Operator-domain / continuum / OS construction

Separate operator-level frontier:

```text
gauge-invariant L2 carrier
  -> genuine D(H) + common invariant core
  -> self-adjoint selected YM operator/form
  -> recovery / spectral transport
  -> OS reconstructed evolution same-object identity
  -> finite-to-continuum YM construction
```

This route reuses generic Kato/Mosco/OS compilers where available but still needs physical YM instantiation.

Use: continuum physical Hamiltonian / mass-gap promotion.

### YM-H. Same-density Heat/Doob / Langevin construction

Row-C producer family:

```text
same-density expectation
  + source marked Hessian comparison
  + anchor Hessian majorant
  + covariance/first-gradient control
  + weighted generator identity
  + relaxation + finite speed
  -> clustering / gap consequences
```

Use: one candidate producer for clustering/mass-gap coordinates.

Important: this is a producer tactic, not the definition of the Clay consumer. A source-native polymer/cluster-expansion or operator route may dominate for a particular final coordinate.

### YM-I. Unified polymer / Schwinger norm construction

Round65-era alternative compression:

```text
one stronger polymer/Schwinger norm
  -> ordinary Schwinger observables
  -> composite insertions
  -> separation-weighted connected correlations
```

Use: collapse multiple continuum receipts into one stronger estimate if the physical norm can be inhabited.

Status: conditional strategy / donor unless the required 4D physical estimate is actually supplied.

### YM-J. Common-metric / QFT-GR endpoint construction

```text
native YM sector recovery
  -> native stress -> shared stress representation
  -> common external metric language
  -> exact sector aggregation
  -> Einstein/common-action variation consumer
```

Use: unification consistency and downstream aggregation.

Not a replacement for upstream YM source realization.

## 4. RH: multiple constructions/routes also exist

### RH-A. Source-native H_A / canonical test-modulation construction

```text
SourceNativePhiHatModulation P
  + SourceNativePhiHatModulationProof P
  -> proof-relevant canonical H_A
```

Later BIDI work compressed several apparent H_A coordinates into one dependent source producer.

Use: source recovery / canonical test-function action.

Status: source-producer route; not automatically the current final high-ordinate scalar producer.

### RH-B. Window / Schur / multi-taper construction

Cross-prover lane includes:

- window-Schur machinery;
- shared-window certificates;
- two-zero / three-taper admission;
- positive pole-null and localized window-separation variants.

Use: structured harmonic/linear-algebraic bounds and donor inequalities.

Status: historical/alternate analytic route. Do not schedule it ahead of the current direct route unless it pays the exact final carrier with fewer open coordinates.

### RH-C. Determinant / G2d scalar construction

The determinant/rank-two taper route owns useful literal finite-sum/scalarization results.

Use: diagnostic and donor.

Critical firewall:

```text
rank-two determinant taper
!= definitionally final universal pole-quotient taper.
```

Therefore determinant payment does not automatically close the final pole-quotient Off consumer.

### RH-D. Explicit-formula / target-window construction

Potential route:

```text
admissible target-centred test f_{t,J}
  -> explicit-formula spectral side
  -> same-ordinate cluster
     + literal finite pole-near response
     + explicit far remainder
  -> lawful extraction/cancellation
```

The source-native modulation / Fourier-shift machinery is already substantially owned. The live issue is same-test-function spectral decomposition/extraction on the final carrier.

Status: legitimate alternate route, but historically more prerequisites than the direct finite route.

### RH-E. Universal pole-quotient direct finite construction

Current preferred high route:

```text
R1: nearResponseAt(chosen J)
      = finiteNearSum(cellResponse)

R2: literalNear(J) + B_far(J) + D_Gamma(g_pole)
      < actual ClusterResponse(g_pole)
```

This is the current acquisition map because it exposes the exact target-centred signed phase consumer.

Status: PRIMARY unless a donor route demonstrably lowers the open-coordinate cost.

### RH-F. 8889 quantitative cluster-margin construction

Checked-Lean return contains a quantitative cluster-margin theorem and related Gamma/off analysis.

Use: optional lower-envelope donor.

Status: `STATUS ONLY / BLOCKED BY SAME-OBJECT` until theorem-bearing source/proof bytes and transport onto the current universal pole-quotient carrier are recovered.

Do not re-prove its generic cluster mathematics merely because the transport is missing; but also do not count its status receipt as payment.

### RH-G. Proof-carrying finite-certificate construction

```text
literal finite fold identity
  + per-term / finite-fold enclosure
  -> certified upper U
  -> U + B_far + D_Gamma < ClusterResponse
```

Use: executable sufficient producer for R2.

Status: optional computational route. Generic certificate machinery exists; same-object numeric realization of the final carrier is the key prerequisite.

### RH-H. Verified low region + generic high contradiction construction

The global endpoint is itself a composition of constructions:

```text
verified low ordinate region
  + uniform arbitrary-high off-line contradiction
  -> global RH endpoint
```

Do not let work on the high route reopen already-owned low-region verification.

### RH-I. de Bruijn--Newman lane

Related RH mathematics, but not automatically the same terminal consumer as the direct G2/pole-quotient route.

Use: independent/adjacent route and source/certificate cross-pollination.

Do not silently merge it into the current direct RH proof graph unless an explicit theorem maps its endpoint into the same RH terminal consumer.

## 5. Producer-first finalisation protocol

For every live terminal consumer `Q`, maintain a producer set:

```text
ProducerAtlas Q = {
  owner,
  routeName,
  exactOutput,
  inputBundle,
  carrier,
  sourceAuthority,
  prover,
  proofStatus,
  sameObjectDebt,
  analyticDebt,
  acquisitionDebt,
  downstreamFanout,
  validationStatus,
  supersededBy,
  canDonateTo
}
```

### Phase 1 — consumer normalization

Write the exact output type first.

Bad:

```text
prove clustering
formalise CMP119
finish RH high case
```

Good:

```text
produce ActiveRegularESection2FormWitness on this exact active density family
prove nearResponseAt(J) = finiteNearSum(cellResponse) on this exact pole taper
prove literalNear + far + Gamma < actual ClusterResponse
```

### Phase 2 — exhaustive producer enumeration

Search in this order:

```text
exact output/type name
-> semantic aliases
-> modules importing the consumer
-> modules exported to the same terminal compiler
-> PR bodies mentioning the consumer or its predecessor
-> archived/cross-prover returns
-> only then external literature
```

Do not search only by the newest round number.

### Phase 3 — quotient equivalent routes

Two routes belong to the same consumer class only when there is an explicit output equality/transport.

```text
same prose / same scalar shape / same theorem name
!= same-object producer
```

Record missing transport as debt rather than rebuilding the mathematics.

### Phase 4 — dominance test

Route `A` dominates route `B` for consumer `Q` when `A` has no worse required debt and is strictly better on at least one of:

- genuinely new analytic leaves;
- source acquisition;
- same-object transport;
- cross-prover transport;
- implementation complexity;
- validation complexity;
- downstream fanout/reuse.

A dominated route stays in the atlas as donor/diagnostic history but should not receive primary proof-search budget.

### Phase 5 — BIDI intersection

Run both directions:

```text
BACKWARD: terminal consumer -> first unowned coordinate
FORWARD: strongest source/theorem producer -> furthest same-object consequence
```

Work only at the intersection.

This prevents long chains of compiler work that never reach the current consumer and prevents re-proving source theorems whose real problem is only attachment.

### Phase 6 — theorem-vs-transport classification

Every live leaf must be typed as exactly one of:

```text
NEW_ANALYSIS
SOURCE_REALIZATION
SAME_OBJECT_TRANSPORT
CROSS_PROVER_TRANSPORT
NUMERIC_CERTIFICATE
COMPILER_PLUMBING
VALIDATION_ONLY
PROVENANCE_ONLY
```

Do not spend analytic effort on a `SAME_OBJECT_TRANSPORT` leaf.
Do not spend source archaeology on `COMPILER_PLUMBING`.
Do not treat `PROVENANCE_ONLY` as theorem payment.

### Phase 7 — stop rules

Stop a search branch when:

- a route is formally disproved for the consumer;
- a strictly dominating route is known;
- only status/provenance remains and theorem bytes are unavailable;
- the current consumer is already paid by another route;
- the next step would recreate a theorem already owned under another carrier without first checking transport.

## 6. Proposed live Pareto boards

### YM board

```text
consumer                              preferred producer                         alternates/donors
-------------------------------------------------------------------------------------------------
BC1 effective potential               active CMP119 regular-E/localization       whole-A_k source route
stress / common metric                whole generated-action D1/stress lane      regular-E is only a subobject
selected Eq119 source                 Path13 literal source lane                  generic source facades
mass-gap physical operator            gauge-invariant L2/operator-domain route    quotient/Hamiltonian historical lane
clustering/gap estimate               compare Heat/Doob vs polymer/source route   do not assume one is canonical
whole Clay dependency accounting      A/B/C/D + backwards compiler atlas          ten/seven/four cuts are donors
```

### RH board

```text
consumer                              preferred producer                         alternates/donors
-------------------------------------------------------------------------------------------------
final near representation R1          universal pole-quotient literal finite     checked Lean nearSignedSum if recovered
strict high complement R2             direct literal phase route                 window/Schur, explicit formula, 8889 donor
certified finite upper                proof-carrying finite certificate          direct analytic theorem can bypass it
cluster lower information             actual ClusterResponse consumer             8889 lower envelope after transport
canonical source modulation           H_A single-source producer                 older multi-coordinate H_A recovery
whole RH endpoint                     verified low + uniform high contradiction   DBN remains adjacent unless bridged
```

## 7. Practical anti-tail rule

Before creating any new YM/RH theorem module, require a short header answer:

```text
CONSUMER:
EXISTING PRODUCERS CHECKED:
DOMINATED ROUTES:
DONORS RETAINED:
LIVE DEBT TYPE:
WHY NEW CODE IS NECESSARY:
```

If `EXISTING PRODUCERS CHECKED` is empty, do archaeology first.

If `LIVE DEBT TYPE` is `SAME_OBJECT_TRANSPORT`, do not prove a stronger analytic theorem.

If a producer already closes the consumer, update routing/status instead of writing mathematics.

## 8. Immediate application

### Yang--Mills

Do not reopen generic CMP109/116/119/122 work.

For each remaining Clay row/consumer, enumerate at least:

- regular-E source route;
- whole-action/stress route;
- Path13 source route;
- finite-H / gauge-invariant-L2 route;
- operator-domain/OS route;
- Heat/Doob route;
- unified-polymer route where applicable.

Then select the least-debt producer for that exact consumer.

### RH

Do not reopen generic explicit formula, generic local zero count, generic cluster, or determinant machinery as undifferentiated tasks.

For R1/R2, compare at least:

- direct universal pole-quotient finite route;
- H_A/source-native route;
- window/Schur route;
- explicit-formula target-window route;
- determinant/G2d donor;
- 8889 quantitative cluster donor;
- proof-carrying finite-certificate route.

The current direct route remains primary only while it is Pareto-nondominated.

## 9. Maintenance rule

Whenever a new PR materially changes a finalisation route, update this atlas with one of:

```text
NEW PRODUCER
ROUTE DOMINATED
ROUTE REVIVED BY NEW TRANSPORT
SAME-OBJECT WELD PAID
ANALYTIC LEAF PAID
ROUTE DISPROVED
STATUS-ONLY DONOR RECOVERED
```

Do not delete old routes. The whole point is to preserve search memory while making current priority obvious.
