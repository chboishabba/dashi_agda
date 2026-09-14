# Navier–Stokes Paper 1 Modern Proof-Spine Migration

Date: 2026-09-14 (Australia/Brisbane)
Status: design/specification; non-promoting

## Goal

Migrate Paper 1 from the June `A1-A9` ESS/Abel-defect/tail-flux narrative to the current literal periodic proof spine without erasing the earlier route. The old route remains visible as historical/provenance material, including why it was pursued, what it established, what later evidence falsified or superseded, and which ideas remain reusable donors.

The paper must continue to distinguish:

- mathematical construction,
- statement/interface status,
- certification status,
- external-source attribution,
- historical/abandoned route status.

No source-written theorem, validation root, workflow target, or external publication is to be promoted into a kernel-checked or Clay-level claim without its own receipt.

## Publication strategy

Paper 1 becomes a proof-causal manuscript rather than a round-number diary.

The main narrative is the modern chain

```text
literal periodic Galerkin NS
  -> signed commutator / raw-curl geometry
  -> exact partner compression and same-output Gram residual
  -> modern weighted/nested commutator carrier
  -> direct companion quotient
  -> R568 commutator-only spacetime budget
  -> R572
  -> R503
  -> critical-barrier consumer.
```

The old `A1-A9` route is retained in an explicit historical appendix and provenance table. It must be described as a serious earlier attempt, not hidden or rewritten after the fact.

## Main theorem policy

Until the live producer is actually paid, the paper's front theorem remains conditional on the exact modern analytic leaf rather than claiming completed global regularity.

Current live producer interface:

```text
CommutatorOnlySpacetimeBudget568
```

Downstream compiler chain:

```text
R568 -> R572 -> R503 -> 4 C_direct -> critical barrier.
```

The manuscript must state which arrows are exact same-object/compiler theorems and which arrow is the unresolved analytic producer.

## Section architecture

### 1. Main result, claim boundary, and status coordinates

Purpose:
- state the periodic NS target;
- state the conditional theorem with `CommutatorOnlySpacetimeBudget568` as the live hypothesis;
- introduce MathematicalStatus / StatementStatus / CertificationStatus;
- state explicitly that validation-root or workflow wiring is not an observed kernel receipt.

Primary owners:
- `DASHI/Physics/Closure/NSTriadKNCommutatorOnlySpacetimeBudgetRound568Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNDirectLeafAProducerRound572Exact.agda`
- `DASHI/Physics/Closure/NSTriadKN...Round503...` direct-off-diagonal consumer owner
- `DASHI/Papers/NavierStokes/TheoremInterface.agda` after migration.

### 2. Literal periodic carrier and exact nonlinear object

Purpose:
- define the literal periodic Fourier/Galerkin carrier;
- identify Leray projection, physical triad incidence, helical decomposition, exact curl eigenvalues;
- separate algebraic identity from analytic estimate.

Primary owner families:
- periodic Fourier/helical infrastructure;
- physical triad enumeration;
- R94/R105/R106 Waleffe/helical forcing objects;
- R120 pure multiplier-difference commutator;
- R172 raw directional kernel.

### 3. Signed commutator and low-output geometry

Purpose:
- explain the cancellation-first construction;
- retain sign/phase before positive majorization;
- show the exact low-output local kernel estimates and radial/angular defect decomposition.

Primary owners:
- R120/R123 signed pure-commutator/Bony weld;
- R126-R132 radial-gap / square-gap / extremal geometry;
- R145 raw-curl algebra;
- R166 homogeneity correction;
- R167/R168 authoritative quadratic kernel;
- R172-R178 raw-curl weld, dual-defect geometry, low-output mass.

### 4. Partner compression, Gram residual, and negative controls

Purpose:
- prove that pair-first compression is exact;
- isolate the true whole-fibre obstruction as same-output between-partner Gram debt;
- retain positive-debt and constant-band no-go witnesses;
- document the PR #890 centered/radial-Plücker lower-separation attempt, the amplitude telescope, and the many-to-one observable obstruction without concealing the failed route.

Primary owners:
- R179/R180 polarization and Gram ledger;
- R181 partner-block compression;
- R183 aligned positive-debt witness;
- R184/R185 three-class reduction;
- R186/R187 literal partner blocks and compressed mass;
- R201/R202 law of total Gram and quantitative positive residual socket;
- R205/R206 literal comparable partner carrier;
- R207 same-output debt;
- R208/R209 outputwise telescope;
- R214 constant-band Gram no-go;
- merged PR #890 same-object difference/PSD adapter and its negative-control owners.

### 5. Historical producer searches and why they were abandoned or retained

Purpose:
- present a provenance-preserving account of earlier producer attempts;
- distinguish false route, insufficient route, fallback route, and reusable donor theorem.

Required route classes:

1. `A1-A9` ESS / Abel-defect / support-richness / tail-flux route:
   - preserve the original June manuscript thesis and blockers;
   - mark it `historicalAlternativeRoute` unless later explicitly revived;
   - record which theorem-shape ideas remain reusable.

2. constant-band / shell-localization-as-payment:
   - retained as a negative control;
   - R214 proves localization alone cannot pay same-output Gram debt.

3. generic positive Gram / Schur / Cotlar route:
   - retained as a fallback producer family;
   - never presented as refuted merely because shell-width alone fails.

4. centered/radial-Plücker pair-separation route from PR #890:
   - retain exact same-object and PSD progress;
   - record the many-to-one observable obstruction exposed by the amplitude telescope;
   - do not claim incidence-only geometry yields anti-alignment.

5. direct signed coherent/resolvent/commutator route:
   - retain as the live highest-alpha family feeding R568.

### 6. Modern weighted/nested commutator carrier

Purpose:
- trace the literal modern object before norm/Schur compression;
- preserve the four-helicity channel distinction and the homochiral/heterochiral firewall.

Primary owners:
- R294 weighted signed commutator;
- R310 inner swap pairing;
- R311 homochiral radial classification;
- R545 spectator factorization;
- R566/R567 transpose/full-square collapse;
- R571-R577 modern helical / cell / Gram chain.

### 7. Direct companion quotient and same-object remainder genealogy

Purpose:
- state the exact same-object chain connecting the old remainder to the modern direct companion;
- make compiler vs producer status explicit.

Required identity:

```text
F_N^(R104)
  = integral R406
  = 4 * integrated C_direct.
```

Primary owners:
- R406 remainder object;
- R414 old-R104-to-R406 integral identification;
- R496-R503 direct companion construction;
- R500 exact factor-four identity;
- R503 downstream budget consumer.

### 8. Live analytic leaf and terminal reduction

Purpose:
- state R568 in its least opaque exact form;
- show that R572/R503 and the terminal critical-barrier machinery are consumers/compilers;
- avoid presenting a consumer as a producer.

Primary owners:
- R568;
- R572;
- R503;
- critical barrier / continuation consumer owners.

### 9. Certification and reproducibility appendix

For every proof-critical owner record:

```text
(role,
 MathematicalStatus,
 StatementStatus,
 CertificationStatus,
 earliest theorem-bearing commit/date,
 validation root,
 workflow target,
 observed commit-specific Agda receipt,
 source/attribution notes)
```

CertificationStatus must distinguish at least:

```text
sourceWritten
validationRootExists
workflowTargetsRoot
observedKernelReceipt
notRecovered
```

No inference from one status to another.

The dedicated NS workflow around R185/R193/R200 is historical evidence of intentional kernel-checkability, not by itself a head-specific success receipt.

## Historical A1-A9 handling

The existing `Docs/papers/live/Paper1NavierStokesClayDraft.md` must not be silently rewritten as though the modern route had always been the argument.

Migration policy:

- preserve the June draft text in repository history and, if useful, an archived snapshot;
- add a short historical-route section explaining the original tail-flux / ESS / Abel-defect thesis;
- list its named blockers (`A1/A3`, `A4`, etc.);
- explain which later exact finite-Fourier/Gram results made a different route preferable;
- state explicitly whether each old route is `abandoned`, `superseded`, `fallback`, `negativeControl`, or `reusableDonor`;
- never retroactively attribute modern results to earlier sources or modules.

## External published-proof reconstruction track

Any comparison with recently published or claimed Clay-level proofs is a separate bidirectional reconstruction track, not evidence that the DASHI proof is complete.

For each external proof:

```text
external theorem/lemma
  -> exact source statement
  -> assumptions
  -> DASHI nearest owner
  -> direction A: external -> DASHI construction
  -> direction B: DASHI -> external construction
  -> same-object status
  -> unresolved mismatches
  -> certification status.
```

Possible outcomes must remain explicit:

- equivalent construction recovered;
- one direction factors but the converse does not;
- same theorem statement, different producer;
- analogous only;
- contradiction / missing assumption;
- unresolved.

No external publication, review status, or publicity substitutes for checking the mathematical construction.

## Interface migration

`DASHI/Papers/NavierStokes/TheoremInterface.agda` should stop using the A6-A9 route as the primary paper status spine.

The migrated interface should expose:

- modern live producer `R568`;
- exact downstream compiler chain `R572 -> R503`;
- same-object remainder genealogy;
- same-output Gram residual status;
- historical A1-A9 route as a named non-promoting historical object;
- terminal false guards;
- separate status booleans for mathematical statement and certification.

Do not delete the old A6-A9 imports until the historical/provenance surface has an explicit replacement.

## Publication-roadmap migration

Update `Docs/papers/PublicationRoadmap.md` and the generated theorem-variable manifest only after the paper interface exposes the modern chain.

The readiness checker must no longer interpret the A1/A3-A4 frontier as the sole current Paper 1 blocker. It should report the modern live producer and separately report the historical route.

## Non-goals

This migration does not:

- prove R568;
- promote PR #890's negative-control route into a producer;
- claim a Clay resolution;
- claim a head-specific Agda success without a receipt;
- delete or hide failed attempts;
- replace exact owner attribution with retrospective narrative;
- create another parallel NS planner or theorem interface.

## Acceptance criteria

The migration is complete when:

1. the live Paper 1 main theorem is conditional on the modern exact producer leaf rather than the stale `A1-A9` package;
2. the old route remains explicitly discoverable with reasons for supersession/abandonment;
3. the paper section-to-owner map is exact enough to trace every load-bearing claim to a module;
4. the theorem interface exposes the modern chain and terminal false guards;
5. publication readiness reports modern and historical blockers separately;
6. certification status never conflates source, validation, workflow wiring, and observed kernel receipt;
7. external published-proof reconstruction remains bidirectional and non-promoting until same-object equivalence is actually established.
