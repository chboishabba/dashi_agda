# YM / RH Pareto Coordination

Status: **live coordination sheet**. Not theorem authority, source authority, or a Clay-completion claim.

Historical companions:
- `Docs/support/reference/YMRHPRRoundArchaeologyAudit.md`
- `Docs/support/reference/YMRHFinalizationProducerAtlas.md`
- `Docs/support/reference/YMCMPWorkStatus.md`
- `Docs/support/reference/YMRHGlobalGoalParetoBoard.md`
- `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda`

Use this as the first-stop **current** state sheet; use the archaeology files for history.

## Snapshot — 2026-09-16

```text
#918  merged — active CMP119 regular-E compression + RH R1 decomposition
#934  merged — producer atlas + CMP status boundary
#940  merged — global YM/RH board + RH R1 checked-scalar split
#944  merged — CMP116 R345–R386 sensitivity/localization audit
#949  merged — concrete CMP119 source route
#953  merged — common-metric/unification recut
#970  merged — TERMINAL B CONSUMER:
       direct selected finite spectral upper -> covariance -> continuum -> gap

#967  open/draft — LIVE SOURCE/PRODUCER feeding merged #970:
       R387–R407 consumer-first reconstruction of the selected CMP116 upper
```

#970 is a stable merged consumer. #967 has one job: manufacture its selected finite mixed-log upper without reopening dominated architecture.

## Current direct chain

```text
CMP99 marked propagator/background replacement         [published/source]
 + CMP109 differentiated operator/multilinear entry    [published/source]
 + CMP116 decoupled local-activity construction        [published/source]
 + selected T5/RG physical source semantics            [physical]
                |
                v
R407 literal CMP109 four-stage factor carrier          [source written]
  path -> transport -> dexp^-1/log -> outer dexp
  ordinary before/after stage bounds                   [compiler-owned]
  marked stage-domain difference                       [LIVE source leaf]
                |
                v
R406 noncommutative selected term localization
  selected scalar term = operator product-difference norm
  marked stage bounds -> whole term majorant           [Round72 compiler]
                |
                v
R404 common-Y absolute finite-walk resummation         [compiler / paid]
                |
                v
R405 nested localization-domain/tree summation         [compiler / paid]
                |
                v
R402 absolute finite-polydisc Cauchy lift              [compiler / paid]
                |
                v
R320/R274 selected two-J rooted-shell upper
                |
                v
R398 canonical direct shell
R399 time <= selected physicalDistance
                |
                v
MERGED #970 direct selected spectral upper             [terminal B ABI]
                |
                v
finite covariance -> continuum -> gap                  [existing compiler chain]
```

## Round ledger

### R402 — absolute Cauchy extraction

Paid:

```text
pointwise absolute CMP116 boundary control
  -> absolute finite-polydisc coefficient control.
```

### R403 — observable-indexed source directions

Paid definitionally:

```text
SourceDirection := TestObservable
sourceDirectionOf := id
literal derivative maps := normalized source-calculus derivative maps
```

No second observable->J representation theorem is primitive debt on the preferred route.

### R404 — common-Y absolute walk resummation

Paid:

```text
boundary = finite sum differentiated walk terms
+ each |term| <= term majorant
+ sum term majorants <= common-Y shell
-------------------------------------------
|common-Y boundary| <= common-Y shell.
```

### R405 — nested source-domain summation

Paid:

```text
selected boundary = finite sum common-Y contributions
+ each |common-Y contribution| <= common-Y tree majorant
+ sum common-Y tree majorants <= selected connecting shell
-----------------------------------------------------------
|selected boundary| <= selected connecting shell.
```

Therefore finite summation/resummation is compiler-owned.

### R406 — noncommutative selected term/local-activity localization

Validation:
`DASHI/Physics/YangMills/BalabanCMP116SelectedTermwiseLocalizationRound406Validation.agda`

Owner:
`DASHI/Physics/YangMills/BalabanCMP116SelectedTermwiseLocalizationRound406Exact.agda`

Key milestones:

```text
b2ec32e1...  initial theorem-bearing owner
75201514...  R318 carrier / observable-index type repair
51d90057...  scalar factorwise cut exposed the right frontier but was too lossy
a766bcec...  source-faithful noncommutative Round72 operator telescope
```

R406 no longer takes an opaque

```text
|differentiated term| <= differentiated term majorant
```

field. Each selected differentiated term is scalarized exactly as the norm of a noncommutative product difference, then
`BalabanNoncommutativeMarkedOperatorProductExact.operatorProductDifferenceFromFactorwiseBounds`
derives the whole-term majorant from factorwise ordinary/marked norm estimates.

### R407 — literal CMP109 four-stage ordinary-factor replay

RED validation:
`DASHI/Physics/YangMills/BalabanCMP109FourStageOperatorFactorRound407Validation.agda`

Production source:
`DASHI/Physics/YangMills/BalabanCMP109FourStageOperatorFactorRound407Exact.agda`

R407 uses the existing `BalabanClayGate4OperatorNormPipelineExact.CMP109DerivativeEntryPipeline` rather than inventing another factor model. The literal ordered carrier is

```text
path derivative
-> transport derivative
-> dexp^-1/log derivative
-> outer dexp derivative.
```

For a neighboring before/after pair it proves, stage-by-stage,

```text
||A_i|| <= b_i
||B_i|| <= b_i
```

from the already-existing Gate4 pipeline estimates and transports the AFTER estimate onto the BEFORE operator-norm algebra when the two pipeline algebras are identified. Thus the **ordinary** factor half of R406/P0b1 is no longer a fresh analytic leaf.

The next live source theorem is narrower:

```text
same selected R318/CMP116 term
x literal four-stage CMP109 before/after entry
x CMP99 marked domain replacement on the changed stage
---------------------------------------------------------
||A_i - B_i|| <= m_i
```

for the stage(s) changed by the domain/background replacement. The whole product difference remains compiler-owned by R406/Round72.

R407 is a source-written compiler surface. No Agda/kernel receipt is claimed here.

## Current YM payments

```text
YM-P0a   selected-density/J/decoupling same-object replay — UNPAID.
YM-P0b0  literal CMP109 four-stage factor carrier — PAID by R407 source.
YM-P0b1a ordinary before/after stage norm bounds — PAID by R407 from Gate4 pipelines.
YM-P0b1b marked stage-domain difference bounds — UNPAID / next source frontier.
YM-P0b2  factorwise bounds -> whole differentiated-term majorant — PAID by noncommutative Round72/R406.
YM-P0c   absolute finite-polydisc coefficient extraction — PAID by R402.
YM-P0d   common-Y + nested source summation — PAID by R404/R405.

YM-P1    generic sourceEnvelope<=shell route — optional if direct R320/#970 is cheaper.
YM-P2    time <= selected physicalDistance on the single R318 carrier.
YM-P3    same-Hamiltonian q(E)/candidate-energy identity only where R400 is used.
YM-P4    same-family finite->continuum covariance transport — existing.
YM-P5    clustering/positive-subgap -> transfer gap — existing.
```

## Paid/compiler-owned

```text
normalized two-source log calculus
mixed-log second derivative = finite connected covariance
observable-indexed source presentation (R403)
CMP109 four-stage ordinary factor extraction (R407)
noncommutative marked operator-product telescope (Round72/R406)
absolute common-Y walk resummation (R404)
nested localization-domain summation (R405)
absolute Cauchy coefficient lift (R402)
R318 -> R284 canonical direct shell (R398)
one-sided time/distance consumer shape (R399)
energy/ratio monotonic compiler (R400)
merged #970 terminal consumer
finite->continuum order closure
clustering -> transfer-gap contradiction
```

## Still theorem-bearing / physical

```text
P0a selected-density, actual J pair and decoupling-boundary same-object replay
P0b1b CMP99 marked stage-domain replacement estimate on the literal four-stage CMP109 entry
exact same-object weld from that four-stage entry/product difference to the selected R406 differentiated term
CMP116 positive common-Y / outer shell majorants on that same selected decomposition
P2 selected support/time geometry inhabitant
P3 same-Hamiltonian ratio/energy identity only where used
```

## Pareto order

| Priority | Work |
|---|---|
| 1 | **R408: pay the literal CMP99 marked difference for the changed R407 stage and weld that four-stage entry to the selected R406 term** |
| 2 | **YM-P2: `time <= selected physicalDistance` if not definitional from selected support** |
| 3 | **YM-P3 only where the source-native-q route actually consumes it** |
| 4 | generic source envelope/rate producer only if cheaper than direct R320/merged-#970 |
| 5 | RH-R2 direct strict literal complement |
| 6 | RH-R1 only on new theorem-bearing same-object evidence |

## Do not reopen

Unless a literal current consumer requires it:

- no new generic P0 wrapper;
- no opaque whole-term source inequality;
- no commutative scalar replacement for CMP109 operator/multilinear products;
- no independent observable->source-direction carrier;
- no R76 `E^(2)/Pi` bridge unless the four-stage R407/R408 replay proves it necessary;
- no citation/`ProofLevel` promotion into a theorem term;
- no comparison-only Hessian stability as absolute localization;
- no generic source-envelope plumbing when direct R320/merged-#970 is cheaper;
- no further finite-summation wrapper after R404/R405;
- no independent R284/R318 distances after R398;
- no exact distance=time when only time<=distance is consumed;
- no fixed q_fast=1/2 architecture;
- no R353–R385/Heat/Doob/Langevin mandatory detour;
- no generic CMP109/116/119/122 re-formalization without a current consumer.

## Source attribution

- CMP99: Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- CMP109: DOI `10.1007/BF01215223`.
- CMP116: Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, DOI `10.1007/BF01239022`.
- CMP119: DOI `10.1007/BF01217741`.

CMP99 Theorem 3.14/(3.154) is the marked domain/background replacement donor. CMP109 (4.3)–(4.5) supplies the differentiated operator/tree structure; the repository Gate4 pipeline already exposes its physical derivative entry as the four ordered stages used by R407. CMP116 Sect. 1 supplies the generalized-walk/decoupling construction around (1.6)–(1.21), differentiated representation around (1.23), and positive tree/localization summation around (1.29)–(1.36).

Citation/source status does not itself inhabit P0.

## Validation / closure boundary

Track separately:

```text
source written?
focused RED observed?
production owner written?
exact-head workflow observed?
Agda/kernel receipt observed?
external/source theorem replay formalized?
Clay/external acceptance?
```

Current focused commits:

```text
224bb0b3...  R404 absolute common-Y finite-walk resummation
143c8f66...  R405 nested source-domain summation source
14b13cbf...  R406 RED-first validation
75201514...  R406 R318/J carrier type repair
a766bcec...  R406 source-faithful noncommutative factor telescope
42406135...  coordination sync through R406
0469bf19...  R407 RED validation
8e4b619e...  R407 literal four-stage ordinary-factor compiler source
```

Per user instruction, CI is not part of this tranche. No current-head Agda/kernel certification is claimed.

## Update log — 2026-09-16

- #970 remains the merged terminal B consumer; #967 remains the live producer.
- R402/R403/R404/R405 remain paid compiler layers.
- R406 retains the noncommutative product-difference formulation.
- R407 reuses the existing CMP109 Gate4 derivative pipeline and pays the ordinary before/after factor estimates on the literal four-stage carrier.
- The immediate source frontier is now the **marked domain-difference estimate for the changed stage**, plus the same-object weld of that four-stage entry to the selected R318/CMP116 differentiated term.
- The R76 `E^(2)/Pi` representation bridge remains donor-only unless this direct replay demonstrates a need.
- RH remains behind YM in the live Pareto order.
