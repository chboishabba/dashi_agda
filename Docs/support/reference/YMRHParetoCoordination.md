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
       R387–R409 consumer-first reconstruction of the selected CMP116 upper
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
                |
                v
R408 changed stage = existing resolvent defect
  changed-stage ||A-B|| <= m                           [compiler-owned]
  unchanged A=B -> exact zero marked cost              [compiler-owned]
                |
                v
R409 single-marked four-stage assembly
  one R408 marked stage + three zero stages
  -> whole four-stage product difference               [compiler-owned]
                |
                v
R406 selected differentiated scalar term
  = norm(four-stage before product - after product)    [LIVE same-object weld]
                |
                v
R404 common-Y absolute finite-walk resummation         [compiler / paid]
R405 nested localization-domain/tree summation         [compiler / paid]
R402 absolute finite-polydisc Cauchy lift              [compiler / paid]
                |
                v
R320/R274 selected two-J rooted-shell upper
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

Paid: pointwise absolute CMP116 boundary control -> absolute finite-polydisc coefficient control.

### R403 — observable-indexed source directions

Paid definitionally:

```text
SourceDirection := TestObservable
sourceDirectionOf := id
literal derivative maps := normalized source-calculus derivative maps
```

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

### R406 — noncommutative selected term localization

Validation: `DASHI/Physics/YangMills/BalabanCMP116SelectedTermwiseLocalizationRound406Validation.agda`

Owner: `DASHI/Physics/YangMills/BalabanCMP116SelectedTermwiseLocalizationRound406Exact.agda`

R406 scalarizes each selected differentiated term as the norm of a noncommutative product difference and invokes `BalabanNoncommutativeMarkedOperatorProductExact.operatorProductDifferenceFromFactorwiseBounds`; it does not accept an opaque whole-term inequality.

### R407 — literal CMP109 four-stage ordinary-factor replay

Validation: `DASHI/Physics/YangMills/BalabanCMP109FourStageOperatorFactorRound407Validation.agda`

Owner: `DASHI/Physics/YangMills/BalabanCMP109FourStageOperatorFactorRound407Exact.agda`

R407 reuses `BalabanClayGate4OperatorNormPipelineExact.CMP109DerivativeEntryPipeline` and pays the ordinary before/after norm bounds for the four literal stages:

```text
path derivative -> transport derivative -> dexp^-1/log derivative -> outer dexp derivative.
```

### R408 — CMP99 changed-stage marked compiler

Validation: `DASHI/Physics/YangMills/BalabanCMP99MarkedStageDifferenceRound408Validation.agda`

Owner: `DASHI/Physics/YangMills/BalabanCMP99MarkedStageDifferenceRound408Exact.agda`

R408 reuses `BalabanClayGate4ResolventDefectPipelineExact.resolventDifferenceNormBelowBudget`; the genuinely changed-stage marked inequality is compiler output once the selected R407 stage is identified with the resolvent defect. It also transports the R407 Gate4 ordinary estimates into the same Round72 norm/order used by R406.

The Round72 operator algebra now has the general self-difference law `||A-A|| <= 0`, and R408 proves `unchangedStageDifferenceBelowZero`; unchanged stages therefore require equality only, not additional marked estimates.

### R409 — one marked stage -> complete four-stage product

RED validation: `DASHI/Physics/YangMills/BalabanCMP99SingleMarkedFourStageRound409Validation.agda`

Production source: `DASHI/Physics/YangMills/BalabanCMP99SingleMarkedFourStageRound409Exact.agda`

R409 exhausts all four possible changed-stage choices with `SingleChangedFourStageAgreement`. Each constructor contains:

```text
changedStage = selected literal stage
+ exact equality of the other three before/after stage operators.
```

It then defines one marked-majorant family:

```text
changed stage -> R408 resolvent budget
unchanged stage -> zero
```

and derives every stagewise marked inequality from R408. Finally
`fourStageProductDifferenceBelowMarkedMajorant` calls the existing noncommutative Round72 telescope with R408's transported R407 ordinary bounds and this one-marked-stage family.

Thus the complete four-stage product inequality is compiler output. There is no remaining factorwise analytic inequality to prove on the preferred route.

R409 is source-written only; `round409KernelCertifiedAtCurrentHead = false`, and its local `ProofLevel` remains non-promotable pending an observed kernel receipt.

## Current YM payments

```text
YM-P0a    selected-density/J/decoupling same-object replay — UNPAID.
YM-P0b0   literal CMP109 four-stage factor carrier — PAID by R407 source.
YM-P0b1a  ordinary before/after stage norm bounds — PAID by R407/R408.
YM-P0b1b1 changed-stage marked norm inequality — PAID by R408 resolvent compiler.
YM-P0b1b2 unchanged-stage marked norm inequalities — PAID by exact equality -> zero.
YM-P0b1c  actual CMP99 defect/stage choice + three unchanged-stage equalities — UNPAID source attachment.
YM-P0b1d  complete four-stage marked product inequality — PAID by R409.
YM-P0b1e  selected R406 differentiated term = R409 four-stage product-difference norm — UNPAID / LIVE FRONTIER.
YM-P0b2   generic factorwise -> product telescope — PAID by Round72/R406.
YM-P0c    absolute finite-polydisc coefficient extraction — PAID by R402.
YM-P0d    common-Y + nested finite source summation — PAID by R404/R405.

YM-P1     generic sourceEnvelope<=shell route — optional if direct R320/#970 is cheaper.
YM-P2     time <= selected physicalDistance on the single R318 carrier.
YM-P3     same-Hamiltonian q(E)/candidate-energy identity only where R400 is used.
YM-P4     same-family finite->continuum covariance transport — existing.
YM-P5     clustering/positive-subgap -> transfer gap — existing.
```

## Paid/compiler-owned

```text
normalized two-source log calculus
mixed-log second derivative = finite connected covariance
observable-indexed source presentation (R403)
CMP109 four-stage ordinary factor extraction (R407)
Gate4 -> Round72 norm/order transport (R408)
resolvent-defect norm assembly for changed stage (R408)
unchanged-stage exact zero marked cost (Round72/R408)
single-marked four-stage product assembly (R409)
noncommutative marked operator-product telescope (Round72/R406)
absolute common-Y walk resummation (R404)
nested localization-domain summation (R405)
absolute Cauchy coefficient lift (R402)
R318 -> R284 canonical direct shell (R398)
one-sided time/distance consumer shape (R399)
merged #970 terminal consumer
finite->continuum order closure
clustering -> transfer-gap contradiction
```

## Still theorem-bearing / physical

```text
P0a selected-density, actual J pair and decoupling-boundary same-object replay
P0b1c literal CMP99 Theorem 3.14/(3.154) defect attached to the actual changed R407 stage + three unchanged-stage equalities
P0b1e exact R409 four-stage product-difference norm attached to the selected R406 differentiated term
CMP116 positive common-Y / outer shell majorants on that same selected decomposition
P2 selected support/time geometry inhabitant
P3 same-Hamiltonian ratio/energy identity only where used
```

## Pareto order

| Priority | Work |
|---|---|
| 1 | **R410: use existing source identities to select the actual CMP99-changed R407 stage, prove the other three stage equalities, and weld the resulting R409 four-stage product-difference norm directly to the selected R406 differentiated term** |
| 2 | **finish CMP116 positive common-Y / outer majorant attachment on that same selected decomposition if not already definitional** |
| 3 | **YM-P2: `time <= selected physicalDistance` if not definitional from selected support** |
| 4 | **YM-P3 only where actually consumed** |
| 5 | generic source envelope/rate producer only if cheaper than direct R320/merged-#970 |
| 6 | RH-R2 direct strict literal complement |

## Do not reopen

Unless a literal current consumer requires it:

- no new generic P0 wrapper;
- no opaque whole-term source inequality;
- no opaque changed-stage `||A-B||<=m` field;
- no marked assumptions for literally unchanged stages;
- no second four-stage product inequality after R409;
- no commutative scalar replacement for CMP109 operator/multilinear products;
- no independent observable->source-direction carrier;
- no R76 `E^(2)/Pi` bridge unless the direct R407–R410 replay proves it necessary;
- no citation/`ProofLevel` promotion into a theorem term;
- no comparison-only Hessian stability as absolute localization;
- no generic source-envelope plumbing when direct R320/merged-#970 is cheaper;
- no further finite-summation wrapper after R404/R405;
- no exact distance=time when only time<=distance is consumed;
- no fixed q_fast=1/2 architecture;
- no generic CMP109/116/119/122 re-formalization without a current consumer.

## Source attribution

- CMP99: Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- CMP109: DOI `10.1007/BF01215223`.
- CMP116: Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, DOI `10.1007/BF01239022`.
- CMP119: DOI `10.1007/BF01217741`.

CMP99 Theorem 3.14/(3.154) is the marked domain/background replacement donor. CMP109 (4.3)–(4.5) supplies the differentiated operator/tree structure. The existing Gate4 operator and resolvent pipelines supply the finite norm compilers consumed by R407/R408. CMP116 Sect. 1 supplies generalized-walk/decoupling and positive localization summability.

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
a766bcec...  R406 noncommutative factor telescope
42406135...  coordination sync through R406
0469bf19...  R407 RED validation
8e4b619e...  R407 literal four-stage ordinary-factor compiler
e09ee044...  coordination sync through R407
e0e1b616...  R407 proof-status correction
4e1cff78...  R408 RED validation
305028b8...  Round72 general self-difference-zero law
7227ce94...  initial R408 resolvent-defect marked-stage compiler
dd1bea92...  R408 unchanged-stage zero theorem / safety cleanup
524ea5c4...  R408 Gate4 -> Round72 norm/order transport
c8593d2a...  R409 RED validation
8b7dc577...  R409 one-marked-stage four-stage product compiler
```

Per user instruction, CI is not part of this tranche. No current-head Agda/kernel certification is claimed.

## Update log — 2026-09-16

- #970 remains the merged terminal B consumer; #967 remains the live producer.
- R402/R403/R404/R405 remain paid compiler layers.
- R406 retains the noncommutative product-difference formulation.
- R407 pays all ordinary four-stage factor estimates.
- R408 pays the changed-stage resolvent inequality and unchanged-stage zero inequalities, plus the Gate4/round72 norm/order seam.
- R409 pays the entire one-marked-stage four-factor product inequality for any of the four possible changed stages.
- The live P0 frontier has moved from analytic/factorwise inequality construction to **source identity and same-object attachment**: choose the actual CMP99 stage/equalities and weld the exact R409 product-difference to the selected R406 term.
- The R76 `E^(2)/Pi` bridge remains donor-only unless this direct route demonstrates a need.
- RH remains behind YM in the live Pareto order.
