# Yang--Mills final direct-upper closure — 2026-09-16

Status: **current-master proof-search ledger**. This is bookkeeping, not theorem authority and not a Clay-completion claim.

This ledger supersedes the R410-centric terminal reading of the stale #967 branch. The authoritative terminal consumer is merged #970 / R387 on current `master`.

## 1. Branch / PR correction

Current `master` before this closure tranche: `58e264dfb0c4633632d29be13ab6f3308fe94774`.

Old Agda #967 is a useful optional source-replay/provenance branch, but it is not the current terminal integration branch:

```text
#967 unique work: R404-R409 + noncommutative marked-product replay
#967 relative to current master: ~35 commits ahead, 1296 commits behind
```

Merged #970 is the least-privilege terminal ABI. It observes only one theorem-bearing YM field:

```text
|D^2_{J_L,J_R} log Z_N| <= selected clusteringEnvelope(O,t).
```

No R410 factor choice, source root, source distance, or intermediate source envelope is a terminal field.

Fresh current-master closure branch:

`agent/ym-final-direct-upper-closure`

## 2. Newly paid terminal composition

`DASHI/Physics/YangMills/BalabanDirectSelectedUpperToGapFinalExact.agda`

adds the thin theorem:

```text
R387.DirectSelectedSpectralUpper
+ selected one-sided limit closure
+ positivity of selected candidate gap
------------------------------------------------
Gap.PositiveTransferGapCore.
```

It is literally the composition of:

```text
R387.directSelectedSpectralUpperBuildsSubgapUpper
Gap.positiveTransferGapCoreFromModeTests.
```

Consequently:

```text
R410 mandatory for terminal gap?        NO
sourceEnvelope mandatory terminal data? NO
fresh YM decay estimate introduced?     NO
```

The source is written but no exact-head Agda kernel receipt has been observed, so its local `ProofLevel` remains `conditional`.

## 3. Equation (25) remains paid

The parallel Lean lane already proves the covariance/clustering-to-vacuum-form-gap implication:

```text
SpectralRepresentation H vac
+ continuum covariance decay
+ source/spectral Laplace comparison
-------------------------------------
ClusteringSpectralData.ofSourceBound
 -> hasVacuumFormGap_of_clustering
 -> HasVacuumFormGap H vac m.
```

`Welds.YMSourceClusteringGap.vacuumFormGapOfSourceCovariance` exposes that composition directly.

Therefore no further generic spectral/clustering theorem is part of this closure cut.

## 4. Source side: exact current leaf

The repository already machine-compiles:

```text
normalized two-source source calculus
mixed-log derivative = finite connected covariance
signed-vs-magnitude correction
exact T5 covariance same-object identity
absolute-value transport
rooted-shell -> direct T5 shell
finite -> continuum one-sided order closure
subgap-mode clustering upper
positive transfer-gap contradiction/core
```

The historical chain R295/R296/R313 shows that the only source-facing analytic theorem on the exact T5 presentation is

```text
R295.differentiatedSourceMagnitudeBoundOnSelectedDirections:

magnitude (D^2_J log Z_N)
  <= rootedShell(scale,volume,root,physicalDistance).
```

R313 proves that R296's explicit `|.|` version is compiler output once the magnitude realization is rational absolute value.

R318 separates this theorem honestly into:

```text
PublishedTwoJLocalizationForBase          [source theorem]
SelectedBaseJApplicability                [same-object application]
```

where applicability is only the triple

```text
source magnitude = selected mixed-log magnitude
source root      = selected connecting root
source distance  = selected physical distance.
```

R318 then machine-compiles those inputs into the exact R295 theorem.

### Source theorem status

The mathematical source statement is explicitly attributed to Bałaban CMP116 Sect. 1, especially (1.23), (1.29), and Lemma 1 / (1.33)-(1.36), and is graded `standardImported`.

However, a repository-wide constructor search finds **no concrete proof-bearing inhabitant** of

`PublishedCMP116DifferentiatedLocalization`.

All hits define, adapt, repackage, or consume that ABI. A `ProofLevel`, citation, or source OCR is not a theorem term.

Therefore the source-side primitive closure target is now:

```text
A1  proof-bearing published CMP116 differentiated-localization inhabitant
A2  selected-T5 same-object applicability of magnitude/root/distance
```

not R410.

R410 remains a valid stronger proof tactic/provenance replay for deriving A1/A2, but it is not terminal architecture.

## 5. Finite physical form / coercivity side

The repository already owns substantial hard mathematics:

```text
BalabanP33LiteralFiveMechanismFamiliesExact
  -> five literal local mechanisms
  -> exact P33 floor from primitive operator norms

BalabanP33PhysicalSU2FiniteCoordinatesExact
  -> explicit finite SU(2) physical coordinates
  -> exact norm/matrix quadratic realization

BalabanP33PhysicalSU2MatrixCoercivityExact
  -> physical P33 floor transfers to every finite physical coordinate

YMKatoClosedFormHamiltonianExact
  -> densely-defined closed semibounded physical form
  -> associated operator domain + self-adjoint Hamiltonian.
```

What is **not** constructed anywhere under the exact producer types is:

```text
PrimitiveAbsoluteOperatorNorms / PrimitivePhysicalOperatorNorms concrete inhabitant
PhysicalSU2MatrixHessian concrete inhabitant
literal physical closed semibounded q_a on L2_gauge(mu_a).
```

Searches for record constructions land only on adapters/definitions, not a physical producer.

Thus the finite physical primitive cut is:

```text
B1  concrete primitive physical/absolute operator norm package
B2  build the corresponding concrete PhysicalSU2MatrixHessian / closed form q_a
B3  identify q_a / its associated H_a with the selected physical action variation
B4  direct Row-A1 coercive floor on that same q_a/H_a.
```

Everything after B2/B4—self-adjoint realization, gap datum, inverse/resolvent bounds—is compiler-owned.

## 6. Continuum / OS side

The repository already owns compilers such as:

```text
BalabanClayT5PreferredContinuumOSGapExact
BalabanClayT5PhysicalContinuumOSGapBridgeExact
BalabanClayDirectTerminalConsumerCutRound308Exact
Lean graph-limit / same-evolution operator compilers.
```

But exact searches for record constructions find no concrete inhabitant of the preferred physical continuum/OS package. The visible constructors are adapters from already-filled input records.

The primitive continuum cut is therefore:

```text
C1  actual selected cutoff physical family / continuum closure inhabitant
C2  actual same-object YM/OS reconstruction/evolution identification
C3  selected physical continuum vacuum/Hamiltonian meaning where required.
```

The spectral/clustering implication itself is already paid.

## 7. Current shortest proof normal form

The proof search is now:

```text
A. published CMP116 localization term + selected same-object applicability
       -> R295/R313/R284/R388/R387
       -> selected continuum clustering upper
       -> PositiveTransferGapCore

B. concrete primitive finite YM norms/form + direct Row-A1 coercivity
       -> Kato associated self-adjoint H_a
       -> VacuumGapDatum / finite inverse bound

C. actual cutoff->continuum + YM/OS same-object reconstruction
       -> same quantitative gap/inverse bound on the physical continuum H.
```

No further generic proof infrastructure is presently identified as necessary.

## 8. Verification boundary

Keep separate:

```text
source written
exact-head Agda kernel checked
retained/imported source authority
selected physical inhabitant
Clay completion
```

The new current-master terminal composition is source-written only pending an observed exact-head Agda kernel receipt.

The retained Lean BIDI package carries its own worker receipt; that receipt is not borrowed for new welds.

## 9. Do not reopen

Unless a literal consumer forces it:

- no mandatory R410 factor replay after merged R387/#970;
- no new Cauchy theorem;
- no new covariance carrier;
- no second clustering-to-gap theorem;
- no separate self-adjointness proof when Kato closed-form representation applies;
- no new P33 coercivity calculus when the five-mechanism/floor compiler already exists;
- no record/Boolean/`ProofLevel` promotion into a theorem inhabitant.

## 10. Exhausted historical-producer audit

A current-master search alone could miss a theorem term living on an old or unmerged branch, so the closure pass also audited historical PRs and exact missing producer names.

### Source A

- PR #648 (`YM post-#644: BIDI literal source closure for A1/A2/BC1/BC2`) was inspected directly.  Its merged diff contains only an audit-start owner/marker; it does not contain a hidden localization constructor.
- PR #635 provides the strict CMP109/CMP116 differentiated same-carrier compiler.  It proves the CMP109 polarization / CMP116 physical marked-Hessian identities once a literal continuation carrier is supplied, while `literalDifferentiatedCarrierInstantiationLevel` remains conditional.
- Exact PR-history search for `PublishedCMP116DifferentiatedLocalization` finds only the current #967/#987 bookkeeping/consumer work; no historical producer PR supplies the record inhabitant.

Therefore A is not an orphaned theorem waiting to be cherry-picked.

### Finite physical B

- PR #811 constructs the finite projected `P M P` Hamiltonian, domain invariance and the exact P33 floor **when supplied** a `PhysicalSU2MatrixHessian` coercivity certificate.  It does not construct that certificate.
- Exact PR-history search for `PrimitiveAbsoluteOperatorNorms` finds no older physical producer.
- Exact PR-history search for `PhysicalSU2MatrixHessian` finds #811 and current #987; the former is a consumer of the certificate, not its producer.

Therefore B is not an orphaned primitive-norm/Hessian constructor.

### Continuum / OS C

- PR #638/Rounds124--131 unify the same finite-measure, continuum-measure, Schwinger and stress carriers, but Round126 stores `literalFiniteMeasuresConverge` and `literalSchwingerBelongsToContinuumMeasure` as physical continuum input fields.
- PR #649 propagates one generated action/history into that same Schwinger/stress spine and explicitly leaves the remaining physical source/continuum identities open.
- Repository and PR-history searches for an actual theorem deriving the pair

```text
IsContinuumLimitOf finiteMeasure continuumMeasure
SchwingerBelongsToMeasure continuumMeasure schwinger
```

find only declarations, stored fields, and projections from already-filled packages.

Therefore C is not an orphaned constructive-continuum theorem.

### Consequence

No further repository wiring or historical transplant can honestly inhabit A/B/C.  Filling them requires new proof-bearing mathematics: the source localization on the literal selected carrier, the concrete physical finite Hessian/form coercivity package, and the constructive continuum/OS same-object theorem.  Those terms must not be simulated with a record field, postulate, citation, `standardImported` label, Boolean, or proof-status receipt.
