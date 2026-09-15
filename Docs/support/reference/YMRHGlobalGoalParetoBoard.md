# YM / RH Global Goal Pareto Board

Status: **live proof-search/accounting board**, not theorem authority.

Update rule: every Pareto recut that changes a preferred producer or live terminal leaf must update this file in the same tranche. Historical detail belongs in the companion archaeology/producer documents; this file is the current source of truth for scheduling.

Companions:

- `Docs/support/reference/YMRHPRRoundArchaeologyAudit.md` — full PR/round chronology.
- `Docs/support/reference/YMRHFinalizationProducerAtlas.md` — route/producer inventory.
- `Docs/support/reference/YMClayEndpointDecompositionMap.md` — YM endpoint/decomposition history.
- `Docs/support/reference/YMCMPWorkStatus.md` — CMP109/116/119/122 authority boundary.

## 1. Global scheduling rule

```text
terminal consumer
-> enumerate all in-repo producers
-> quotient only by theorem-bearing same-object transports
-> classify remaining debt
-> Pareto-rank producers
-> BIDI intersect backward consumer search with forward source search
-> only then implement/prove something new
```

Debt classes:

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

## 2. Yang–Mills global endpoint

Official endpoint:

```text
ClayYangMillsSolution
```

Preferred Level-II finalisation compiler:

```text
T78-A = UVToContinuumYM Y
T78-B = SameHamiltonianPhysicalMassGap Y
T78-C = SameFamilyLocalFieldsOPEStressWard Y
```

all on the same literal construction `Y`.

Frozen Round87–89 A/B/C/D are lower-level internal research rows for this one endpoint. They remain useful scoreboards/donors but are not mandatory route architecture when a cheaper producer pays a T78 role directly.

## 3. YM T78-B — current Pareto winner

Terminal consumer:

```text
CutoffUniformPhysicalMassGap Y
```

Current preferred source-native route:

```text
R278 selected finite/continuum covariance carrier
-> R281 reconstructed covariance spectrum
-> R341 direct CMP116 selected-spectrum application
-> positive subgap exclusion / same-H mass gap
```

Heat/Doob/Langevin, unified polymer norm, rooted-shell R284, older R279/R280, and operator-domain/spectral constructions remain alternates/donors. Do not force the terminal consumer through historical frozen Row C.

### 3.1 R341 live coordinates

```text
B1 SAME_OBJECT_TRANSPORT
   CMP116 differentiated source-response magnitude
   = selected literal mixed-log magnitude.

B2 SOURCE_REALIZATION / QUANTITATIVE CALIBRATION
   CMP116 sourceEnvelope
   <= R281 selected spectral clusteringEnvelope.

B3 STANDARD IMPORT / SHARED TOPOLOGY
   one-sided rational upper closed under actual R278 convergence.
```

R341 records `freshYMDecayEstimateIntroduced = false`.

### 3.2 R342 B1 recut — current exact leaf

`BalabanCMP116R281SourceResponseSameObjectRound342Exact.agda` isolates B1 from B2.

Already-owned facts:

1. `NormalizedTwoSourceConnectedCumulantExact.logSecondDirectionAgrees` gives

```text
literalMixedSecondLogDerivative(J(F), J(G))
= selected mixedSecondLogDerivative(F,G).
```

2. R321 already isolates

```text
selected mixed-log magnitude
= CMP109 E^(2)/Pi source magnitude.
```

Therefore current B1 is reduced to:

```text
B1a SAME_OBJECT_TRANSPORT

R338 CanonicalCommonDomainCMP116Source.differentiatedMagnitude
  =
R321 PublishedCMP109SelectedShellPayment.sourceE2PiMagnitude

on the exact selected scale / volume / J(F) / J(G) pair.
```

`r321SameObjectBuildsB1AfterSourceIdentity` compiles B1a + the existing R321 weld into the current R341 B1 witness.

R103 is a useful structural donor: it proves CMP109 polarization = CMP116 physical marked Hessian on one strict differentiated carrier. It does not dominate B1a because it does not supply the selected T5 cutoff/observable/J indexing; forcing B1a through R103 adds carrier-identification debt.

Current statuses:

```text
R342 B1 compiler                          machineChecked status
B1a CMP109/CMP116 source-source identity conditional
B2 envelope calibration                  conditional
B3 one-sided closure                      standardImported
fresh YM decay estimate                   false
Clay promotion                            false
```

CMP116 source authority does not manufacture B1a.

### 3.3 B2 stop condition

No direct theorem-bearing sourceEnvelope -> R281 clusteringEnvelope calibration exists elsewhere in the current repo.

R284/R339 can route through selected rooted-shell/geometric structure, but they require extra root/distance/time/envelope coordinates. That route is stronger and therefore Pareto-dominated for the R341 consumer unless those extra coordinates become independently free.

Current T78-B frontier is genuinely `{B1a, B2}` plus standard one-sided closure.

## 4. YM T78-A — UV -> same continuum YM

Target:

```text
UVToContinuumYM Y
```

This remains a bundle:

```text
literal weak-coupling RG construction
+ continuum limit of same finite family
+ Schwinger belongs to same continuum measure
+ accepted OS/Wightman axioms
+ reconstructed Hilbert space
+ positive self-adjoint Hamiltonian
```

Current status:

```text
OPEN / producer audit incomplete.
```

Prefer shared continuum/OS/operator completion with T78-B and T78-C rather than duplicating a second continuum construction. Historical Prokhorov/all-scale RG packaging is not automatically the cheapest route.

## 5. YM T78-C — same-family local fields / OPE / stress / Ward

Target:

```text
SameFamilyLocalFieldsOPEStressWard Y
```

Round78 requires the local-field/OPE/stress/Ward object on the SAME continuum family/Hamiltonian as T78-A/B.

The later repo has already removed several historical overpayments. Current producer audit gives four physical/source coordinates:

### C1 — one completed marked state supplies composite + stress fields

`BalabanMarkedSourceCompositeStressFieldExact` compiles two marked coordinates on the SAME completed differentiated RG state into continuum composite and stress nuclear fields.

Live physical payment:

```text
construct the literal stress marked-source data on the same completed RG state,
including the cutoff-independent Hilbertian modulus required by the existing
marked-source completion theorem.
```

A second unrelated continuum stress completion is not required.

### C2 — physical composite/OPE identification

`YangMillsSharedMarkedCompositeOPERemainderExact` proves that the shared composite-mark tail is already the exact `DyadicOPERemainderMajorant`. Pure geometric decay of the OPE remainder is compiler-owned.

Live payment:

```text
actual gauge-invariant curvature/composite insertion on the same continuum family
+ its physical RG remainder = the shared composite-mark tail.
```

Do not prove a second geometric OPE convergence theorem.

### C3 — OPE coefficient / AF identification

`BalabanOPECoefficientRGRecurrenceUniquenessExact` proves all-depth coefficient equality from:

```text
same UV normalization
+ physical coefficient obeys the same one-step mixing map
+ AF/reference coefficient obeys that same one-step map.
```

The AF/reference recurrence is compiler/donor structure. The live Yang–Mills payment is the literal same-family one-step composite coefficient identification + common UV normalization. An all-depth coefficient comparison is overpayment.

### C4 — local stress/Ward -> same-H generator

`YangMillsLocalChargeCommutatorToCoreStabilizationExact` and `YangMillsStressChargeLocalCoreCutoffStabilizationExact` remove global spatial-cutoff convergence as a primitive.

Live physical inputs:

```text
local current/charge shell decomposition
+ outer-shell commutator vanishes beyond observable support
+ vacuum-neutral Ward relation on A Omega
-> compiler-owned eventual local-core cutoff independence
-> self-adjoint/closable local charge
+ same reconstructed OS translation group/Hamiltonian.
```

The last same-H identification should share the T78-A reconstructed-Hamiltonian carrier rather than build a second Hamiltonian.

### T78-C current verdict

```text
C1 same-family marked composite/stress field realization
C2 physical composite/OPE remainder identification
C3 one-step OPE/AF coefficient identification + UV normalization
C4 local Ward/current realization + same-H charge identification
```

This is the current C accounting; historical monolithic `ContinuumLocalOperatorOPEStressTensor` remains a target/donor, not the preferred proof-search granularity.

Whole-action `A_k` semantics belongs here when first-variation/stress provenance requires it. Do not make it a prerequisite of the shorter BC1 regular-E route.

## 6. RH global endpoint

Terminal strategy is producer-agnostic. Current acquisition map remains the universal pole-quotient direct route.

### 6.1 RH R1 — first high-route representation wall

```text
nearResponseAt(chosen J)
= finiteNearSum(cellResponse)
```

Classification:

```text
SAME_OBJECT_TRANSPORT / representation theorem
```

The evaluator-independent literal kernel is already owned as an interface. The checked Lean return records the near/far theorem but does not transport this exact finite representation equality into Agda. Earlier archaeology found no theorem-bearing `nearSignedSum` / `nearOffFinset` copy in the current Agda tree/history.

Current status:

```text
OPEN / genuine representation implementation unless source proof bytes reappear.
```

### 6.2 RH R2 — first high analytic wall

Direct form:

```text
literalNear(J) + B_far(J) + D_Gamma(g_pole)
< actual ClusterResponse(g_pole)
```

Optional proof-carrying certificate form:

```text
nearResponseAt(J) <= U
and
U + B_far(J) + D_Gamma(g_pole)
< actual ClusterResponse(g_pole).
```

Classification:

```text
NEW_ANALYSIS
```

Pruned primitive requirements:

```text
intermediate M_cluster
separate finite-near envelope theorem
separate Gamma envelope theorem
final balance as analytic input
determinant-q payment
```

8889 remains `STATUS ONLY / SAME_OBJECT_BLOCKED` until theorem-bearing proof/carrier transport is recovered.

### 6.3 RH R3 — independent terminal coordinate wall

One same-carrier analytic-coordinate package now feeds low-region verification and critical-line stability.

Live work:

```text
criticalLine iff Re = 1/2 on the same AnalyticSubstrate
equality stability
theorem-bearing interpretation of published numeric verified region
on the abstract analytic Real carrier
```

Opaque same-predicate / exact-height Set receipts are pruned. Numeric verified-region interpretation remains live and independent of R1/R2.

## 7. Current cross-lane Pareto queue

```text
1. YM T78-B / R342 B1a
   CMP109 E^(2)/Pi source magnitude
   = R338 canonical CMP116 differentiated magnitude.

2. YM T78-B / B2
   direct source-envelope -> R281 spectrum-envelope calibration.

3. RH R1
   exact final-near finite representation; stop archaeology unless theorem-bearing source bytes appear.

4. YM T78-C / C1-C4
   work only if one leaf gains a cheaper same-object/source route than RH R1;
   current recut is now explicit above.

5. YM T78-A
   fresh producer audit with shared continuum/OS/Hamiltonian completion preferred.

6. RH R2
   begin fresh analysis after R1, unless an exact donor pays the same literal scalar inequality.

7. RH R3
   keep numeric verified-region / critical-line carrier work independent from R1/R2.
```

## 8. Accounting invariants

- One YM Clay endpoint; T78-A/B/C and frozen A/B/C/D are internal decompositions.
- A cheaper terminal producer can route around a historical research row without declaring that historical row literally inhabited.
- Source authority != source realization.
- Same scalar shape != same-object theorem.
- Cross-prover status != transported proof.
- Compiler closure != physical theorem closure.
- Standard imported analysis may remove generic work but never manufactures physical same-object/calibration data.
- Historical donors are retained append-only even when dominated.
- Every Pareto recut updates this board before the tranche is considered complete.

## 9. Snapshot

Date: 2026-09-15 Australia/Brisbane.

```text
YM T78-B: preferred route R341; current smallest B1 leaf is R342 B1a; B2 independent.
YM T78-C: recut to C1 marked fields, C2 composite/OPE identity, C3 one-step OPE/AF law, C4 local Ward/same-H stress charge.
RH high: R1 representation then R2 strict actual-ClusterResponse family.
RH terminal: R3 verified-region / critical-line same-carrier interpretation remains independent.
YM T78-A: next un-audited global producer bundle.
```

No Clay Yang–Mills solution or RH proof is claimed by this accounting document.
