# Yang–Mills Clay Endpoint / Decomposition / Producer Map

Status: repository navigation and proof-search reference, not theorem authority.

Companions:

- `Docs/support/reference/YMRHFinalizationProducerAtlas.md`
- `Docs/support/reference/YMRHPRRoundArchaeologyAudit.md`
- `Docs/support/reference/YMCMPWorkStatus.md`

## 1. The first distinction: one official endpoint, many repository decompositions

The repository formalises the Clay/Jaffe–Witten target as one endpoint:

`DASHI/Physics/YangMills/YangMillsClayProblemContractExact.agda`

The final type is:

```text
ClayYangMillsSolution vocabulary
```

Its repository contract has 8 precondition coordinates, 9 postcondition coordinates, and 11 invariants. These coordinates are not separate Clay prize problems; they are the repository's typed contract for one complete Yang–Mills solution.

Therefore:

```text
Clay Yang–Mills
!= four official A/B/C/D subproblems
!= ten official Clay masters
!= seven official Clay programmes
```

Those smaller counts are DASHI proof-search decompositions of the one endpoint.

## 2. NS A/B/C/D and YM A/B/C/D are different kinds of objects

### Navier–Stokes A/B/C/D

The current NS programme nomenclature separates equation/domain variants:

```text
A = unforced whole-space R^3
B = unforced periodic T^3
C = forced breakdown on R^3
D = forced breakdown on T^3
```

Those labels distinguish problem/program variants. Released C/D proof work does not automatically pay A/B; the repository retains an explicit forced-to-unforced firewall.

### Yang–Mills A/B/C/D

YM A/B/C/D are instead a frozen internal research cutset for the one Clay-facing endpoint. They are four physical theorem families selected by the later highest-alpha analysis. They are not four official Clay formulations and should not be described as four independent external submissions.

Canonical owners:

- `BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda`
- `BalabanClayFrozenFourCompletionContractExact.agda`
- later R90/R95/R101 synchronization/correction owners.

Round87 calls the set the shortest literal-Clay research cutset. The frozen completion contract deliberately acts as a scoreboard: a row decrements only when its literal physical completion predicate is inhabited, or when a theorem eliminates the whole row by deriving it from another.

Important audit boundary: this scoreboard is not itself the official endpoint type. Do not infer `A × B × C × D -> ClayYangMillsSolution` merely from the row count unless a concrete compiler supplying the remaining endpoint obligations is identified.

## 3. The frozen YM four-row research cut

### Row A — positive and tuned literal beta trajectory

Consumer shape:

```text
same generated RG history
+ positive bilateral cumulative beta slope on required terminal tails
+ tuned bare coupling / nonvanishing observation window
+ source small-coupling admissibility
```

Typical producer families/donors:

- CMP109 beta / Ward / mixed-derivative producers;
- finite beta-history and inverse-square terminal-history machinery;
- pointwise beta-bound and tuned-family adapters;
- constrained-Gaussian / five-channel / source-native RG constructions.

Do not count a positive beta slope alone as row completion.

### Row B — differentiated marked-source locality / composite-stress shell energy

Consumer shape:

```text
same source-native CMP116 marked coordinates
+ common uniform analytic radii
+ spatial/locality majorant
+ geometric shell-energy decay E_d <= E0 r^d
```

Typical producer families/donors:

- CMP116 localization and marked-source carriers;
- differentiated regular-E/CMP109–116 continuation;
- marked composite/stress fields;
- shell-energy / weighted Hilbert / nuclear-completion machinery;
- unified polymer/Schwinger norm as a stronger conditional producer.

### Row C — same-density clustering / mass-gap family

Primary frozen route:

```text
literal compact-group Gibbs density
+ Heat/Doob curvature history
  1/2 Ric + Hess V_t >= kappa_t g
+ finite negative debt
+ same-density physical covariant influence estimate
-> cutoff-uniform exponential connected clustering
-> gap consequences through downstream reconstruction
```

Competing producer families that must be compared rather than conflated:

1. compact-group Heat/Doob/Langevin route;
2. Bauerschmidt–Bodineau/Polchinski-style weighted criterion after a literal gauge-chart/globalisation bridge;
3. source-native CMP116/polymer/cluster-expansion route;
4. unified polymer/Schwinger norm route;
5. operator-domain / spectral-reconstruction route where the exact consumer permits it.

`row C open` therefore does not mean `prove the current Heat/Doob implementation`; it means compare all exact producers of the clustering/gap consumer first.

### Row D — same-family short-distance/OPE/stress/asymptotic-freedom identification

Consumer shape:

```text
same continuum family
+ physical RG product tail
+ same one-step AF operator-mixing law and normalization
+ local translation Ward/stress law
+ required OPE/local-field identification
```

Typical producer families/donors:

- OPE coefficient recurrence/uniqueness;
- CMP119/CMP116 marked-source stress route;
- Round107–131 same-family stress/Schwinger/common-metric exporter;
- generated-action/first-variation route;
- OS/operator reconstruction donors where they preserve the same continuum family.

Integrated `T00 = H_OS` is useful additional structure but was deliberately not counted as a fifth frozen row.

## 4. Other internal decompositions of the same one Clay endpoint

These are alternate dependency decompositions, not additional prize problems.

| Internal construction | Interpretation |
|---|---|
| Round63 SU(2) backwards compiler | first end-to-end implementation-shaped graph |
| Round64 ten-master compiler | literal Clay endpoint decomposed into ten master obligations |
| Round65 seven-programme compiler | broad honest seven-programme cut |
| six-package / eleven-leaf compiler | intermediate dependency decomposition |
| six-package / ten-physical-leaf compiler | physical-leaf refinement |
| top-down five-theorem closure | stronger packaging of terminal obligations |
| Round65 four-package compiler | conditional collapse if one unified continuum package is inhabited |
| Round78 top-down three-analytic frontier | explicit three-role compiler into `ClayYangMillsSolution` |
| Round87–89 frozen A/B/C/D | four-family research scoreboard for remaining physical analytic work |

These decompositions may not be pairwise equivalent without explicit compilers. A smaller count can be stronger because each item packages more mathematics.

Therefore the correct comparison is not:

```text
10 > 7 > 4 > 3, therefore progress is automatic.
```

It is:

```text
for the exact Clay endpoint,
which packages are actually inhabited,
which implications are theorem-bearing,
and which physical leaves remain unpaid?
```

## 5. Three levels of YM construction that must not be mixed

### Level I — official endpoint contract

One object:

```text
ClayYangMillsSolution
```

### Level II — endpoint decompositions / completion cutsets

Examples:

```text
ten masters
seven programmes
six packages / ten or eleven leaves
five theorems
conditional four packages
frozen A/B/C/D
three-analytic frontier
```

These tell us how a complete solution could be assembled.

### Level III — producers for one row/subconsumer

Examples:

```text
CMP119 regular-E -> BC1
whole A_k -> D1 -> stress
Path13 / Eq119
Heat/Doob
BBD/Polchinski
source-native cluster expansion
unified polymer norm
finite quotient -> Hamiltonian
selected gauge-invariant L2/domain operator
OS reconstruction
common-metric sector export
```

Most day-to-day implementation happens at Level III. Never promote a Level-III producer to a complete Clay construction unless a Level-II compiler closes the other endpoint coordinates.

## 6. Current producer matrix for the frozen rows

| Row | Exact research consumer | Primary/near-primary producer families | Important alternates/donors | Main failure mode to avoid |
|---|---|---|---|---|
| A | same-history positive+tuned beta trajectory | CMP109/Ward + finite beta-history source route | five-channel, interval/certificate, source-native RG | counting one-sided smallness as positive AF slope |
| B | differentiated locality + geometric shell-energy | CMP116 regular-E/marked-source localization | unified polymer norm, stress/Hilbert completion | confusing source transcription/compiler with physical shell estimate |
| C | same-density cutoff-uniform clustering/gap | historical Heat/Doob frozen-row producer | BBD after chart bridge; source-native two-J CMP116 route; unified norm; operator route | treating frozen row C as the definition of the Clay mass-gap consumer |
| D | same-family OPE/stress/AF identification | local-field/OPE recurrence + same-family stress route | generated-action/common-metric and OS/operator donors | splicing obligations from unrelated continuum families |

## 7. Current Clay-facing Pareto rule

Before working a frozen row:

```text
1. name the exact endpoint or row consumer;
2. enumerate all Level-III producers already in repo;
3. quotient only by explicit same-object transports;
4. compare live debt type:
     NEW_ANALYSIS
     SOURCE_REALIZATION
     SAME_OBJECT_TRANSPORT
     CROSS_PROVER_TRANSPORT
     NUMERIC_CERTIFICATE
     COMPILER_PLUMBING
     VALIDATION_ONLY
     PROVENANCE_ONLY;
5. spend proof-search effort only on nondominated producers;
6. after a row is physically inhabited, use an explicit Level-II compiler before claiming any Clay-level decrement.
```

## 8. Immediate Pareto interpretation

### BC1

The active CMP119 regular-E/localization route dominates whole-`A_k` semantics for the BC1 consumer. Whole `A_k` remains important for stress/generated-action provenance.

### Stress / common metric

Whole generated-action / first-variation provenance is the appropriate producer. The regular-E route is only a subobject here.

### Frozen Row C versus the Clay mass-gap endpoint

Do not schedule `prove Heat/Doob` by default. The frozen row-C record is Heat/Doob-shaped, but the literal Clay-facing mass-gap consumer is not.

Round270 explicitly normalizes the endpoint to:

```text
CutoffUniformPhysicalMassGap Y
```

and classifies Heat/Doob/Langevin/Dyson and source-native cluster expansion as optional producer tactics. Direct same-family clustering and direct same-H spectral gap are canonical residuals.

Therefore a direct clustering producer may dominate Heat/Doob for the Clay endpoint without literally inhabiting the historical frozen row-C record. In that situation the correct operation is endpoint rerouting / decomposition supersession, not falsely declaring the frozen row closed.

### Physical Hamiltonian

Compare the historical rooted-quotient/wavefunction/Hamiltonian construction against the later gauge-invariant-L2/domain/self-adjoint route. Prefer the latter where the consumer does not require the stronger configuration-space quotient.

### Row D / local fields

Require a same-continuum-family weld. Common metric/stress export can donate structure, but cannot define upstream source semantics or splice a different continuum limit into the Clay endpoint.

## 9. Explicit top-down three-role Clay compiler

`BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact.agda` is currently the cleanest Level-II finalisation map because it contains an explicit theorem into `ClayYangMillsSolution`.

On one literal Yang–Mills construction `Y`, its independent analytic roles are:

```text
T78-A = UVToContinuumYM Y
T78-B = SameHamiltonianPhysicalMassGap Y
T78-C = SameFamilyLocalFieldsOPEStressWard Y
```

plus structural endpoint data and a standard same-H Gaussian/nontriviality consequence.

The compiler:

```text
literalClaySolutionFromTopDownThree
```

combines those objects into the literal Clay endpoint.

This is a different use of A/B/C lettering from the frozen Round87 A/B/C/D scoreboard. To avoid ambiguity, call these `T78-A`, `T78-B`, and `T78-C` in future archaeology.

## 10. T78-B mass-gap producer Pareto board

Canonical endpoint:

```text
T78-B = CutoffUniformPhysicalMassGap Y
```

Round270 says the producer tactic is not part of that type.

### Candidate 1 — Heat/Doob/Langevin/Dyson

Useful structure:

- same-density LSI;
- curvature/Hessian debt;
- covariant influence;
- stochastic finite speed;
- connected clustering.

Status for T78-B: legitimate alternate producer, but stronger/more structured than the canonical residual.

### Candidate 2 — direct source-native CMP116 two-J route

R279 reduces the finite-scale analytic/source input to:

```text
literal physical J direction F
+ literal physical J direction G
+ same mixed log-generating response
+ CMP116 differentiated localization on the existing hessian/spatial shell
```

The one live finite-scale source theorem is:

```text
round279LiteralTwoJDirectionsToSpatialShellLevel
```

Everything from the shell estimate to geometric covariance decay is compiler-owned.

R280 converts that source-native shell into the route-neutral:

```text
QuantitativeCorrelationDecayTrajectory
```

but retains one independent same-object representation debt:

```text
correlationSnapshotMeaning
```

meaning the continuum-capable correlation snapshot at each scale must evaluate to the same finite covariance proved in R279.

Current Pareto classification:

```text
B1 = SOURCE_REALIZATION
     two literal J insertions -> CMP116 spatial shell

B2 = SAME_OBJECT_TRANSPORT
     correlation snapshot evaluation = same finite covariance
```

This is presently leaner for the canonical clustering residual than the whole Heat/Doob stack.

### Candidate 3 — unified polymer/Schwinger norm

The stronger `PhysicalYMUnifiedPolymerNormProducer` mechanically projects to the same route-neutral `QuantitativeCorrelationDecayTrajectory`.

However the normalized trajectory record deliberately removes large-field, derivative, composite and generic state-distance coordinates. Therefore the whole unified norm is an optional stronger tactic, attractive only if those extra coordinates simultaneously pay T78-A or T78-C cheaply.

### Candidate 4 — direct spectral theorem

A direct same-H spectral theorem can pay T78-B without a clustering proof. This remains a canonical alternative, but it must live on the reconstructed Hamiltonian of the same literal continuum family `Y`.

## 11. Shared downstream path from a quantitative correlation trajectory

R272 proves that any valid finite-scale producer may supply:

```text
QuantitativeCorrelationDecayTrajectory
```

A separate `SameCorrelationTrajectoryCompletion` transports the same correlation object to the continuum limit. The geometric upper bound is then closed under that convergence; no second clustering estimate is needed.

R278 further minimizes the spatial-to-temporal/spectral bridge. The gap contradiction does not require an all-observable clustering upper. It only requires O(4)/same-object transport for observables associated with hypothetical positive subgap modes.

Thus after B1/B2 the remaining B-specific obligations should be classified primarily as representation/same-object payments:

```text
B3 = shared continuum same-correlation completion
     (normally shared with T78-A, not a second B-specific continuum theorem)

B4 = SAME_OBJECT_TRANSPORT / O(4)
     continuum spatial subgap-mode pair
     = temporal spectral pair on the same reconstructed family

B5 = physical spectral interpretation inputs
     required by the clustering -> positive transfer-gap compiler
```

The abstract slow-vs-fast spectral contradiction and gap assembly are already compiler-owned once those physical meanings are supplied.

## 12. Current T78-B Pareto verdict

For the *canonical mass-gap consumer*, the current preferred investigative order is:

```text
1. direct CMP116 two-J source realization (B1)
2. exact correlation snapshot same-object weld (B2)
3. reuse/shared continuum completion from T78-A where possible (B3)
4. least-privilege subgap-mode O(4)/spectral meaning weld (B4/B5)
```

Heat/Doob remains an important alternate and donor, especially where its LSI/semigroup structure pays other consumers. It should not receive primary budget merely because the frozen row-C record was written around it.

## 13. Attribution boundary

Primary Clay attribution remains Jaffe–Witten, `Quantum Yang-Mills Theory`, official Clay Mathematics Institute problem description; no DOI is assigned.

The A/B/C/D lettering, T78-A/B/C naming, ten/seven/four/three decompositions, and producer rankings are DASHI proof-engineering/search structures. Do not attribute those internal decompositions to Jaffe–Witten, Bałaban, or Clay.

Bałaban CMP109/CMP116/CMP119/CMP122 sources remain source authorities for their bounded theorem roles; citation does not make a DASHI decomposition an authorial claim of those papers.

## 14. Bottom line

```text
NS A/B/C/D:
  alternative equation/domain proof programmes.

YM frozen A/B/C/D:
  four internal physical research rows for one Clay YM endpoint.

YM T78-A/B/C:
  three analytic endpoint roles with an explicit compiler into ClayYangMillsSolution.

Clay YM itself:
  one complete solution contract, with multiple in-repo decompositions
  and multiple competing producer constructions under each decomposition.
```

Use this file before interpreting any future statement such as `row C open`, `four YM leaves`, `seven programmes`, `three analytic theorems`, or `mass gap route`.