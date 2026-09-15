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
| Round78 top-down three-analytic frontier | still stronger conditional compression after structural/source work |
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
three-analytic conditional frontier
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
| C | same-density cutoff-uniform clustering/gap | Heat/Doob + same-density influence | BBD after chart bridge; source-native polymer/cluster expansion; operator route | treating one convenient producer as definition of row C |
| D | same-family OPE/stress/AF identification | local-field/OPE recurrence + same-family stress route | generated-action/common-metric and OS/operator donors | splicing obligations from unrelated continuum families |

## 7. Current Clay-facing Pareto rule

Before working a frozen row:

```text
1. name the exact row consumer;
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

### Row C clustering / mass gap

Do not schedule `prove Heat/Doob` by default. Compare at least:

```text
Heat/Doob same-density
source-native polymer/cluster expansion
unified polymer/Schwinger norm
operator/spectral route
```

against one normalized exact clustering/gap consumer.

### Physical Hamiltonian

Compare the historical rooted-quotient/wavefunction/Hamiltonian construction against the later gauge-invariant-L2/domain/self-adjoint route. Prefer the latter where the consumer does not require the stronger configuration-space quotient.

### Row D / local fields

Require a same-continuum-family weld. Common metric/stress export can donate structure, but cannot define upstream source semantics or splice a different continuum limit into the Clay endpoint.

## 9. Attribution boundary

Primary Clay attribution remains Jaffe–Witten, `Quantum Yang-Mills Theory`, official Clay Mathematics Institute problem description; no DOI is assigned.

The A/B/C/D lettering, ten/seven/four/three decompositions, and producer rankings are DASHI proof-engineering/search structures. Do not attribute those internal decompositions to Jaffe–Witten, Bałaban, or Clay.

Bałaban CMP109/CMP116/CMP119/CMP122 sources remain source authorities for their bounded theorem roles; citation does not make a DASHI decomposition an authorial claim of those papers.

## 10. Bottom line

```text
NS A/B/C/D:
  alternative equation/domain proof programmes.

YM A/B/C/D:
  four internal physical research rows for one Clay YM endpoint.

Clay YM itself:
  one complete solution contract, with multiple in-repo decompositions
  and multiple competing producer constructions under each decomposition.
```

Use this file before interpreting any future statement such as `row C open`, `four YM leaves`, `seven programmes`, or `three analytic theorems`.