# DASHI grokking operator formalism

## Status

This tranche is a **proved specification plus empirical receipt surface**. It does not claim a new universal law of grokking, an asymptotic critical exponent, or that AdamW weight decay is literally minimum-description-length optimisation.

The implementation connects machine-learning experiments to existing DASHI surfaces:

- `DASHI.Geometry.RGFlowContract`: a state update equipped with an ultrametric contraction witness and an MDL Lyapunov function;
- `DASHI.Geometry.COL`: contraction, stable obstruction, and witness-preserving lift;
- `DASHI.Learning.GrokkingOperatorContract`: a two-part code-length learner, metric closure, horizon-aware first-passage observations, and the decomposition `t_grok = t_cross + t_contract`;
- `DASHI.Learning.GrokkingCOLBridge`: a level-indexed adapter from learning operators into the existing COL architecture, plus explicit obligations for regularisation-to-code and observation-to-mechanism bridges;
- `DASHI.Learning.Mod97WeightDecayReceipt`: the recorded modular-multiplication experiment;
- `DASHI.Learning.Mod97GrokkingBoundary`: exact consequences of those receipts without promotion beyond the measured horizon;
- `DASHI.Learning.GrokkingCircuitTemporalAlignmentExact`: a Stage-6/7 receipt bridge comparing predeclared circuit-beta transitions against first-passage timing without promoting the comparison into a mechanism proof;
- `DASHI.Learning.Mod97CircuitRuntimeBoundaryExact`: typed separation among runtime producer implementation, execution, historical identity, leakage control, oriented damage adaptation, observation adequacy, relation payment, beta maximality, and mechanism payment;
- `DASHI.Learning.GrokkingRegression`: compact import and value regression surface.

## Learning operator

For learner state `s`, the formal contract separates

```text
dataCode(s)   : residual/data code length
modelCode(s)  : model/structure code length
totalMDL(s)   = dataCode(s) + modelCode(s)
```

and requires

```text
totalMDL(step(s)) <= totalMDL(s).
```

A metric learning operator additionally supplies an existing DASHI `Ultrametric` and `Contractive` witness. The adapter `asRGFlowAxioms` then exposes the learner through `DASHI.Geometry.RGFlowContract` rather than inventing a parallel contraction formalism.

This is intentionally stronger than the current PyTorch experiment. AdamW supplies a decoupled L2-like pressure, but no theorem in this tranche equates that pressure with the explicit two-part MDL code.

## COL integration

`GrokkingCOLBridge` turns a level-indexed learning family into a `COL` system by the following exact identifications:

```text
COL.E n      = totalMDL of the level-n learner
COL.K n      = the level-n learning update
COL.Obs n    = an explicitly supplied stable obstruction detector
COL.lift n   = an explicitly supplied witness-preserving capacity lift
```

The existing `E-monotone-iter` theorem then immediately yields repeated-update MDL monotonicity at each level. This is the formal cross-pollination between the ML tranche and DASHI's capacity-growth story: depth or model enlargement is not silently scheduled; it is exposed as a lift that requires an obstruction and embedding witness.

Two non-derivations are made explicit:

1. `RegularisationCodingBridge` is the missing coding theorem needed before an empirical penalty such as AdamW weight decay can be identified with `modelCode`.
2. `GrokkingMechanismWitness` is the missing bridge needed before a measured first-passage curve can be identified with the formal crossing-plus-contraction decomposition.

Thus the empirical receipt, the MDL interpretation, and the contraction mechanism remain connected but logically distinct.

## Grokking-time decomposition

The operator interpretation keeps two times distinct:

```text
t_grok = t_cross + t_contract
```

- `t_cross` is the long model-selection or basin-entry period;
- `t_contract` is the within-rule-basin convergence period.

The Agda record stores the equality as a required witness. A quantitative upper bound must be supplied by concrete crossing and contraction theorems; it is not inferred from an accuracy curve.

## Empirical task

The current receipt fixes:

- modular multiplication modulo `97`;
- `9409` total pairs;
- `2822` training pairs and `6587` test pairs;
- a shared residue embedding, one ReLU hidden layer, and a 97-way output;
- full-batch AdamW with learning rate `0.001`;
- three seeds;
- a `15000`-epoch horizon with measurements every `20` epochs.

Weight decay is stored in thousandths, so `600` denotes `0.6`. Accuracy is stored in permille. A missing `t95` is represented as `rightCensored`, not as proof that grokking never occurs.

The checked-in receipt does **not** fix the original embedding width, hidden width, or exact split-generation procedure. Those coordinates therefore remain provenance debt. Matching an old weight decay, seed, first-passage time, or final accuracy cannot by itself identify a regenerated run with the historical run.

## Defensible measured boundary

At the fixed 15000-epoch horizon:

- weight decay `0.45`: all three seeds are right-censored;
- weight decay `0.50`: one seed reaches 95% test accuracy and two are right-censored;
- weight decay `0.60` through `1.00` on the coarse grid: all three seeds reach 95% test accuracy.

This establishes a **horizon-dependent transition band** for the fixed task and optimiser configuration. It does not establish an absolute critical weight decay. The earlier 10000-epoch scan locating reliable passage near `1.0`, followed by the 15000-epoch scan locating reliable passage at `0.6`, is evidence that the apparent boundary depends on the observation horizon.

## Runtime checkpoint, relation, and beta frontier

PR #900 now contains an executable but deliberately unexecuted pure/runtime spine for a **new checkpoint-bearing Mod97 run family**:

```text
scripts/mod97_checkpoint_producer.py
scripts/mod97_circuit_intervention_producer.py
scripts/mod97_relation_classifier.py
scripts/mod97_relation_graph_compiler.py
scripts/mod97_closed_compatible_capacity.py
```

The checkpoint producer preserves the source-paid coordinates above but requires the previously unpaid architecture and split coordinates explicitly. Its manifests and saved checkpoints retain:

```text
historical_receipt_same_run = false
historical_receipt_same_configuration = false
historical_checkpoint_reconstruction = false
```

so regeneration cannot silently rewrite the old receipt into checkpoint custody.

The intervention producer uses the Fly-style leakage firewall operationally:

```text
training activations
-> predeclare/freeze candidate hidden units
-> held-out singleton and joint ablations
-> raw effect receipt
```

Held-out outcomes do not select the candidate units. The current rule ranks units by mean absolute post-ReLU activation on the training carrier with deterministic unit-index tie breaking. That rule is a local experimental method, not a source-derived fact or universal circuit definition.

The held-out effect is represented first as the signed change in cross-entropy loss. For compatibility with the existing non-negative `PairInterventionScore` carrier, the producer also emits an orientation-aware Nat adapter:

```text
larger held-out loss = worse
Nat damage = max(0, round(lossIncrease * 1_000_000))
```

The raw signed value is retained. A beneficial ablation therefore remains visible in the receipt even though its contribution to the non-negative damage carrier is zero. The `1_000_000` scale is experiment metadata, not a physical or source-derived unit.

The current producer-safe relation classifier mirrors the formal threshold rule only on the observation coordinates that are actually available:

```text
adequacy/power unpaid -> underpowered
interaction excess > frozen threshold -> conflict
otherwise -> independent
```

It has no `gluingRequirement` branch. That is not because canonical `gluingRequirement` means a physical hidden-unit wire. The canonical RSA/NDim relation means **selection closure**: selecting one candidate may require another so that an operator/seam compatibility condition closes.

The current singleton/joint pair-ablation observation is inadequate for the query “which directed requirement closure holds?”. `GrokkingSparseActiveColouringRoutingExact` now pays this with an exact query-indexed fibre collision: two worlds expose the same observed pair effects while one has `left requires right` and the other `right requires left`. Therefore requirement direction does not factor through the current pair-ablation surface.

This reuses `QueryIndexedProjectionAdequacyExact`; its Blackwell citation remains conceptual precedent for information comparison only. The finite requirement-direction collision is a repository-local theorem and imports neither empirical truth nor authority from that citation.

The fail-closed relation-graph compiler consumes only already-paid canonical relation receipts:

```text
conflict            -> undirected coexistence prohibition
gluingRequirement   -> directed selection-closure edge; direction must be paid
independent         -> retained audit pair; no graph constraint
```

Unpaid relation classifications are rejected. A `gluingRequirement` without a paid direction is rejected. The compiler therefore cannot manufacture the missing requirement direction from raw pair effects.

The exact finite capacity producer then exhaustively enumerates the supplied finite graph:

```text
beta(G,R) = max |S|
subject to S conflict-free and requirement-closed
```

For the intended 12-unit frozen carrier, the reference exhaustive search examines `2^12 = 4096` subsets. This is an exact local certificate for the supplied paid graph, not a universal optimisation theorem.

The typed runtime frontier deliberately keeps these states separate:

```text
checkpoint producer implemented != checkpoint executed
intervention producer implemented != intervention executed
relation classifier implemented != classifier executed
relation-graph compiler implemented != compiler executed
beta producer implemented != beta executed
historical run/config identity != regenerated run provenance
Nat damage adapter paid != relation classification paid
pair-ablation effects != requirement direction
paid relation graph != beta transition through training
beta maximality != Grokking mechanism
```

At the current repo frontier, all five producer/compiler surfaces above are implemented but unexecuted. Historical run/config identity remains unestablished, training/held-out selection separation is encoded, and the Nat damage adapter is paid. Requirement direction, empirical relation classification, empirical beta maximality, and mechanism promotion remain unpaid.

## Circuit-mechanism temporal alignment

PR #900 adds a second, independent receipt family for candidate circuit structure. The intended composition is:

```text
GrokkingObservation || GrokkingCircuitTrajectoryReceipt
                    -> GrokkingTemporalAlignmentReceipt
```

The circuit side retains intervention-paid conflict / gluing-requirement / independence relations and the finite requirement-closed compatible-family observable `beta`. The Learning-side bridge compares the first paid beta transition against the existing horizon-aware `test95` first passage.

The temporal classes are:

```text
betaBeforeTest95
betaCoincidentWithTest95
betaAfterTest95
betaTransitionUnobserved
firstPassageRightCensored
notComparable
```

The comparison is admissible only under matched run/split/horizon identity, stable extraction/intervention/threshold rules, paid beta maximality receipts, fixed checkpoint cadence, and a no-leakage rule. Held-out `test95` outcomes may not select the circuit extraction rule, intervention threshold, beta threshold, or coincidence tolerance.

This imports the Fly NDim discipline structurally:

```text
select on the fitting/training carrier
-> freeze the selected rule
-> evaluate held-out outcome
```

and the RSA/NDim discipline structurally:

```text
classify relations
-> close requirements
-> select conflict-free requirement-closed family
-> validate the downstream consumer
```

The bridge retains the following WrongType boundaries:

```text
beta-before-test95 != causal mechanism
alignmentPromotionPaid != GrokkingMechanismWitness
cross-seed stability != cross-task stability
beta increase != held-out improvement
requirement closure != physical causal wiring
```

A beta transition may eventually be evidence for pre-crossing structural reorganisation, crossing/basin entry, post-crossing contraction/cleanup, or merely a correlate. The formal carrier does not choose among these interpretations.

## Cross-pollinated research programme

The formal split suggests a disciplined empirical programme:

- treat a persistent train/test separation or MDL plateau as an obstruction candidate, not yet as a proved `Obs`;
- test whether a capacity or representation lift preserves the old learner state and lowers the best attainable total code;
- measure first-passage times with censoring rather than converting horizon failures into impossibility claims;
- estimate a post-crossing contraction rate separately from the pre-crossing waiting time;
- compare explicit coding penalties against L2 weight decay to determine which transitions are genuinely description-length driven;
- predeclare circuit extraction/intervention rules and measure beta trajectories without using held-out passage to tune them;
- compare circuit-transition timing against `test95` only after the circuit rule is frozen;
- only then connect the empirical penalty to `RegularisationCodingBridge` and the measured transition to `GrokkingMechanismWitness`.

This keeps the useful DASHI synthesis—MDL selection, obstruction-triggered lift, contractive closure, intervention-paid circuit structure, and temporal validation—without treating suggestive curves as proofs.

## Next scientific closure obligations

A stronger contribution requires at least one of the following:

1. survival/right-censoring analysis over longer horizons and more seeds;
2. a pre-registered fit of `t95(lambda)` with uncertainty, compared against non-critical alternatives;
3. replication over multiple primes, train fractions, widths, and optimisers;
4. explicit parameter-norm and spectral trajectories tied to first-passage time;
5. a coding theorem connecting the optimisation penalty to `modelCode` rather than treating weight decay as an MDL proxy;
6. a concrete contraction constant after rule-basin entry, permitting an actual upper time bound;
7. a concrete obstruction detector and witness-preserving lift, allowing the ML system to instantiate `LearningCOLBundle` rather than only the generic adapter;
8. execute the new checkpoint-bearing Mod97 producer in a PyTorch-capable environment and retain the generated checkpoint/receipt hashes;
9. execute the frozen training-selected / held-out-evaluated singleton/joint intervention producer over those checkpoints;
10. predeclare and pay the classifier adequacy/power rule, then execute conflict/independent classification under the frozen interaction threshold;
11. define a richer **consumer-specific closure observation** capable of distinguishing opposite directed `gluingRequirement` worlds; the current symmetric pair-ablation surface is formally inadequate for this query;
12. compile the paid relation receipts and execute exact finite beta certification at each checkpoint;
13. cross-seed replication of the predeclared circuit extraction/intervention/classification rule;
14. cross-task/config transfer across at least another modulus, train fraction, width, or optimiser;
15. timing-null comparisons, including epoch-label permutation or equivalent temporal-null tests;
16. threshold-robustness analysis under a predeclared admissible grid or interval;
17. an active-support-only baseline establishing whether beta adds information beyond raw participation changes.

Until those are supplied, the repo claim is the typed operator contract, exact receipt-level boundaries, implemented-but-unexecuted runtime/classifier/compiler/beta producers, the orientation-aware damage adapter, the exact requirement-direction nonfactorability witness, the circuit temporal-alignment carrier, and the proved adapters between the learning, RG-flow, COL, and circuit-receipt interfaces—not a universal grokking mechanism.
