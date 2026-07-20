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

## Defensible measured boundary

At the fixed 15000-epoch horizon:

- weight decay `0.45`: all three seeds are right-censored;
- weight decay `0.50`: one seed reaches 95% test accuracy and two are right-censored;
- weight decay `0.60` through `1.00` on the coarse grid: all three seeds reach 95% test accuracy.

This establishes a **horizon-dependent transition band** for the fixed task and optimiser configuration. It does not establish an absolute critical weight decay. The earlier 10000-epoch scan locating reliable passage near `1.0`, followed by the 15000-epoch scan locating reliable passage at `0.6`, is evidence that the apparent boundary depends on the observation horizon.

## Cross-pollinated research programme

The formal split suggests a disciplined empirical programme:

- treat a persistent train/test separation or MDL plateau as an obstruction candidate, not yet as a proved `Obs`;
- test whether a capacity or representation lift preserves the old learner state and lowers the best attainable total code;
- measure first-passage times with censoring rather than converting horizon failures into impossibility claims;
- estimate a post-crossing contraction rate separately from the pre-crossing waiting time;
- compare explicit coding penalties against L2 weight decay to determine which transitions are genuinely description-length driven;
- only then connect the empirical penalty to `RegularisationCodingBridge` and the measured transition to `GrokkingMechanismWitness`.

This keeps the useful DASHI synthesis—MDL selection, obstruction-triggered lift, and contractive closure—without treating suggestive curves as proofs.

## Next scientific closure obligations

A stronger contribution requires at least one of the following:

1. survival/right-censoring analysis over longer horizons and more seeds;
2. a pre-registered fit of `t95(lambda)` with uncertainty, compared against non-critical alternatives;
3. replication over multiple primes, train fractions, widths, and optimisers;
4. explicit parameter-norm and spectral trajectories tied to first-passage time;
5. a coding theorem connecting the optimisation penalty to `modelCode` rather than treating weight decay as an MDL proxy;
6. a concrete contraction constant after rule-basin entry, permitting an actual upper time bound;
7. a concrete obstruction detector and witness-preserving lift, allowing the ML system to instantiate `LearningCOLBundle` rather than only the generic adapter.

Until those are supplied, the repo claim is the typed operator contract, the exact receipt-level boundary, and the proved adapters between the learning, RG-flow, and COL interfaces.
