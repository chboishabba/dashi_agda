# Conscious access as a state-dependent network of networks

## Status

This tranche is a **candidate formal architecture for access-consciousness**. It does not claim a complete theory of phenomenal consciousness, a neural diagnosis, a psychedelic treatment theorem, a recovered-memory method, or a one-to-one identification of psychoanalytic terms with neural structures.

The implementation translates the supplied discussion into finite, checked theorem shapes while reusing existing DASHI carriers rather than adding a separate brain ontology.

## Existing spine reused

The tranche composes the existing:

- `DASHI.Biology.Core.ContextIndexedSystem` context-indexed projection;
- `DASHI.Biology.Cell.BioelectricNetwork` voltage, channel, gap-junction, chemical, mechanical and regulatory state carrier;
- `DASHI.Biology.FunctionalConnectomeBodyMemoryBridge` structural/functional connectome and proxy boundaries;
- `DASHI.Biology.NeurochemicalBrainCarrierBridge` synaptic, volume-transmission and neuromodulatory carrier;
- `DASHI.Biology.PredictiveMetastabilityTraumaBridge` prior precision, local-minimum and chart-mobility boundary;
- `DASHI.Biology.BraidedEmotionDynamics` recurrent, world-resistant and co-regulated episode transitions;
- `DASHI.Biology.RelationalChartResidualMachine` chart-local residual and successor-state machinery;
- `DASHI.Core.RelationalHypervoxelBraidCore` non-collapsing braid and shared-root/ultrametric locality;
- `DASHI.Geometry.SSP369Ultrametric` exact prefix ultrametric over `369` addresses.

## 1. Stateful biological transform

The local computational primitive is not a timeless scalar activation. It has the form

```text
(Input × State × Modulator) -> (Output × State).
```

`StateDependentMultiplexTransducer.agda` gives a finite deterministic instance

```text
output = input xor priorState xor modulator
state' = priorState xor modulator
```

and proves exactly that:

- the same input with a different prior state can produce a different output;
- the same input and state with a different modulator can produce a different output;
- the modulator can alter the successor state;
- the existing context-indexed projection and bioelectric network can instantiate the same structural claim.

This is a finite structural theorem, not a claim that Boolean dynamics are a complete neuron model.

## 2. Productive coherence

Coherence is not defined as parallel vectors or identical local encodings. It is defined as compatibility under transformation.

For transforms

```text
A --first--> B --second--> C
 \----------------direct-> C
```

the exact finite core requires

```text
direct x = second (first x).
```

`ProductiveTransformCoherence.agda` proves three useful cases:

1. **Productive opposition:** two inhibitory transforms can recompose to the identity.
2. **Different coordinates, same latent relation:** one chart encodes `x`, another encodes `not x`, and the chart transition makes the latent square commute.
3. **Order residual:** inhibition followed by saturation differs from saturation followed by inhibition, proving that transform order can carry information.

The exact equalities are a zero-defect prototype. A later quantitative layer may replace equality by a metric defect bound.

## 3. Sparse production and global conditional readability

`SparseExpertRoutingCoalition.agda` separates:

```text
all experts active
```

from

```text
content conditionally readable by many experts.
```

A finite four-expert carrier proves that two-expert routes are sparse while a globally addressed result remains readable by a non-producing planning expert. This is an MoE-inspired architectural analogy, not a literal claim that the brain implements a modern machine-learning router.

## 4. Relational access and recurrent coalition

`ConsciousAccessCoalition.agda` makes consciousness a relation between a representation and a context:

```text
available : Context -> Representation -> Bool.
```

The same trace is exactly unavailable in a restricted local context and available in a recurrent global context. Consciousness is therefore not installed as an intrinsic tag on the trace.

The recurrent access cycle is:

```text
recruitment
  -> transformation
  -> coherent regime
  -> redistributed constraint
  -> updated state
  -> recruitment.
```

This replaces a permanent sink with a **sink-transform-source-update regime**. The coalition must track:

- transformational compatibility;
- recurrent viability;
- broad conditional reach;
- counterfactual influence;
- self-conditioning.

The aggregate directly contains the existing connectome, neurochemical, predictive-metastability, braided-emotion and relational-chart carriers.

## 5. The unconscious as an access regime

`UnconsciousAccessRegime.agda` proves a finite version of:

```text
generated representation
+ blocked access
+ continuing causal effect.
```

Two representations are both blocked by the access gate, yet their action readouts differ. Lack of access therefore does not imply causal inertness.

The same declarative trace is unavailable in one access context and available in another, so memory kind does not determine consciousness.

This reconstructs repression-like language as a stable access-avoidance regime without installing a separate unconscious substance or a psychoanalytic diagnosis.

## 6. Symbolic transform without a homunculus

`SymbolicTransformWithoutHomunculus.agda` distinguishes a latent invariant from its local rendering.

A direct and a transformed symbol:

- use different constructors;
- preserve the same latent invariant;
- can have different access costs;
- require no inner translator field.

A separate condensation theorem shows that distinct latent inputs can map to the same rendering. A symbol is therefore neither a fixed dictionary lookup nor guaranteed recovery of hidden memory.

## 7. Ultrametric attractor reweighting

`PsychedelicAttractorReweightingBoundary.agda` consumes the existing exact `369` prefix ultrametric. For three depth-two addresses it proves distances:

```text
habitual to itself      = 0
habitual to nearby      = 1
habitual to crossBranch = 2.
```

It then constructs baseline and reweighted finite regimes in which:

- routing threshold is no higher;
- modular segregation is no higher;
- high-level prior precision is no higher;
- reachable repertoire is no smaller;
- the habitual basin is relatively less privileged;
- a previously expensive cross-branch state is relatively cheaper.

A three-state motif transition proves recurrence without reducing visions to unstructured noise or assigning a universal symbolic dictionary.

These are exact comparative statements about the finite model. They are not empirical effect-size estimates or clinical claims.

## 8. Determinism under coarse-graining

`DeterministicCoarseGrainingBoundary.agda` gives a concrete no-go theorem.

The microscopic state is

```text
visible × hidden
```

with deterministic update

```text
visible' = visible xor hidden
hidden'  = hidden.
```

Two microstates have the same visible macrostate but different next visible states. The module proves:

```text
there is no f : Bool -> Bool
such that project (microStep m) = f (project m)
for every microstate m.
```

Thus deterministic microdynamics need not induce closed deterministic macrodynamics after information-losing projection. An effective stochastic description therefore does not by itself settle the ontology of randomness.

## 9. Source atlas

`ConsciousAccessNetworkSourceAtlas.agda` records title, authors and DOI/arXiv DOI where available for:

- Samantha Brooks, *How your conscious and unconscious mind interact*;
- Mashour, Roelfsema, Changeux and Dehaene, *Conscious Processing and the Global Neuronal Workspace Hypothesis*, DOI `10.1016/j.neuron.2020.01.026`;
- Cogitate Consortium et al., *Adversarial testing of global neuronal workspace and integrated information theories of consciousness*, DOI `10.1038/s41586-025-08888-1`;
- Beniaguev, Segev and London, *Single cortical neurons as deep artificial neural networks*, DOI `10.1016/j.neuron.2021.07.002`;
- London and Hausser, *Dendritic computation*, DOI `10.1146/annurev.neuro.28.061604.135703`;
- Battiston, Nicosia, Chavez and Latora, *Multilayer motif analysis of brain networks*, DOI `10.1063/1.4979282`;
- Carhart-Harris and Friston, *REBUS and the Anarchic Brain*, DOI `10.1124/pr.118.017160`;
- Carhart-Harris et al., *The entropic brain*, DOI `10.3389/fnhum.2014.00020`;
- Tagliazucchi et al., *Enhanced repertoire of brain dynamical states during the psychedelic experience*, DOI `10.1002/hbm.22562`;
- Power et al., *Grokking*, arXiv DOI `10.48550/arXiv.2201.02177`.

The atlas records how each source motivates a limited bridge and what is not promoted from it.

## Exact theorem surface

`ConsciousAccessNetworkRegression.agda` assembles the tranche and checks:

- state and modulator dependence;
- productive double inhibition;
- noncommutative transform-order residual;
- context-relative access;
- full coalition criteria;
- recurrent reopening of recruitment;
- exact ultrametric distances;
- comparative routing and repertoire inequalities;
- recurrent motif dynamics;
- source count;
- causal efficacy under blocked access;
- symbolic invariant preservation and carrier difference;
- deterministic coarse-graining no-go;
- sparse routing with global conditional readability;
- fail-closed single-ignition, phenomenal-identity and treatment boundaries.

## Honest frontier

This tranche does **not** prove that the finite carriers are an empirically complete model of the brain. The next mathematical and empirical producers are:

1. replace exact Boolean compatibility with a quantitative defect on typed local metric spaces;
2. define a genuinely time-indexed multiplex graph whose effective edge transforms depend on cellular and chemical state;
3. connect recurrent viability to a nontrivial finite or continuous stability theorem;
4. connect ultrametric address costs to measured neural state-transition data without reverse inference;
5. distinguish access-consciousness, report, metacognition and phenomenal claims with experimentally anchored observation maps;
6. test whether the proposed routing/reweighting inequalities are supported across psychedelic compounds, doses, tasks and measurement modalities;
7. retain the current no-diagnosis, no-recovered-memory and no-treatment-authority boundaries.

The focused validation command is:

```bash
bash scripts/check_conscious_access_network_of_networks.sh
```
