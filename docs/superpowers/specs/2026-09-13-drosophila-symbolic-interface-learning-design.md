# Drosophila Symbolic Interface Learning Design

## Purpose

Formalise the current viral "fruit fly writes Python" demonstration as a source-bounded symbolic-interface experiment over the repository's existing Drosophila MaleCNS, Animalexic, learning, decision, provenance, and nonfactorability machinery.

The design must preserve the strongest scientifically useful claim without promoting the meme wording into a biological conclusion.

## Existing owners reused

The new tranche composes rather than replaces:

- `DASHI/Biology/DrosophilaMaleCNSEffectorObservationBridge.agda`: structural connectome, neural state, motor/effector continuation, body/behaviour, sensory return, and explicit connectome/dynamics/effector firewalls.
- `DASHI/Biology/AnimalexicDrosophilaEmbodiedBridge.agda`: candidate/promotion governance, multimodal observations, intervention language, and neural-state/behaviour/meaning separation.
- `DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda`: recurrent active-sensing carrier and learning/non-promotion boundaries from stacked PR #895.
- `DASHI/Cognition/PNF/DecisionOutcomeLearningFeedbackExact.agda`: outcome -> learning -> future action relevance.
- `DASHI/Core/AttributedSourceCore.agda`: source identity and non-promoting attribution.
- `DASHI/Core/IntersectionalNonFactorability.agda`: collision witnesses and post-rechart non-recovery.

## Source/provenance model

The viral demonstration is not treated as a neuroscience paper. Its source role is an experimental/demo claim about a software interface around a simulated connectome-derived neural carrier.

The source bundle must keep separate:

1. the primary scientific connectome sources already represented by the MaleCNS owners;
2. the social/demo manifestation claiming a simulated fly brain produced Python/FizzBuzz through a keyboard-like interface;
3. any implementation repository or technical account that can pay the interface, dynamics, training, or evaluation details;
4. secondary media that can locate the demo but cannot independently pay its hidden implementation details.

Identity is fail-closed. A social handle/display name such as `Nalin` must not be identified with a named academic researcher without a same-object source receipt.

## Core carrier

The experiment is represented as the typed chain

```text
ConnectomeCarrier
  -> ExecutableDynamics
  -> NeuralState
  -> InterfaceDecoder
  -> SymbolicActuator
  -> TokenStream
  -> ProgramText
  -> ParseResult
  -> RuntimeResult
  -> TaskEvaluation
```

with a distinct update lane

```text
TaskFeedback
  -> LearningUpdate
  -> NextExecutableState/Policy
```

The keyboard is an artificial actuator. It is not silently identified with biological muscle output or native Drosophila motor semantics.

## Competence ladder

The formalisation distinguishes at least the following levels:

```text
neural activity exists
< mapped key/token emission
< non-empty source text
< syntactically valid Python
< executable Python
< correct FizzBuzz on declared examples
< correct FizzBuzz on held-out cases
< transfer to another programming task
< general programming competence
```

No lower level automatically promotes to a higher level.

## Assistance budget

A task run must carry the external assistance coordinates needed to interpret the result:

- sensory/input encoding;
- neural dynamics rule;
- initial state/seed;
- decoder/output mapping;
- training/update rule;
- reward/fitness signal;
- prompt/template/scaffold, if any;
- parser/runtime/evaluator;
- number of attempts or search budget;
- selection/cherry-picking policy.

A successful output is not attributable to the connectome alone unless the required ablations/nulls close those dependencies.

## Null-model obligations

The strongest future promotion route compares the same task/interface/training budget against controls such as:

- shuffled or degree-preserving rewired connectivity;
- randomized neuron identities;
- generic recurrent network matched in size or budget;
- identical decoder with no learning;
- identical learning under alternate initialization.

The tranche does not claim those experiments have been run unless a receipt exists.

## Required WrongType / non-promotion boundaries

The owner must block all of:

```text
connectome map = executable brain dynamics
simulated dynamics = living fly cognition
external symbolic actuator = native biological effector
emitted characters = Python knowledge
valid syntax = correct task solution
FizzBuzz success = general programming competence
one successful run = learned policy
training/update = biological synaptic plasticity
social caption = technical implementation receipt
secondary media report = primary implementation proof
shared name/display name = person identity
connectome-derived success = causal advantage of biological topology
```

It must also preserve the #895 boundary that empirical task performance proves neither metaphysical determinism nor libertarian free will.

## Minimal implementation shape

Create one focused owner:

`DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda`

Create one focused regression:

`DASHI/Biology/DrosophilaSymbolicInterfaceLearningRegression.agda`

Create one static contract:

`scripts/check_drosophila_symbolic_interface_learning.py`

Wire the two Agda modules into `DASHI/Biology/AnimalexicEverything.agda`.

No new general planner, no duplicate decision ontology, no duplicate memory ontology, and no attempt in this tranche to build a full executable fly simulator.

## Verification boundary

Source integration, static-contract success, Agda typechecking, executable simulation, and empirical reproduction are separate statuses. The branch may not claim any later status without an actual receipt for it.
