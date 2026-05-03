# Brain Lane Status

Declared surface level: `adjacent lane with theorem-thin local owner surfaces`,
not a local closure or brain theorem lane.

This note is the compact status surface for the brain-side lane shown on the
physics diagrams. Its purpose is to keep the roadmap truthful without
overstating what is localized in this repo.

## Current Sources Of Truth

- `Docs/PhysicsGuide.md`
- `Docs/PhysicsUnificationMap.puml`
- `Docs/PhysicsRealityRoadmap.puml`
- sibling-repo adjacent work in `../dashiBRAIN`
- archive / NotebookLM context used to justify the lane as part of the wider
  DASHI program

## Current Status

The brain-side lane is real in program scope. It is still adjacent in the
program-level sense, but it is no longer "archive only" inside
`dashi_agda`.

What is local here:

- roadmap and unification diagrams that show the lane explicitly
- claim-boundary language that marks the lane as adjacent rather than proved
- theorem-thin local owner surface in `Ontology/Brain/BrainVocabularySurface.agda`
- theorem-thin local coarse-summary surface in
  `Ontology/Brain/BrainCoarseSummarySurface.agda`
- theorem-thin local extraction/coarse-graining surface in
  `Ontology/Brain/BrainExtractionSurface.agda`
- theorem-thin local invariant surface in
  `Ontology/Brain/BrainInvariantSurface.agda`
- theorem-thin local invariant-depth surface in
  `Ontology/Brain/BrainInvariantDepth.agda`
- theorem-thin local region-automaton owner surface in
  `Ontology/Brain/BrainRegionAutomatonSurface.agda`
- theorem-thin local visual form-constant / log-polar owner surface in
  `Ontology/Brain/BrainVisualFormConstantSurface.agda`
- theorem-thin local learning/eigenbasis phase-profile owner surface in
  `Ontology/Brain/BrainLearningEigenbasisSurface.agda`
- theorem-thin local morphospace/gap-junction owner surface in
  `Ontology/Brain/BrainMorphospaceGapJunctionSurface.agda`
- theorem-thin local downstream theme-consumer law surface in
  `Ontology/Brain/BrainThemeConsumerLaws.agda`
- the local extraction/invariant/invariant-depth stack is now explicitly
  consumed from `Ontology/BrainDNA/`, not only declared in isolation
- nearby crossover interfaces on the DNA / channel side that may later become
  stronger bridge points

What is adjacent rather than local:

- most brain-specific structure, datasets, and analysis code
- current hemibrain / Drosophila-oriented work in `../dashiBRAIN`
- archive-backed design language relating brain structure to wider DASHI
  modeling

## Notebook-Confirmed Brain Themes

The NotebookLM-backed archive context confirms that the broader DASHI program
contains explicit discussion of these brain-side themes.

## Localization Matrix

| Theme | Present in notebook | Present in sibling repo | Localized in Agda here | Not yet localized |
| --- | --- | --- | --- | --- |
| Brain-region automaton mapping | yes | not directly evidenced by quick local scan | yes | no |
| Klüver form constants / log-polar V1/V2 geometry | yes | not directly evidenced by quick local scan | yes | no |
| Grokking / eigenbasis / Fourier-basis phase transition | yes | not directly evidenced by quick local scan | yes | no |
| Gap junctions / morphospace error correction | yes | not directly evidenced by quick local scan | yes | no |

Notes:

- `present in notebook` is backed by the current NotebookLM notebook and source
  titles already checked in this repo workflow.
- `present in sibling repo` is conservative here: a quick thematic scan of
  `../dashiBRAIN` did not directly surface these exact themes by name.
- `localized in Agda here` is currently `no` for all four because no dedicated
  theorem owner modules existed at the time the matrix was introduced. It is
  now `yes` for the three themes listed above that have landed local owner
  modules.

### 1. Brain-region automaton mapping

- notebook/archive context: yes
- relevant source titles:
  - `Explain system transition.pdf`
  - `DASHI - Dashi and DNA Quantum Dynamics.pdf`
- local Agda status here:
  - localized as `Ontology/Brain/BrainRegionAutomatonSurface.agda`
  - still theorem-thin and static rather than a richer routing/control theorem
- blocker:
  - still lacks a physically informative downstream consumer or richer local
    control/routing semantics

### 2. Klüver form constants / hallucination geometry / log-polar V1/V2

- notebook/archive context: yes
- relevant source titles:
  - `Klüver’s Form Constants.pdf`
  - `DASHI - Dashi and DNA Quantum Dynamics.pdf`
- local Agda status here:
  - localized as `Ontology/Brain/BrainVisualFormConstantSurface.agda`
  - still theorem-thin and geometric rather than a richer visual-cortex
    dynamics lane
- blocker:
  - still lacks a stronger downstream consumer and does not prove unique
    biological realization of the packaged geometries

### 3. Grokking / eigenbasis / Fourier-basis phase transition

- notebook/archive context: yes
- relevant source titles:
  - `DASHI learner context.pdf`
  - `DASHI - Interference and Learning Demo.pdf`
  - `CONTEXT.md`
- local Agda status here:
  - localized as `Ontology/Brain/BrainLearningEigenbasisSurface.agda`
  - still theorem-thin static phase profiling rather than a dynamic learning
    theorem lane
- blocker:
  - still lacks optimization/gradient/learning dynamics and stronger
    downstream consumers

### 4. Gap junctions / cognitive glue / morphospace error correction

- notebook/archive context: yes
- relevant source titles:
  - `Huawei patent explanation.pdf`
  - `DASHI - Dashi and DNA Quantum Dynamics.pdf`
- local Agda status here:
  - localized as `Ontology/Brain/BrainMorphospaceGapJunctionSurface.agda`
  - still theorem-thin packaging rather than a richer tissue/channel dynamics
    lane
- blocker:
  - still lacks multiscale biological channel semantics or recursive
    tissue-level recovery dynamics

## Current Implementation Lanes

The current bounded implementation ownership for the brain-side lane is:

1. `Brain-region automaton mapping`
   - target owner:
     - `Ontology/Brain/BrainRegionAutomatonSurface.agda`
   - scope:
     - bounded region/lens/motif vocabulary and exact packaging only
   - non-claim boundary:
     - no neuroscience completeness claim

2. `Klüver / log-polar visual geometry`
   - target owner:
     - `Ontology/Brain/BrainVisualFormConstantSurface.agda`
   - scope:
     - bounded form-constant / log-polar / open-loop geometry packaging only
   - non-claim boundary:
     - no full V1/V2 recovery claim

3. `Grokking / eigenbasis phase transition`
   - target owner:
     - `Ontology/Brain/BrainLearningEigenbasisSurface.agda`
   - scope:
     - bounded representation-phase-transition packaging only
   - non-claim boundary:
     - no global learning theory claim

4. `Gap junction / morphospace coherence`
   - target owner:
     - `Ontology/Brain/BrainMorphospaceGapJunctionSurface.agda`
   - scope:
     - bounded morphospace/gap-junction/error-correction packaging only
   - non-claim boundary:
     - no biological completeness claim

## Why It Appears On The Physics Diagrams

The lane appears on the diagrams for roadmap truthfulness, not because it
currently closes physics theorems here.

It matters because:

- it exerts structural pressure on the crossover lane
- it helps explain why brain-DNA / codec / channel ideas are in scope for the
  broader program
- leaving it out would make the current local physics story look narrower and
  more self-contained than the actual archive-backed program

## Current Non-Claim Boundary

Do not read the brain-side lane as:

- local Agda closure
- current theorem evidence for physics unification
- a finished brain formalism in this repo
- evidence that the sibling-repo brain work has been absorbed here in depth

The honest reading is:

- adjacent lane with theorem-thin local packaging
- sibling-repo informed structural lane
- candidate future source of stronger formalization targets
- now connected into the local crossover/chemistry boundary through a
  theorem-thin extraction-aware connector in `Ontology/BrainDNA/`

The honest theme-by-theme reading is:

- the four brain themes above are present in archive/notebook context
- all four of them are now localized here as bounded theorem-thin owners:
  - region automaton mapping
  - visual form-constant / log-polar geometry
  - grokking / eigenbasis phase transition
  - morphospace gap-junction coherence
- none of them are yet localized here as rich dynamic or consumer-heavy
  theorem lanes

## Concrete Localization Targets Here

1. Strengthen the local brain-side invariant-depth surface beyond the current
   coarse `0/1` bounded law into richer bounded invariant semantics.
2. Extend the now-landed region automaton, visual form-constant,
   grokking/eigenbasis, and morphospace gap-junction surfaces beyond the new
   bounded theme-consumer law surface into richer local semantics.
3. Extend the now-landed extraction-aware connector depth/semantics and
   structural-consumer semantics into stronger local
   crossover semantics over DNA-side structural and chemistry summaries.
4. Keep local brain packaging explicitly adjacent/non-closure while widening
   the set of bounded formalization targets imported from `../dashiBRAIN`.
