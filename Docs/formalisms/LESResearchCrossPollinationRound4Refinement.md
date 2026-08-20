# Cross-pollination round 4: consumer-guided reopenable refinement

Round 3 extracted the common reopenable consumer/intervention kernel. Round 4 turns that static commonality into an adaptive theorem loop:

```text
abstract -> predict/act cheaply -> challenge -> separating discrepancy/counterexample
         -> refine only the affected abstraction fibre
         -> selectively reopen assumption-dependent descendants -> re-certify
```

## Exact additions

- `DASHI.Core.ConsumerGuidedReopenableRefinementExact`
  - strict projection refinement with an explicit forgetful map;
  - constructive witness that one old fibre is split by the new projection;
  - consumer-guided refinement produces an old-projection descent defect;
  - finite action-trace separation refutes bounded future equivalence at that trace length;
  - one-step witness proves depth-0 equality and refutes depth-1 equivalence;
  - context/scenario-robust bounded equivalence;
  - approximate descent composed with a consumer decision margin;
  - local refinement can preserve all unaffected old fibres.

- `DASHI.Core.DualEffectAdaptiveFidelityExact`
  - world-only, information-only and dual-effect actions;
  - information-only actions prove exact world-state identity while still producing evidence;
  - low/high fidelity evaluator with an application-supplied discrepancy relation;
  - terminal decision stability turns bounded discrepancy into exact decision agreement;
  - high-fidelity allocation remains an explicit policy rather than an invented scalar utility.

- `DASHI.Core.AssumptionIndexedReopeningExact`
  - validity is represented as `assumptions hold -> claim valid`;
  - alternative sufficient support routes are first class;
  - a surviving route constructively refutes global invalidation;
  - evidence independence is defined by absence of a shared provenance root;
  - a shared root constructively refutes an independence claim;
  - reopening can be consumer indexed.

- `DASHI.Core.TypedTemporalExperimentExact`
  - Allen's thirteen interval relations;
  - observed/inferred/continuous/discrete/intervention event kinds;
  - experiments are bounded action traces;
  - bounded experiment equivalence reuses the existing finite-depth refinement theorem;
  - experiment-language exhaustion reuses `BoundedEnumeration`.

## Animalexic adapter

`DASHI.Biology.AnimalexicFormalSystemExact` implements the supplied architecture as typed surfaces for:

- persistent `geometry x pose x vocal x facial x attention x environment x history x interpretation` state;
- provenance-bearing observations and candidate promotion;
- surfels with observed anchor distinct from fused centroid;
- distinct-frame support;
- exact spatial-hash membership and non-periodic-boundary witnesses;
- weighted local geometry graphs;
- promotion margins and low-margin defect localization;
- connected ascended cores plus plateau shells;
- incremental factor/dependency state without forcing every factor to be probabilistic;
- active/reopenable/refuted semantic hypotheses;
- explicit individual animal models;
- dual-effect communication actions;
- interventional hypothesis separation;
- lineage-based evidence independence;
- the full observation -> geometry -> behaviour -> communication -> semantics authority boundary.

`AnimalexicRegression` supplies a concrete finite countermodel: two states have the same passive observation, but one `probe` action yields distinguishable responses. Agda therefore proves depth-0 equivalence while refuting depth-1 equivalence. A second finite witness shows that a camera failure hits the visual route while an acoustic route survives, so global invalidation is impossible.

## Source metadata

`AnimalexicSourceAtlas` records bounded source relationships, including:

- Keller et al., *Real-time 3D Reconstruction in Dynamic Scenes using Point-based Fusion*, DOI `10.1109/3DV.2013.9`;
- Whelan et al., *ElasticFusion: Dense SLAM Without A Pose Graph*, DOI `10.15607/RSS.2015.XI.001`;
- Newcombe, Fox & Seitz, *DynamicFusion*, DOI `10.1109/CVPR.2015.7298631`;
- Niessner et al., *Real-time 3D Reconstruction at Scale using Voxel Hashing*, DOI `10.1145/2508363.2508374`;
- Mathis et al., *DeepLabCut*, DOI `10.1038/s41593-018-0209-y`;
- Pereira et al., *SLEAP*, DOI `10.1038/s41592-022-01426-1`;
- Kim et al., *Multiple Hypothesis Tracking Revisited*, DOI `10.1109/ICCV.2015.533`;
- Allen, *Maintaining Knowledge about Temporal Intervals*, DOI `10.1145/182.358434`;
- Weinreb et al., *Keypoint-MoSeq*, DOI `10.1038/s41592-024-02318-2`;
- Wathan et al., *EquiFACS*, DOI `10.1371/journal.pone.0131738`;
- Teglas et al., *Dogs' Gaze Following Is Tuned to Human Communicative Signals*, DOI `10.1016/j.cub.2011.12.018`.

Rabbani region growing and Dellaert's factor-graph tutorial are retained with atlas-local `noDOIRecordedByAtlas`. No citation imports theorem authority.

## Cross-project result

The reusable loop is now:

```text
consumer-safe abstraction
-> bounded prediction/search
-> information or world action
-> discrepancy / separating witness
-> local quotient refinement
-> support-route-aware selective reopening
-> re-certification
-> next action.
```

This is stronger than a static governed transition system. It is a **consumer-guided reopenable refinement system**: abstraction is allowed to be incomplete, but the system must retain enough provenance and residual structure to refine exactly when a downstream consumer or intervention proves that the current quotient is insufficient.

The applications still own their science. A curvature defect, communicative ambiguity and nutrient residual are not the same quantity; a citation is not a proof; a behavioural cluster is not a semantic meaning; and a model result is not deployment authority.
