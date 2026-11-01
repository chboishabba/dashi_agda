# Mesh Morphology Calibration and Bidirectional Seam A/B

## Scope

This tranche formalizes the boundary reached in the SeaMeInIt discussion without importing renderer heuristics into DASHI.

The system labels `human` and `ogre` are treated as genuine system outputs, but they are licensed only by a human-provided calibration containing one labelled human exemplar and one labelled ogre exemplar. The numerical observation surface is a barycentric radial-mass signature. DASHI does not add anatomical intuition such as head/feet, limb, pose, or world-axis rules.

## Modules

- `DASHI.Empirical.MeshMorphologyCalibration`
  - `BarycentricRadialMassModel`
  - `HumanCalibration`
  - explicit nearest-exemplar comparison outcomes
  - fail-closed `needs-human`
  - proof that every classification is licensed by calibration
- `DASHI.Empirical.SeamABExperiment`
  - Strategy A: solve on base, transfer to ROM
  - Strategy B: solve on ROM, transfer to base
  - both directions are first-class and mandatory in the experiment carrier
  - selection requires an explicit policy and may retain both or return to a human
- `DASHI.Empirical.MeshMorphologySeamProtocol`
  - specializes the DASHI `O,R,C,S,L,P,G,F` schema
  - joins calibrated morphology with the bidirectional seam experiment
  - promotion fails closed on unresolved morphology

## Formal boundary

Proved by construction:

1. The classifier cannot invent a third morphology label.
2. An unresolved comparison returns `needs-human`; it does not default to either label.
3. Strategy A and Strategy B have distinct typed directions.
4. An `ABExperiment` contains both results.
5. Promotion is blocked if either mesh classification remains unresolved.

Not claimed:

- that a particular radial signature or distance is scientifically optimal;
- that PCA, world axes, feet/head heuristics, or render orientation identify morphology;
- that provenance, topology, and morphology are interchangeable;
- that A or B is globally superior without an explicit metric and selection policy.

## Intended empirical adapter

A runtime adapter should:

1. calculate a radial-mass function about the mesh barycentre;
2. record one human-labelled and one ogre-labelled exemplar;
3. compare a candidate signature against both exemplars;
4. pass only the explicit comparison result into the formal classifier;
5. run and retain both seam directions and their metrics;
6. return ties or low-confidence cases to the human in the loop.
