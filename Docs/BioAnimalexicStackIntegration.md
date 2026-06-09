# BioAnimalexic Stack Integration

## Purpose

The BioAnimalexic stack extends the current bounded observation-and-transport
formalism from sensory channels into whole embodied animal interpretation.
It remains a receipt vocabulary, not a complete biology theorem.

The intended chain is:

```text
DNA
  -> regulation
  -> cell differentiation
  -> cell-cell communication
  -> tissue morphogenesis
  -> organ and sensor formation
  -> body physiology
  -> sense and connectome transport
  -> behaviour
  -> social/ecological meaning
  -> cross-species ontology translation
```

## Stack Sectors

| Sector | Role | Boundary |
| --- | --- | --- |
| genome/development | constrains regulation, lineage, tissue, and wiring | no DNA-to-meaning closure |
| cell communication | ligand, ion, gap, synaptic, hormone, immune, and mechanical channels | no full cell-fate prediction |
| metabolism/circulation | ATP, oxygen, glucose, CO2, hormones, immune signals, heat | no disease-causation claim |
| motor/body state | motor plans, muscles, posture, gait, pain, proprioception, vestibular state | no intent or pain-qualia recovery |
| multisensory integration | vision, hearing, smell, touch, pain, proprioception, vestibular, interoception, magnetoreception | no sensor-fusion closure |
| memory/social/ecology | learning, social roles, habitat, weather, resources, threat, repair | no context-free meaning |
| ontology translation | species-native ontology to another species or Wikidata surface | no qualia identity or isomorphism claim |

## Promotion Discipline

The local promotion target is only:

```text
persistent constrained latent body-social state
```

not:

```text
subjective qualia
complete disease model
complete cell biology
species-universal dictionary
context-free cross-species semantics
```

Cross-species translation is treated as partial transport:

```text
Ontology_x -> Ontology_y -> Ontology_x'
```

where the projection defect is explicit.  Zero defect would be an isomorphism;
positive defect is analogy or partial translation only.

## Current Implementation Status

The current tranche inhabits the following bridge modules:

```text
DASHI.Biology.CellDifferentiationCommunicationBridge
DASHI.Biology.EmbodiedMotorMultisensoryBridge
DASHI.Biology.CrossSpeciesOntologyTranslationBridge
DASHI.Biology.BioAnimalexicStackDischarge
```

The aggregate discharge imports the individual surfaces and records the thread
as covered by a typed, non-promoting biology/Animalexic stack.  Focused Agda
validation passes for all four modules.

## Remaining Roadmap

The local BioAnimalexic formalism has no open implementation item in this
tranche.  Remaining work is downstream:

1. Add empirical receipt adapters when real datasets or annotation protocols
   exist for cell physiology, motor/body state, social ecology, or translation.
2. Connect Animalexic observation packets to a runtime ITIR/PNF consumer rather
   than only Agda toy witnesses.
3. Add species-specific ontology packs for concrete targets such as dog, bird,
   octopus, frog, machine, or human comparison surfaces.  The first bounded
   public semantic join surface now lives in
   `DASHI.Ontology.WikidataAnimalSemanticJoinLayer`.
4. Decide whether WikiSpecies/Wikidata integration should become a live runtime
   importer or remain a static receipt vocabulary.  The current Agda surface is
   review-only and has no edit or truth authority.
5. Restore a whole-repo `DASHI/Everything.agda` aggregate pass after the
   unrelated Yang-Mills receipt blocker is resolved.

None of those are prerequisites for the typed BioAnimalexic discharge itself.

## Thread Tail Extension

The refreshed tail also adds a broader bidirectional transport rule:

```text
human ontology
  <-> dog ontology
  <-> octopus ontology
  <-> alien ontology
  <-> renderer ontology
  <-> machine ontology
```

That extension is now represented outside the biology stack by:

```text
DASHI.Computation.PersistentTransportMotifs
DASHI.Ontology.WikidataAnimalSemanticJoinLayer
DASHI.Interop.AggregateBidirectionalTranslationDischarge
```

The aggregate discharge imports the computation motif surface and public
semantic join certificate, so the local story is linked: Animalexic provides
the situated observation candidate, public ontology provides review context,
computation/machine domains provide the execution/fibre-motif analogue, and
bidirectional transport keeps projection defects explicit.
