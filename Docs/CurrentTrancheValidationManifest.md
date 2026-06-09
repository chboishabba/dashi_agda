# Current Tranche Validation Manifest

Date: `2026-05-19`
Owner: `bounded validation-manifest worker`
Status: `reproducibility manifest; non-promoting`

This manifest records the bounded validation surface for the current tranche.
It is documentation only: validation evidence is not external authority, does
not construct governance tokens, and does not promote terminal, Clay, W3, W4,
W5, or any external authority claim.

Authoritative status for this tranche:

- `laneDimension` has internal promotion status only. The promotion is a local
  route fact, not schema/test authority and not an external authority token.
- G6 is validated on the tracked route only. The old full `LaneOperator` route
  is not promoted by this manifest.
- W9 is scoped to the pressure/MDL-bounded route. This manifest does not widen
  it into unscoped closure or external authority.
- GR remains candidate-only finite-r/curvature-sidecar status. It is not sourced
  GR, Schwarzschild, continuum closure, or terminal unification.
- Terminal, Clay, W3, W4, W5, and external authority status remain fail-closed.
- Pytest status is targeted pytest only. Full pytest status is not asserted here.

## Commands

Run from the repository root.

| Surface | Command | Expected boundary |
|---|---|---|
| Whole import surface | `agda -i . DASHI/Everything.agda` | Typechecks the current aggregate imports only. It does not promote any authority-gated claim. |
| Moonshine lane receipt surface | `agda -i . DASHI/Physics/Moonshine/DASHIPrimeLaneVOATypeReceipt.agda` | Typechecks the candidate Moonshine receipt route. It does not prove terminal unification or external authority. |
| Moonshine equivalence closure surface | `agda -i . DASHI/Physics/Moonshine/DASHIPrimeLaneEquivClosureReceiptSurface.agda` | Typechecks the current `DASHIPrimeLaneEquiv` closure boundary only. It does not promote downstream physics claims. |
| W9 Lyapunov adapter surface | `agda -i . DASHI/Physics/Closure/DASHIPhysicsClosureW9LyapunovAdapterReceipt.agda` | Typechecks the scoped pressure/MDL-bounded W9 adapter receipt surface only. It does not promote unscoped closure or external authority. |
| G6 tracked/Kostant surface | `agda -i . DASHI/Physics/Closure/G6CrossLaneCommutingTheoremFromKostant.agda` | Typechecks the tracked G6 route through its current receipt surface. It does not promote the old full `LaneOperator` route. |
| GR candidate surface | `agda -i . DASHI/Physics/Closure/GRDiscreteRicciCandidateFromCurvature.agda` | Typechecks candidate finite-r/curvature-sidecar status only. It does not prove sourced GR, Schwarzschild, or continuum closure. |
| Light transport fibre closure | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/LightTransportFibreClosure.agda` | Typechecks the receipt-gated light transport closure vocabulary only. It does not prove global exact `O(1)` rendering or validate a renderer. |
| Quantum path fibre observation quotient | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/QuantumPathFibreObservationQuotient.agda` | Typechecks the quantum path-fibre quotient vocabulary only. It does not prove QED completeness, retrocausality, hidden classical paths, measurement collapse, or renderer `O(1)`. |
| Quantum path/light transport promotion-gated discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/QuantumPathLightTransportAnalogyDischarge.agda` | Typechecks the promotion-gated bridge between quantum path fibres and renderer light transport. The canonical state records promotion intent but still requires compiler, error-bound, material, visibility, residual, side-information, runtime, and empirical receipts before promotion. |
| Stationary-phase mirror/grating toy receipt | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/StationaryPhaseMirrorGratingToyReceipt.agda` | Typechecks the first inhabitable compiler/error/mask/residual subset for a mirror/grating toy lane. It does not promote full renderer, QED-backed, runtime, material, side-information, or empirical conformance claims. |
| Triadic video codec quotient | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Combinatorics/TriadicVideoCodecObservationQuotient.agda` | Typechecks the residual/reuse/side-info quotient vocabulary only. It does not promote a production codec or benchmark-only claim. |
| Light/codec analogy discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/LightCodecTransportDischarge.agda` | Typechecks the analogy-only bridge between light closure and codec reuse. It does not identify codec compression with light physics. |
| LES/GLES world transport bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Computation/LESGLESWorldTransportBridge.agda` | Typechecks the high-fidelity simulation -> LES/invariant quotient -> fast GLES runner -> conformance residual surface only. It does not prove physical exactness, global `O(1)` world update, or empirical conformance without receipts. |
| Cell communication physiology bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/CellDifferentiationCommunicationBridge.agda` | Typechecks the bounded cell differentiation / communication / physiology surface only. It does not promote disease causation, cell-fate prediction, full development recovery, or biology closure. |
| Protein/hormone chemistry-cell bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/ProteinHormoneChemistryCellBridge.agda` | Typechecks the chemistry-to-protein/hormone/cell observation surface only. It does not promote disease causation, full protein folding, cell-fate prediction, hormone-to-behaviour closure, or chemistry-to-biology closure. |
| Embodied motor multisensory bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/EmbodiedMotorMultisensoryBridge.agda` | Typechecks the bounded motor, pain-behaviour, proprioception, vestibular, and multisensory surface only. It does not promote intent recovery, pain qualia identity, full motor policy, or sensor-fusion closure. |
| Cross-species ontology translation bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/CrossSpeciesOntologyTranslationBridge.agda` | Typechecks the Animalexic/WikiSpecies translation surface only. It does not promote qualia identity, species isomorphism, anthropomorphic projection, or context-free translation. |
| BioAnimalexic stack discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/BioAnimalexicStackDischarge.agda` | Typechecks the aggregate non-promoting BioAnimalexic stack discharge over the three biology bridges. It does not prove full biology closure or a species-universal dictionary. |
| Physics/chemistry/biology/DNA unification discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/PhysicsChemistryBiologyDNAUnificationDischarge.agda` | Typechecks the aggregate cross-scale connection surface only. It does not promote physics-to-biology derivation, finished chemistry, full protein folding, hormone-to-behaviour closure, DNA-to-meaning, disease causation, or full biology closure. |
| Persistent computation motif surface | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Computation/PersistentTransportMotifs.agda` | Typechecks the program/machine execution motif vocabulary only. It does not prove compiler optimality, source-level semantic equivalence, hardware closure, or trace-to-source recovery. |
| Wikidata/Wikipedia semantic join layer | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Ontology/WikidataAnimalSemanticJoinLayer.agda` | Typechecks the public semantic review join for Animalexic candidates only. It does not create edit authority, truth authority, blind-edit authority, qualia identity, or anthropomorphic promotion. |
| Aggregate bidirectional translation discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/AggregateBidirectionalTranslationDischarge.agda` | Typechecks the human/dog/octopus/alien/renderer/machine bidi transport discharge only. It does not promote a universal translator, zero-defect isomorphism, qualia identity, or runtime optimizer. |
| Evolutionary transport MDL bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/EvolutionaryTransportMDLBridge.agda` | Typechecks the bounded evolutionary conserved-transport vocabulary only. It does not prove biology inevitability, abiogenesis, origin-of-life closure, or explicit MDL optimization. |
| Multi-observer science quotient | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Reasoning/MultiObserverScienceQuotient.agda` | Typechecks the observer quotient/fusion vocabulary only. It does not prove universal determinism, hidden variables, truth closure, peer-review infallibility, or latent recovery. |
| Free-will admissible branch PNF | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Reasoning/FreeWillAdmissibleBranchPNF.agda` | Typechecks observer-local branch navigation and PNF/population fusion only. It does not prove metaphysical free will, determinism, intent recovery, fantasy promotion, or complete branch enumeration. |
| Inverse bidirectional culture operators | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Culture/InverseBidirectionalCultureOperators.agda` | Typechecks culture/art/reading operators and bounded style quotients only. It does not provide clinical diagnosis, WAIS interpretation authority, culture determinism, qualia recovery, or aesthetic truth. |
| Observer/culture/evolution thread discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/ObserverCultureEvolutionThreadDischarge.agda` | Typechecks the aggregate thread-tail discharge over the four new surfaces only. It does not promote any of their blocked claims. |
| Operator invariant equivalence | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Reasoning/OperatorInvariantEquivalence.agda` | Typechecks the cross-domain operator/topology equivalence vocabulary only. It does not promote global ontology, substance identity, untyped exact equivalence, or universal reducibility. |
| Metaphor alignment and misunderstanding | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Reasoning/MetaphorAlignmentMisunderstanding.agda` | Typechecks the observer-context communication alignment vocabulary only. It does not guarantee perfect understanding, qualia recovery, universal exact translation, or context-free communication optimality. |
| Semantic operator alignment discharge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/SemanticOperatorAlignmentDischarge.agda` | Typechecks the aggregate semantic/operator-alignment discharge only. It does not promote any blocked operator-equivalence or communication claim. |
| Knot/weave topology culture bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Culture/KnotWeaveTopologyCultureBridge.agda` | Typechecks the theorem-thin knot/weave/braid semantic-topological carrier bridge only. It does not promote cultural universals, identity or qualia closure, context-free equivalence, or authority. |
| Fibre pressure metric bridge | `agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Metric/FibrePressureMetricBridge.agda` | Typechecks the theorem-thin pressure/residual metric bridge only. It does not calibrate thresholds, prove metric completeness for every domain, construct a global optimizer, or promote transport claims. |
| W4/W5 accepted-packet boundary tests | `pytest -q tests/test_w4w5_fail_closed_authority_packets.py` | Runs the targeted fail-closed W4/W5 packet tests only. Passing tests do not construct accepted DY convention authority or W5 promotion. |
| W4/W5 CT18 preflight tests | `pytest -q tests/test_w4w5_pdf_lhapdf_intake_preflight.py` | Runs the targeted CT18/preflight tests only. Passing tests preserve the provider/preflight boundary and do not promote W4/W5. |

## Out Of Scope

- Do not treat this manifest as CI policy or as a request to add broad CI.
- Do not treat schemas, tests, or this manifest as authority for promotion.
- Do not infer Clay, W3, W4, W5, GRQFT, sourced GR, Schwarzschild, continuum,
  or terminal unification promotion from these checks.
- If full `pytest` collection has unrelated collection issues in the current
  worktree, use the targeted pytest commands above for this tranche.
- If `DASHI/Everything.agda` stops in an unrelated dirty-tree surface, use the
  focused tranche commands above for the biology, light-transport, and codec
  surfaces and do not infer failure of those focused surfaces from the
  unrelated aggregate blocker.
