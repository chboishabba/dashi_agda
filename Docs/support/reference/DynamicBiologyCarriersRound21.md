# Dynamic biology carriers and graph-generating control — Round 21

Round 21 implements the outstanding surfaces in the four attached biology/helix roadmaps. It builds on Round 20 rather than replacing it.

The central refinement is:

```text
persistent carrier + context + changing interaction graph + hierarchical goal
    -> coupled local operators
    -> graph/state trajectory
    -> consumer-visible morphology
```

A biological state is therefore not identified with DNA, current morphology, voltage, transcriptome, or a fixed interaction graph.

## Persistent state carriers and prion boundary

`PersistentCarrierTemplatingExact` instantiates the existing `AgenticMaterialsControlCore.TemplatedPropagation` surface with a two-state conformational carrier. A prion-like template converts normal conformation to prion conformation while leaving genome state unchanged. The same module proves that equal genome observation does not reconstruct the persistent fine carrier.

It deliberately reuses the existing `PrionLikeBoundary`: templated self-amplification alone is not promoted to agency because target-relative defect and corrective feedback are absent.

Primary source:

Stanley B. Prusiner, *Novel proteinaceous infectious particles cause scrapie*, Science 216 (1982), 136–144. DOI `10.1126/science.6801762`.

`CrossCarrierTemplatingFamilyExact` adds a substrate-neutral `TemplateSystem` and finite instances for sequence, protein conformation, epigenetic state, bioelectric pattern and morphology repair. This is theorem reuse across typed mechanisms, not a claim that all five mechanisms are physically identical.

## Dynamic graph morphogenesis

`DynamicTissueGraphRewriteExact` makes the tissue graph itself part of the state. Its action language can:

- create/delete a cell;
- create/delete a junction;
- displace a cell state;
- differentiate a cell;
- attach tissue to the larger body.

The finite regression proves that division changes the vertex carrier and connection changes the edge carrier. A compound action simultaneously performs state, edge, node and displacement rewrites. `repairIntegratedGraph` rewrites an arbitrary finite state into one satisfying the declared integrated-organ constraint.

`DynamicTopologyFutureDefectExact` then makes the PNF consequence explicit. Two states have the same present morphology but different hidden junction topology. Under the same admissible signal their future morphologies differ. Therefore morphology with topology forgotten is not a dynamically safe consumer quotient.

The legacy repository type `TerminalisationDefect` is used only as the bare future-divergence witness; no unreopenability theorem is claimed.

## Hierarchical goal delegation

`HierarchicalGoalConstraintCompilerExact` formalizes the goal ladder

```text
organism -> organ -> tissue -> cell -> molecular
```

as proof-bearing refinement relations, rather than deterministic decoding. The same `leftHand` organ goal has distinct admissible tissue refinements, and the same `digitField` tissue goal has distinct admissible cell policies.

This is the formal anti-micromanagement result: a higher-level goal supplies a feasible lower-level set, not a unique microscopic trajectory.

Source-facing motivation:

Michael Levin and Christopher J. Martyniuk, *The bioelectric code: An ancient computational medium for dynamic control of growth and form*, Biosystems 164 (2018), 76–93. DOI `10.1016/j.biosystems.2017.08.009`.

## Error descent, basin recovery and policy degeneracy

`GoalErrorDescentControllerExact` gives an exact finite target-defect system. Every positive natural-number defect decreases strictly by one, zero is fixed, and two different perturbation severities recover to the same target. Distinct local policies also reach the target from different initial defects.

This is a finite descent/basin certificate only. It does not assert that biological morphogenesis globally minimizes one scalar energy.

Primary source:

Nikolai Bessonov, Michael Levin, Nadya Morozova, Natalia Reinberg, Alen Tosenberger, Vitaly Volpert, *Target morphology and cell memory: a model of regenerative pattern formation*, Neural Regeneration Research 10 (2015), 1901–1905. DOI `10.4103/1673-5374.165216`.

`GraphGeneratingGoalControllerExact` composes the previously separate ingredients into the requested closed-loop factorization:

```text
Sense -> Goal -> Error -> Policy -> LocalAction -> GraphRewrite
```

For the finite integrated-hand target, one closed-loop step fills exactly the missing junction/differentiation/attachment constraints, proves that the resulting graph satisfies the integrated-organ target, and fixes states already satisfying that target.

## Coupled developmental operator stack

`CoupledDevelopmentalOperatorStackExact` implements a finite state with genomic, epigenetic, transcript, protein, metabolic, bioelectric, mechanical, proliferative, migration, repair and phenotype coordinates.

The full update explicitly factors through transcription, translation, metabolism, bioelectric update, mechanics, proliferation, migration, repair and morphology observation.

It proves both sides of the causal-order question:

- writes to independent repair/phenotype coordinates commute;
- transcription and translation do not commute on a concrete witness;
- bioelectric and mechanical updates do not commute on a concrete witness.

Thus the operator algebra is not treated as a feed-forward compiler.

## Biological measurements are quotients

`DevelopmentalMeasurementQuotientExact` gives two cells with the same genome, transcript observation and present phenotype but different hidden chromatin state. The same developmental action produces different future phenotype.

This is a concrete theorem that genome/transcript/present-phenotype equality does not imply developmental future equivalence.

## Context-dependent hierarchical-to-physical representation

`ContextDependentPadicPhysicalMapExact` strengthens the Round-20 p-adic adapter. The physical map is now explicitly

```text
Psi : Context -> HierarchicalAddress -> PhysicalParameter
```

not a context-free address decoder. The same fine address maps to different downstream physical parameters in different contexts, while two fine addresses sharing one coarse prefix still select different parameters inside one context.

This preserves the intended boundary: p-adic/ultrametric structure is hierarchical symbolic/history geometry, not a claim that molecular physics is intrinsically p-adic.

## Multiscale identity and “our hand”

`MultiscaleSelfBoundaryExact` models an effective self boundary at cell, tissue and organism scales. A generic hand-shaped candidate and an organism-integrated hand share the same shape observation while differing in attachment and self-boundary membership.

The theorem `shapeAloneDoesNotDetermineOurHand` makes ownership relational rather than another shape coordinate.

Source:

Michael Levin, *Darwin's agential materials: evolutionary implications of multiscale competency in developmental biology*, Cellular and Molecular Life Sciences 80 (2023), 142. DOI `10.1007/s00018-023-04790-z`.

## DNA physical helix and dihedral symmetry

`DNAHelixDihedralExact` adds the missing DNA-specific helical layer while keeping the native 4-adic sequence carrier separate from the 369 scaffold.

The finite `Phase4` skeleton has rotation `r`, inverse rotation, reflection `s`, and proves the dihedral conjugation law

```text
s (r (s p)) = r^-1 p.
```

A `HelixSite` carries DNA base, cyclic phase, axial index and strand. `pairedSite` combines Watson–Crick complement, a half-turn phase offset and strand swap. It is involutive and commutes with helical advancement. The module also reuses the existing exact UV result that complement preserves U and flips the V coordinate.

Primary source:

J. D. Watson and F. H. C. Crick, *Molecular Structure of Nucleic Acids: A Structure for Deoxyribose Nucleic Acid*, Nature 171 (1953), 737–738. DOI `10.1038/171737a0`.

`DNASequenceHelixPositionExact` makes the requested position-to-phase map explicit. A finite cyclic sequence position advances exactly when helical phase rotates, and the positioned-base embedding commutes with helix advancement. Axial history remains a distinct coordinate from cyclic phase.

The finite four-phase period is an algebraic regression, not a claim that B-DNA has four bases per physical turn.

## Exact 27-cell C3 cubical character carrier

`C3CubeFourier27Exact` defines the exact product carrier `C3^3`, componentwise addition, and a product character indexed by another `C3^3`. It proves the character homomorphism law.

The module also gives an explicit 27-constructor `CubeCell27` and exact two-way maps

```text
CubeCell27 <-> C3^3
```

with both round trips proved. Since `CharacterIndex = C3^3`, the same exact 27-element carrier indexes the product characters.

This is the finite group-theoretic 27-cell/27-character theorem surface. It deliberately does **not** claim a complex-valued Fourier inversion theorem.

## What Round 21 closes

The four attachments asked for the missing bridges between persistent non-genomic state, graph-changing morphogenesis, hierarchical agentic control, measurement quotients, context-dependent hierarchical representations, physical DNA helix geometry and the 27-cell spectral scaffold. Those bridges are now theorem-bearing modules in one cumulative aggregate:

`DASHI/EverythingDynamicBiologyRound21.agda`.

Fail-closed local checker:

`scripts/check_dynamic_biology_round21.sh`.

The checker cascades Round 20, rejects postulates/holes/unsafe trust escapes in Round 21, verifies load-bearing theorem names and source DOI metadata, and invokes Agda only when an executable is available.

## Remaining authority boundary

Round 21 still does not claim:

- a calibrated stochastic model in which life emerges with probability approaching one;
- the full England dissipative-adaptation or self-replication inequalities;
- a complete reaction-network / Nernst–Planck / mechanochemical developmental PDE;
- a quantitative basin-volume theorem for a real organ;
- calibrated B-DNA twist, pitch or strand geometry;
- complex Fourier inversion/orthogonality on `C3^3`;
- that prion, epigenetic, bioelectric and morphological templating have the same physical mechanism;
- that p-adic or 369 coordinates are literal biological substrate.

Those are now analytic/calibration frontiers rather than missing architecture.
