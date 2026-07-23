# DASHI controlled ternary cognitive formalism

This directory models a physical cognitive subsystem as a controlled ternary language machine. It does not identify the brain with a PDA, manifold, chemical field, electromagnetic field, or diffusion model separately. Those are differently typed layers connected by explicit projections and coupling maps. The formal lane keeps three claims separate:

```text
structural compatibility
empirical establishment
causal explanation
```

## Master object

`DashiCognitiveSystem.agda` defines the concrete carrier:

- hidden physical/cognitive state and observable quotient;
- exogenous/endogenous control and stack-obligation alphabet;
- ternary semantic and stack transitions;
- contextual admissibility and signed margin;
- grammar/model/distortion code lengths;
- coarse-graining and involution stability.

It directly reuses:

- `DASHI.Algebra.BalancedTernary.Trit`;
- `DASHI.Combinatorics.PDA_MDL.PDA`;
- `DASHI.Combinatorics.PDA_MDL.Prelude.CodeLength`;
- `DASHI.Cognition.ResidualPhaseGeometry.Projection/Fibre`.

A derivation is accepted only when every prefix remains admissible, the terminal obligation stack closes, and the terminal margin commits positively. The master system retains depth-to-failure, feasible branching, finite MDL difference, and stack depth as distinct observables.

## Ternary and 3-adic structure

`TernaryDerivationAddress.agda` maps balanced trits to finite base-three addresses with the earliest token least significant, matching a p-adic coarse-to-fine convention.

`TernaryDerivationUltrametric.agda` defines longest-common-prefix distance and proves identity, symmetry, and the strong triangle inequality using the repository `Ultrametric` interface and the proof pattern of `MonsterUltrametric15`.

## Phase-enriched zero

`PhaseEnrichedTrit.agda` places a finite weight-and-phase carrier above the public balanced trit. The quotient selects `neg` or `pos` only when that polarity is uniquely dominant. Neutral dominance, ties, balanced opposition, and unresolved phase relations project to `BT.zero`.

The formal distinction is:

```text
BT.zero                         one public constructor
observeTrit^-1(BT.zero)         a populated hidden fibre
```

Exact hidden profiles with different cyclic phase coordinates project to the same public zero. This supplies a phase-bearing zero fibre, but not yet a complex Hilbert space, amplitude norm, Born rule, or physical neural superposition.

## The common 3-6-9 quotient

`Base369ZeroFibre.agda` exposes exact product coordinates for the existing cyclic carriers:

```text
HexTruth    ~= TriTruth x Orientation
NonaryTruth ~= TriTruth x TriTruth
```

with proved round trips. The common quotient is:

```text
q6 : HexTruth -> TriTruth
q9 : NonaryTruth -> TriTruth

HexTruth -> TriTruth <- NonaryTruth
```

The fibres over `tri-mid` contain exactly two and three representatives. The pullback `6 x_3 9` contains eighteen states, and its public-zero sector contains six.

`IdEgoSuperego369.agda` gives these product carriers role types without claiming literal psychoanalytic neuroanatomy:

- `3`: immediate or pre-reflexive valuation (`IdCarrier`);
- `6`: valuation plus binary observer/orientation split (`EgoCarrier`);
- `9`: felt/local valuation paired with desired, compelled, or normative valuation (`SuperegoCarrier`).

Categorical identity remains separately named `identityMorphism`. The self fixture keeps felt, desired, and compelled values distinct and computes their exact mismatch count.

## Local zero, holonomy, contextuality, and nonseparability

`ZeroFibreContextuality.agda` formalises the Minesweeper-like claim that visible zero can be locally informative rather than empty. Every node projects to `BT.zero`, while hidden binary orientations are transported around an odd cycle. Every edge admits a local section, but the three edge constraints admit no global section. Three local flips also produce nontrivial loop holonomy.

The construction is inspired by Samson Abramsky and Adam Brandenburger, *The sheaf-theoretic structure of non-locality and contextuality*, DOI `10.1088/1367-2630/13/11/113036`.

`Monoidal369Nonseparability.agda` defines a non-rectangular joint support on `ZeroFibre6 x ZeroFibre9` and proves it cannot factor into independent left and right predicates. This is exact structural nonseparability. It does not yet establish complex tensor entanglement, no-signalling, or a Bell violation.

## Recursive fibres and literal tetration

`RecursiveFibreTower.agda` separates two recurrences:

1. recursive phase refinement, which adds hidden phase coordinates while preserving a lower observable;
2. iterated ternary-valued function spaces.

The literal function tower is:

```text
PredicateLevel 0       = Unit
PredicateLevel (n + 1) = PredicateLevel n -> TriTruth
```

For a finite level of size `a(n)`, the next level has size:

```text
a(0) = 1
a(n + 1) = 3 ^ a(n)
```

so the cardinality sequence is genuine base-three tetration:

```text
1, 3, 27, 3^27, ...
```

The module constructs lossless codes for the first two levels:

- level one is one trit;
- level two is three trits and therefore has `3^3 = 27` codes.

This is distinct from the self-transformer recurrence `X(n+1)=X(n)->X(n)`, whose finite sizes obey `a(n+1)=a(n)^a(n)`.

The same module defines an inverse-system interface and a canonical compatible zero family across every recursive phase-refinement level.

## Fibre/braid reasoning and the recursive self

`FibreBraidReasoning.agda` represents reasoning through latent, observed, desired, and compelled ternary coordinates. Auxiliary fibres act through the existing associative `Base369.triXor` transport. A concrete witness lowers global mismatch defect from two to one.

This is a goal-directed fibre step rather than a completed observer-of-observer chain. The stable self is a compatible class across projections; the Ego mediates felt, desired, and compelled coordinates while retaining the pre-reflexive carrier.

## Quotients, multiple drafts, and category

`MultipleDraftsQuotient.agda` gives distinct Orwellian and Stalinesque hidden histories that map to the same public report and action but to different detailed traces. Their distinction disappears only after the chosen quotient.

`CognitiveProjectionCategory.agda` constructs a free category generated by physical evolution, physical realisation, guarded transition, derivation readout, class quotient, coarse-graining, involution, observation, visual generation, and visual deformation. Identity and associativity are proved recursively using `DASHI.Core.ProjectionCategory`.

## Identity and vacuum

`CognitiveVacuumClassBoundary.agda` proves that an arbitrary stable observed class need not be a vacuum.

`IdentityVacuumClosure.agda` supplies the stronger principle. `IdentityNeutralDefectLaw` requires:

```text
stable identity class
coarse-graining identity
involution identity
totalDefect(candidate) = neutralFloor + residualExcess(candidate)
residualExcess(identity) = 0
```

Since residual excess is non-negative, global defect minimality is derived rather than separately assumed. The resulting theorem is:

```text
identityNeutralityImpliesVacuum
```

A second fixture proves that the neutral floor may be non-zero: the identity class has defect `2`, another class has defect `3`, and the identity is still the vacuum. Identity neutrality therefore means no additional admissibility defect, not necessarily zero measured energy.

## Physical coupling without grammar laundering

`PhysicalCouplingFactorisation.agda` separates:

- hidden physical evolution;
- ternary token semantics;
- stack maintenance;
- the abstract grammar.

It supports guard-only and state-affecting coupling without silently adding grammar symbols or treating a physical mechanism as a consciousness theorem.

## Control, kink, collapse, and recovery

`AnesthesiaLanguagePhaseDynamics.agda` defines a finite effect-site recurrence and the margin normal form:

```text
support    = baseline + compensation * effect + coupling
impairment = anesthetic * effect^3 + obligation * stackDepth
```

The linear compensation and cubic impairment prove the small pre-collapse upward kink, subsequent turn, and negative crossing without inserting a hand-shaped GELU.

A Schmitt-style phase gate uses separate collapse and recovery thresholds. Recovery additionally requires stack reconstruction, so the same control value can yield a different phase depending on path. The module also proves the cusp boundary witness:

```text
4 * r^3 = 27 * h^2
(r,h) = (3,2)
```

Here `27=3^3` arises from the cubic discriminant, not from the ternary gate.

## Commas as diffusion anchors

`CommaDiffusionLanguage.agda` models a comma as a locally fixed relational coordinate inside a jointly revisable sentence. The left clause is retained as a coarse basis, the right clause is refined against it, and interruption at the comma recovers the held left constituent.

The denoiser proves:

```text
boundary (denoise state) = comma
relation (denoise state) = relation state
```

while left and right content may change. Right refinement depends on the left clause, so the update does not factor into two independent denoisers.

The ternary candidate lane permits early `pos -> zero` revision and later `zero -> pos` finalisation. An anchor-first planner explicitly chooses the comma boundary before the left and right clause coordinates.

Diffusion-language-model sources include:

- Jacob Austin, Daniel D. Johnson, Jonathan Ho, Daniel Tarlow and Rianne van den Berg (2021), `arXiv:2107.03006`;
- Xiang Lisa Li, John Thickstun, Ishaan Gulrajani, Percy Liang and Tatsunori Hashimoto (2022), `arXiv:2205.14217`;
- Subham Sekhar Sahoo et al. (2024), `arXiv:2406.07524`;
- Jiaxin Shi, Kehang Han, Zhe Wang, Arnaud Doucet and Michalis K. Titsias (2024), `arXiv:2406.04329`;
- Shen Nie et al., *Large Language Diffusion Models* (NeurIPS 2025), `arXiv:2502.09992`;
- Fred Zhangzhi Peng et al., *Planner Aware Path Learning in Diffusion Language Models Training* (ICLR 2026 Oral), OpenReview `lAlI5FuIf7`.

Comma/prosodic-boundary sources include:

- Robin L. Hill and Wayne S. Murray (2000), DOI `10.1016/B978-008043642-5/50027-9`;
- Yingyi Luo, Ming Yan and Xiaolin Zhou (2013), DOI `10.1037/a0029182`.

Those papers motivate iterative refinement, non-uniform denoising order, boundary wrap-up, and altered post-boundary processing. They do not state the DASHI comma theorem.

## Physical electrochemical diffusion and network transport

`ElectrochemicalDiffusionBridge.agda` keeps molecular/ionic transport separate from graph transport. Its physical channel vocabulary includes:

- voltage-gated axonal propagation;
- vesicular release and receptor binding;
- gap-junction current;
- extracellular concentration diffusion.

A two-compartment concentration fixture conserves total concentration while reducing the gradient:

```text
(5,1) -> (4,2)
total:    6 -> 6
gradient: 4 -> 2
```

The sources for extracellular/volume transmission are Kjell Fuxe et al. (2010), DOI `10.1016/j.pneurobio.2009.10.012`, and Dasiel O. Borroto-Escuela et al. (2015), DOI `10.1098/rstb.2014.0183`.

`PsychedelicNetworkDiffusion.agda` separately models graph/effective transport and distinguishes:

- structural adjacency;
- functional statistical dependence;
- effective directed influence;
- local dynamical Jacobian;
- phase synchrony;
- chemical diffusion kernel;
- haemodynamic observation.

Functional connectivity is not a literal physical wire or molecular diffusion coefficient. A Jacobian belongs to a selected dynamical model `x' = F(x)`. A difference norm measures displacement from baseline, cosine data compare flattened profile direction, and synchrony measures phase/timing alignment.

`NetworkIntegritySynchronyMetrics.agda` proves that higher cross-system transport can coexist with lower phase synchrony. Thus increased communication between systems does not imply increased internal integrity or time-locking.

The exact network fixture is:

```text
within-system integrity : 18 -> 12
cross-system transport  :  2 ->  8
segregation margin      : 16 ->  4
phase agreement         :  3 ->  1
```

The empirical source boundary includes:

- Karl J. Friston (2011), DOI `10.1089/brain.2011.0008`;
- Pascal Fries (2005), DOI `10.1016/j.tics.2005.08.011`;
- Robin L. Carhart-Harris et al. (2016), DOI `10.1073/pnas.1518377113`;
- Andrea I. Luppi et al. (2021), DOI `10.1016/j.neuroimage.2020.117653`;
- S. Parker Singleton et al. (2022), DOI `10.1038/s41467-022-33578-1`;
- Manesh Girn et al. (2026), DOI `10.1038/s41591-026-04287-9`.

The 2026 mega-analysis supports a robust core increase in selected transmodal-to-unimodal functional coupling and only selective, variable reductions within networks. The formalism therefore does not promote a uniform increase in every edge or a universal within-network collapse.

The measurable DASHI hypothesis is increased residence near the projective decision band. The present module proves a finite one-versus-three zero-state fixture; real psychedelic zero-residence remains an empirical target.

## Visual basis, noise, defect, and fixed points

`VisualPatternGeneratorMDL.agda` reuses `Base369.TriTruth`, retinal form-constant vocabulary, and the perceptual-manifold residual. It renders orientation, lattice, checker, spiral, tunnel, cobweb, and semantic-scene sheets, assigns constructive code lengths, proves geometric-versus-semantic comparisons, and proves three pointwise phase rotations return the original sheet.

`VisualAttractorDefect.agda` implements:

```text
visual state = basis generator + noise + residual defect
```

and combines eigenmode defect, nonlinear-selection defect, semantic-binding defect, and MDL cost. The finite lattice fixture witnesses:

```text
neural attractor
intersection geometric eigenmode
intersection MDL compression attractor
```

`VisualSymmetryFixedPoint.agda` gives a stronger exact result. A four-pixel alternating orientation pattern is fixed by spatial shift followed by hidden-fibre involution. Every pixel nevertheless projects publicly to `BT.zero`. Its fixed-point defect is zero, while a uniform hidden pattern has defect four.

The neural-field sources are:

- G. Bard Ermentrout and Jack D. Cowan (1979), DOI `10.1007/BF00336965`;
- Paul C. Bressloff, Jack D. Cowan, Martin Golubitsky, Peter J. Thomas and Matthew C. Wiener (2001), DOI `10.1098/rstb.2000.0769`.

The finite fixtures are not cortical parameter fits and do not claim that all psychedelic imagery is generated in V1.

## Keppler discriminator

`KepplerFiniteResonanceMDL.agda` implements finite frequency-labelled glutamate susceptibility, field-mode density, in-band overlap, off-band control, ensemble drive, thresholded coherent-domain candidate phase, and complete predictive-code comparison.

`BaselineMarginModelSelection.agda` inverts:

```text
baseline = control + observedMargin - beta * resonanceDrive
```

One fixture shows scalar control is sufficient and the extra term loses MDL. Another shows a coupling reconstructs a tighter baseline distribution and earns its model cost. These are model-theoretic fixtures, not evidence for a physiological ZPF spectrum, vacuum causality, clinical prediction, or consciousness causation.

## Enriched quantum-mind implication ladder

`QuantumMindRetypingBoundary.agda` retains the conservative authority boundary.

`QuantumMindEnrichedRetyping.agda` records the stronger internal ladder:

```text
observable ternary shadow
-> phase-bearing zero fibre
-> common 3-6-9 quotient
-> non-rectangular joint support
-> no-global-section contextuality
-> recursive compatible fibre family
-> identity vacuum from neutral defect decomposition
```

The repository still does not derive complex Hilbert amplitudes, a Born rule, physical brain entanglement, no-signalling, or a Bell violation.

## Typed research receipts

`CognitiveResearchSources.agda` stores author, year, title, venue, DOI, and archive identifiers. These values document empirical/model contact; they are not theorem assumptions.

## Closure surface

`CognitiveSystemAnalyticClosure.agda` packages theorem values for:

- ternary ultrametricity and addresses;
- category and quotient-relative multiple drafts;
- independent branching, MDL, and stack observables;
- the control kink, hysteresis, and cusp boundary;
- scalar-versus-coupled Keppler MDL selection;
- phase-bearing zero fibres and exact `2/3/6/18` counts;
- nonfactorability, holonomy, and no-global-section contextuality;
- literal triadic tetration and recursive inverse-limit families;
- comma invariance and anchor-first planning;
- Id/Ego/Superego discrepancy and auxiliary-fibre reasoning;
- physical diffusion conservation and gradient reduction;
- psychedelic integration/segregation/synchrony fixtures and zero residence;
- visual basis/noise/defect compression and symmetry fixed points;
- stable-class/non-vacuum separation;
- identity-neutrality-to-vacuum closure at zero and non-zero floors.

The focused aggregate is `LanguagePhaseEverything.agda`.

## Check

```bash
nix develop .# --command \
  bash scripts/check_cognitive_formalism.sh
```

The script audits every top-level cognition Agda module for postulates, termination escapes, and TODO/FIXME markers, then delegates to the repository Agda 2.9 parallel checker on the focused aggregate.
