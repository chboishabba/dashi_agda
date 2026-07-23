# DASHI controlled ternary cognitive formalism

This directory models a physical cognitive subsystem as a controlled ternary language machine. The formal layer does **not** identify the brain with a PDA, a manifold, a chemical field, or an electromagnetic field separately. It types their coupling and preserves the distinction between structural compatibility, empirical establishment, and causal explanation.

## Master object

The concrete carrier is `DASHICognitiveSystem` in `DashiCognitiveSystem.agda`:

- hidden physical/cognitive state and observable quotient;
- exogenous/endogenous control and stack-obligation alphabet;
- ternary semantic and stack transitions;
- contextual admissibility and signed margin;
- grammar/model/distortion code lengths;
- coarse-graining and involution stability.

It directly reuses:

- `DASHI.Algebra.BalancedTernary.Trit` for `neg / zero / pos`;
- `DASHI.Combinatorics.PDA_MDL.PDA` for observation, admissibility, and lens cost;
- `DASHI.Combinatorics.PDA_MDL.Prelude.CodeLength` for constructive MDL;
- `DASHI.Cognition.ResidualPhaseGeometry.Projection/Fibre` for lossy observation classes.

A configuration contains a hidden state and a literal obligation stack. A derivation is accepted only when every prefix is admissible, the terminal stack closes, and the terminal margin commits positively. `LanguageAtDepth` is therefore the type of accepted ternary addresses at a fixed depth.

## Ternary and 3-adic structure

`TernaryDerivationAddress.agda` maps balanced trits to digits `0,1,2` and evaluates finite base-three addresses with the earliest token least significant, matching the p-adic coarse-to-fine convention.

`TernaryDerivationUltrametric.agda` defines longest-common-prefix distance on finite ternary vectors and proves identity, symmetry, and the strong triangle inequality. It reuses the repository `Ultrametric` interface and the proof architecture of `DASHI.Algebra.MonsterUltrametric15`.

## Phase-enriched zero and the 3-6-9 quotient

`PhaseEnrichedTrit.agda` places a finite weight-and-phase carrier above the observable balanced trit. The quotient commits to `neg` or `pos` only for a uniquely dominant binding polarity. Neutral dominance, ties, and balanced opposition project to `BT.zero`.

The theorem surface therefore distinguishes:

```text
BT.zero                         -- one public constructor
observeTrit^-1(BT.zero)         -- a populated hidden fibre
```

Two exact hidden profiles with different cyclic phases project to the same public zero. This is a structural phase-bearing fibre, not yet a Hilbert space, complex amplitude norm, Born rule, or physical neural superposition.

`Base369ZeroFibre.agda` exposes concrete product coordinates for the existing `Base369` carriers:

```text
HexTruth    ~= TriTruth x Orientation
NonaryTruth ~= TriTruth x TriTruth
```

The maps

```text
q6 : HexTruth -> TriTruth
q9 : NonaryTruth -> TriTruth
```

form the common-base diagram `6 -> 3 <- 9`. The exact fibres over `tri-mid` contain two and three representatives respectively. The pullback `6 x_3 9` has eighteen states, while its public-zero sector has six states.

`IdEgoSuperego369.agda` gives these carriers role types without treating psychoanalysis as literal anatomy:

- `3`: immediate/pre-reflexive valuation (`IdCarrier`);
- `6`: valuation plus binary observer/orientation split (`EgoCarrier`);
- `9`: felt/local valuation paired with desired, compelled, or normative valuation (`SuperegoCarrier`).

Categorical identity remains separately named `identityMorphism`.

## Local zero, global obstruction, and nonseparability

`ZeroFibreContextuality.agda` formalises the Minesweeper-like claim that visible zero is locally informative rather than empty. Every node projects to `BT.zero`, while hidden binary orientations are transported around an odd cycle. Each edge admits a local section, but the three edge laws admit no global section. Three local flips also produce nontrivial loop holonomy.

This is an exact combinatorial contextuality fixture inspired by Samson Abramsky and Adam Brandenburger, *The sheaf-theoretic structure of non-locality and contextuality*, DOI `10.1088/1367-2630/13/11/113036`.

`Monoidal369Nonseparability.agda` constructs a non-rectangular joint support on `ZeroFibre6 x ZeroFibre9` and proves that it cannot factor into independent left and right predicates. This establishes structural nonseparability. It does not yet establish complex tensor entanglement, no-signalling, or a Bell violation.

## Recursive fibre formation and tetration

`RecursiveFibreTower.agda` separates two recurrences that had previously been conflated:

1. recursive phase refinement, which adds hidden phase coordinates while preserving the base trit;
2. literal ternary-valued function-space growth.

The function-space tower is

```text
PredicateLevel 0       = Unit
PredicateLevel (n + 1) = PredicateLevel n -> TriTruth
```

and its finite cardinality obeys

```text
a(0) = 1
a(n + 1) = 3 ^ a(n)
```

which is genuine base-three tetration: `1, 3, 27, 3^27, ...`. By contrast, `X(n+1)=X(n)->X(n)` has self-exponentiation cardinality `a(n+1)=a(n)^a(n)` and is not silently called ordinary tetration.

The module also defines an inverse-system interface and a canonical compatible zero family across every phase-refinement level.

## Fibre/braid reasoning and reflexive self

`FibreBraidReasoning.agda` represents reasoning through latent, observed, desired, and compelled ternary coordinates. An auxiliary fibre acts through the existing associative `Base369.triXor` transport. A concrete witness lowers global mismatch defect from two to one by pulling in a high-valued auxiliary fibre.

This formalises a goal-directed fibre step rather than an observer-of-observer regress. The self is represented by a compatible/reflexively stable class, while the Ego mediates felt, desired, and compelled projections.

## Quotients, drafts, classes, and category

`DashiCognitiveSystem.agda` defines observational equivalence and stable observed classes under coarse-graining and involution.

`MultipleDraftsQuotient.agda` gives distinct Orwellian and Stalinesque hidden histories that map to the same public report and action but to different detailed traces. The distinction therefore disappears only after the specified quotient; hidden identity is not asserted.

`CognitiveProjectionCategory.agda` is the free category generated by physical evolution, physical realisation, guarded transitions, derivation readout, class quotient, coarse-graining, involution, observation, visual generation, and visual deformation. Identity and associativity are proved by recursion on paths, using `DASHI.Core.ProjectionCategory` as the repository category interface.

`CognitiveVacuumClassBoundary.agda` proves that an arbitrary stable class need not be a vacuum.

`IdentityVacuumClosure.agda` supplies the stronger implication. A class fixed by coarse-graining and involution and certified at a global defect floor yields the existing `VacuumClass`. A second fixture proves that the defect floor may be non-zero: identity neutrality means that no additional defect is introduced, not that measured energy must literally vanish.

## Physical coupling without grammar laundering

`PhysicalCouplingFactorisation.agda` separates:

- physical evolution of the hidden carrier;
- token semantics over that carrier;
- stack-maintenance dynamics;
- the abstract ternary alphabet and stack alphabet.

It types both a smallest guard-only lane and a state-affecting lane. The concrete Boolean witness proves that an external control can act through the control-indexed admissibility margin without adding a PDA state or redefining token meaning. The more general factorisation permits physical coupling to change the carrier passed into semantics.

## Four phase observables

The master system computes four distinct quantities:

1. fuel-bounded depth-to-failure;
2. feasible ternary branching count;
3. exact finite MDL rise/fall between observations;
4. open stack-obligation depth.

`CognitiveObservableDistributions.agda` retains exact finite distributions rather than replacing them by a single average.

`PhaseObservableIndependence.agda` proves on a concrete system that equal feasible branching can coexist with different stack depth and different MDL slope. These observables gauge different structure and are not aliases for one scalar.

## Control, kink, collapse, and recovery

`AnesthesiaLanguagePhaseDynamics.agda` supplies a finite fixed-point effect-site recurrence. Its margin normal form is

```text
support    = baseline + compensation * effect + coupling
impairment = anesthetic * effect^3 + obligation * stackDepth
```

The linear compensation and cubic impairment prove the small pre-collapse upward kink, subsequent turn, and negative crossing without inserting a hand-shaped GELU.

A Schmitt-style phase gate uses separate collapse and recovery thresholds. Recovery additionally requires a rebuilt stack scaffold, so the same control value can lie in different phases depending on path. The module also states the exact cusp boundary

```text
4 * r^3 = 27 * h^2
```

and proves the finite witness `(r,h)=(3,2)`. The coefficient `27=3^3` comes from the cubic discriminant, not from the ternary gate.

## Commas as language diffusion anchors

`CommaDiffusionLanguage.agda` models a comma as a fixed relational coordinate inside a jointly revisable sentence. The left clause is held as a coarse basis on a comma frame; the right clause is refined against it; interruption at the comma recovers the held left constituent.

The denoiser proves:

```text
boundary (denoise (left , right)) = comma
relation (denoise (left , right)) = relation (left , right)
```

while both clauses may change. Right refinement explicitly depends on the left clause, so the construction does not factor into two independent denoisers.

The ternary candidate lane permits early `pos -> zero` revision and later `zero -> pos` finalisation. This extends discrete/masked diffusion work by Austin et al. (`arXiv:2107.03006`), Li et al. (`arXiv:2205.14217`), Sahoo et al. (`arXiv:2406.07524`), and Shi et al. (`arXiv:2406.04329`); those papers motivate iterative refinement but do not claim the comma theorem.

## Brain signalling and network diffusion

`PsychedelicNetworkDiffusion.agda` distinguishes the underlying communication and measurement layers:

- axonal spikes and chemical synapses;
- electrical gap junctions;
- extrasynaptic/volume transmission;
- coherence-gated communication;
- structural, functional, and effective connectivity;
- local dynamical Jacobians;
- haemodynamic observation.

Functional connectivity is statistical dependence, not a physical wire or molecular diffusion coefficient. Effective connectivity is directed model-based influence; a Jacobian can be used as a local linearisation of that dynamical layer. Difference norms compare a condition against baseline; cosine data compare profile direction; synchrony is a separate phase statistic.

The source boundary references:

- Karl J. Friston (2011), DOI `10.1089/brain.2011.0008`;
- Pascal Fries (2005), DOI `10.1016/j.tics.2005.08.011`;
- Kjell Fuxe et al. (2010), DOI `10.1016/j.pneurobio.2009.10.012`;
- Dasiel O. Borroto-Escuela et al. (2015), DOI `10.1098/rstb.2014.0183`.

A finite two-system fixture proves the direction of the proposed psychedelic deformation:

```text
within-system integrity : 18 -> 12
cross-system transport  :  2 ->  8
segregation margin      : 16 ->  4
```

and gives exact graph-transport steps. This is motivated by Carhart-Harris et al. (2016), DOI `10.1073/pnas.1518377113`; Luppi et al. (2021), DOI `10.1016/j.neuroimage.2020.117653`; Singleton et al. (2022), DOI `10.1038/s41467-022-33578-1`; and Girn et al. (2026), DOI `10.1038/s41591-026-04287-9`.

The latest mega-analysis supports increased communication between transmodal and unimodal systems across several classic psychedelics. The formalism therefore does not claim a uniform increase on every edge or a simple global “disintegration”.

The measurable DASHI hypothesis is increased residence near the projective decision band. The module proves only a finite fixture with one versus three zero states; real psychedelic zero-residence remains an empirical target.

## Visual basis, noise, defect, and compression attractors

`VisualPatternGeneratorMDL.agda` reuses:

- `Base369.TriTruth` and `rotateTri`;
- `DASHI.Biology.RetinalPerturbationObservationBridge.FormConstantGeometry`;
- `DASHI.Biology.ObserverPerceptualManifoldResidual`.

It renders literal ternary orientation, lattice, checker, spiral, tunnel, cobweb, and semantic-scene sheets, assigns two-part constructive code lengths, proves low-code geometric comparisons, and proves three pointwise phase rotations return the original sheet. Shared low-code geometry does not imply shared phenomenal identity.

`VisualAttractorDefect.agda` adds the requested decomposition

```text
visual state = basis generator + noise + residual defect
```

and combines linear-mode defect, nonlinear-selection defect, semantic-binding defect, and MDL cost. The exact lattice fixture lies in the intersection

```text
neural attractor ∩ geometric eigenmode ∩ MDL compression attractor.
```

The mathematical motivation is Ermentrout and Cowan (1979), DOI `10.1007/BF00336965`, and Bressloff, Cowan, Golubitsky, Thomas and Wiener (2001), DOI `10.1098/rstb.2000.0769`.

An almost-binary lane is also explicit: when the public ternary coordinate remains zero, the two-state orientation fibre of the six-carrier can alternate while remaining publicly neutral.

## Keppler discriminator

`KepplerFiniteResonanceMDL.agda` turns the previous candidate vocabulary into a finite calculation:

- frequency-labelled glutamate susceptibility samples;
- frequency-labelled field-mode-density samples;
- exact in-band spectral overlap and off-band control;
- ensemble coupling drive from microcolumn count, glutamate population, and overlap;
- thresholded coherent-domain candidate phase;
- complete predictive-code comparison.

`BaselineMarginModelSelection.agda` inverts the positive-margin lane:

```text
baseline = control + observedMargin - beta * resonanceDrive
```

It proves one finite dataset where scalar control is sufficient and an extra coupling loses MDL, and another where a coupling reconstructs a tighter baseline distribution and earns its model cost.

These are model-theoretic fixtures. They do not establish a physiological ZPF spectrum, vacuum causality, clinical prediction, or consciousness causation.

## Enriched quantum-mind boundary

`QuantumMindRetypingBoundary.agda` retains the conservative authority split.

`QuantumMindEnrichedRetyping.agda` now records the stronger internal implication ladder:

```text
observable ternary shadow
-> phase-bearing zero fibre
-> common 3-6-9 quotient
-> non-rectangular joint support
-> no-global-section contextuality fixture
-> recursive compatible fibre family
-> identity vacuum at a certified defect floor
```

The branch still does not derive complex Hilbert amplitudes, a Born rule, physical brain entanglement, or a Bell violation.

## Typed sources

`CognitiveResearchSources.agda` stores author, year, title, venue, DOI, and archive identifiers used by the new modules. These citations document empirical/model contact; they are not theorem assumptions.

## Closure surface

`CognitiveSystemAnalyticClosure.agda` packages theorem values for:

- ternary ultrametricity and address evaluation;
- category and quotient-relative multiple drafts;
- physical coupling and independent phase observables;
- the cubic control kink and cusp boundary;
- scalar-versus-coupled Keppler MDL discrimination;
- phase-bearing zero fibres and exact `2/3/6/18` fibre counts;
- structural nonfactorability and no-global-section contextuality;
- literal triadic tetration and recursive inverse-limit zero family;
- comma preservation under joint denoising;
- felt/desired/compelled discrepancy and auxiliary fibre reasoning;
- psychedelic within/cross-network transport fixtures and zero residence;
- basis/noise/defect visual compression;
- stable-class/non-vacuum separation and nonzero-floor identity vacuum closure.

The focused aggregate is `LanguagePhaseEverything.agda`.

## Check

```bash
nix develop .# --command \
  bash scripts/check_cognitive_formalism.sh
```

The check first rejects postulates, termination escapes, and TODO/FIXME markers in the analytic lane, then type-checks the focused aggregate.
