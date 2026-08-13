# LLM / PNF Future Compression — Round 18

## Purpose

Round 18 moves the neural/PNF programme from counterexamples and one-query factorisations toward a reusable theory of maximally safe representation:

- normalized rational probability future kernels with total variation;
- additive epsilon-error composition and data processing;
- finite future-signature partition refinement;
- quotient-fibre residual lower bounds and a literal one-bit/two-bit optimum;
- an actual held-out modular C3 grokking task whose structural rule is the task character;
- a dynamic multi-query state-abstraction theorem;
- reconstruction-obligation refinement;
- provenance-sensitive learning futures;
- text-as-image / optical compression as a modality-phase transform;
- cross-modal common-latent future equivalence;
- an infinite Cantor polar-stream carrier with exact cylinder premeasure consistency.

This directly addresses the frontier list in the attached round-17 status: calculate the safe quotient, quantify approximate safety, and prove minimum retained information rather than adding more isolated loss examples.

## Rational probability future kernels

`RationalProbabilityFutureKernelExact` replaces the Nat-weight approximation at the theorem frontier with exact normalized rational binary distributions.

For a kernel `K`, total variation is

`TV(p,q) = 1/2 (|p0-q0| + |p1-q1|)`.

The module proves:

- exact normalization/nonnegativity is part of the probability carrier;
- the total-variation triangle inequality;
- `epsilon1` plus `epsilon2` error composition across future-equivalent approximations;
- a data-processing theorem for every explicitly TV-non-expansive postprocessor.

The result is genuine finite probability semantics. It still does not claim a sigma-additive measure over infinite token traces.

## Computing a future quotient

`FiniteFuturePartitionRefinementExact` defines depth-indexed future equivalence recursively and proves refinement monotonicity. A four-state deterministic machine is then actually refined:

- current observation merges `source` and `memo`;
- one-step refinement separates them because their next observations differ;
- `memo` and `twin` remain one class;
- every state is fixed after its first transition;
- the resulting one-step code determines every finite-trace observation.

Thus the stable code computes the complete deterministic future quotient for that finite machine rather than merely characterising safe compression abstractly.

## Residual lower bounds

`ResidualFibreLowerBoundExact` proves the generic injection theorem:

`same quotient class + same exact residual -> same fine state`.

Consequently distinct states in one quotient fibre require distinct residual codes. The same theorem is stated dynamically: distinct future-equivalence classes inside one coarse fibre must receive different residuals in any future-safe pair code.

`ResidualBitLowerBoundThreeExact` makes the cardinality lower bound literal. Three representatives in one class cannot be exactly reopened from one Boolean residual (pigeonhole over three Booleans), while two Boolean coordinates encode and reopen all three exactly. This is the concrete fixed-length optimum `ceil(log2 3) = 2`.

## Actual modular grokking task

`ModularFourierGrokkingC3Exact` replaces the earlier Boolean progress-only toy with a real modular task over the repository's C3 character carrier.

The algorithmic learner implements C3 composition. The memorizer agrees on eight training pairs but intentionally misextends the held-out `(2,2)` pair. Therefore:

- memorizer and structural rule are exactly training-equivalent;
- the held-out task point separates them;
- the algorithmic rule is definitionally the supplied task-character composition law.

Sources:

- Alethea Power, Yuri Burda, Harri Edwards, Igor Babuschkin, Vedant Misra, *Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets*, arXiv:2201.02177; no DOI asserted.
- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt, *Progress measures for grokking via mechanistic interpretability*, arXiv:2301.05217; no DOI asserted.
- Andrey Gromov, *Grokking modular arithmetic*, arXiv:2301.02679; no DOI asserted.

## Grokking / Cantor refinement

`GrokkingCantorRefinementExact` keeps the analogy disciplined. Training mass remains unit at every finite learning stage; mechanism mass becomes unit before task mass; support complexity falls from 3 to 2 to 1; and the cleanup transition simultaneously lowers support complexity and raises task coverage.

Cantor layer mass remains a separate certificate imported from the existing finite cylinder module. No theorem turns `1_training`, `1_mechanism`, `1_task`, or `1_Cantor` into one another.

## Dynamic multi-query abstraction

`DynamicMultiQueryMultiResolutionExact` upgrades static query factorization into a real state abstraction. The fine, compressed-global, and local-residual carriers each have query-indexed dynamics. If both retained components commute with each fine step and the observation factors through them, then:

- compression commutes with every query trace;
- the local residual commutes with every query trace;
- the final observation factors through the evolved retained carrier;
- equal initial retained carriers imply equal observations after every finite query trace.

This is the dynamic form needed for long-context sequence systems.

## Reconstruction-obligation lattice

`ResidualObligationLatticeExact` formalizes

`exact => provenance => semantic => compute`

as refinement of reconstruction relations. A residual satisfying a stronger relation automatically satisfies every weaker relation. Conversely, whenever a stronger consumer separates two states that a weaker consumer merges, any pair code sufficient for the stronger relation must give those states distinct residuals.

## Learning provenance

`LearningProvenanceFutureExact` reuses `PathDependentAccessibilityExact`. Two learners have identical current parameter and output projections but different optimizer provenance. The same training action sends one to a specialized parameter and leaves the other neutral. Thus parameter equality is not a complete learning-state quotient.

## Optical / image-token text compression

`OpticalTextCompressionPNFExact` formalizes text-as-image compression as a representation-modality change, not semantic authority.

Source metadata carried in Agda:

- Haoran Wei, Yaofeng Sun, Yukun Li, *DeepSeek-OCR: Contexts Optical Compression*, arXiv:2510.18234, arXiv DOI `10.48550/arXiv.2510.18234`.
- Yanhong Li, Zixuan Lan, Jiawei Zhou, *Text or Pixels? Evaluating Efficiency and Understanding of LLMs with Visual Text Inputs*, Findings of EMNLP 2025, DOI `10.18653/v1/2025.findings-emnlp.558`.

The finite theorem demonstrates that perfect rendered-surface reconstruction can coexist with loss of provenance needed by a future query. Retaining provenance as a residual reopens the fine carrier exactly.

`MultimodalPhaseFutureEquivalenceExact` then separates modality phase from the existing C3/task dynamical phase. Modality change commutes with task-phase advance. More generally, text and visual states that factor through the same latent code have identical declared consumer observations for every query.

This is the safe cross-modal statement: different token modalities may be different representatives of one consumer-future class when the common-latent factorization is proved.

## Infinite Cantor carrier

`CantorProjectiveCylinderMeasureExact` moves beyond finite depth to an infinite binary polar-stream carrier embedded in ternary left/right Cantor digits. Finite prefixes define cylinder events with exact rational mass `2^-n`. The root has mass one and every parent mass equals the sum of its two child masses.

This is an exact projectively consistent cylinder premeasure over an infinite carrier. Countable additivity and sigma-algebra extension remain the analytic measure-extension seam; the module does not disguise finite/projective consistency as that theorem.

## Combined research spine

The current strongest form is:

`fine state -> representation modality -> retained carrier -> accessibility -> current observation -> deterministic/probabilistic future class + residual`.

The safety criterion is consumer-indexed future equivalence. The quantitative criterion is total-variation error under complete traces. The minimum residual is constrained by quotient-fibre cardinality. Task symmetry supplies phase structure rather than receiving it from numerology. Multimodal compression is safe only relative to the future distinctions its common latent carrier provably preserves.

## Validation boundary

No GitHub Actions or CodeRabbit are required by this tranche. The round-18 checker cascades the round-17 checker, scans all new theorem files for holes/postulates/trust escapes, validates theorem/source markers, and invokes Agda on the cumulative aggregate when Agda is available.
