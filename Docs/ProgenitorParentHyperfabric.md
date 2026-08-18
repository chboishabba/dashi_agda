# Progenitor / Parent Hyperfabric

This tranche separates generative provenance, parenthood, Wikidata representation, and disclosure rather than overloading one `ParentRole` or one property slot.

## Carrier

The base object is an arbitrary finite `GenerationEvent` whose `progenitors` are immediate lineage-bearing predecessors/contributors. Mere causal inputs are separate: the canonical incubator witness participates causally but is not lineage-bearing.

The base carrier has no universal two-parent cardinality axiom. `triparentalPlantGeneration` has three direct gametic progenitors, grounded by Mao et al., *Selective egg cell polyspermy bypasses the triploid block*, eLife 9:e52976 (2020), DOI `10.7554/eLife.52976`. Exact binary cardinality is recovered only from an explicit `BiparentalNuclearWitness`.

Mitochondrial contribution is kept distinct from ordinary nuclear/gametic contribution, with source metadata for Tachibana et al., *Towards germline gene therapy of inherited mitochondrial diseases*, Nature 493, 627–631 (2013), DOI `10.1038/nature11647`.

## Orthogonal fibres

`RelationVector` retains independent coordinates for progenitor relation, genetic, gametic, mitochondrial, gestational, genealogical-parent, intended-parent, legal-parent, social-parent, caregiver, identity-known, and identity-disclosable status.

This yields executable countermodels:

- anonymous IVF donor: progenitor/genetic/gametic contributor, not genealogical/intended/legal/social parent;
- adoptive parent: genealogical/intended/legal/social parent, not progenitor or genetic contributor;
- gestational surrogate-only witness: gestational contributor without progeniture or genealogical parenthood;
- mitochondrial donor: progenitor/mitochondrial/genetic contribution without automatic parenthood.

The concrete donor-conception family computes to **one genealogical parent and two genetic contributors**. This is the central witness that `Parent ≡ GeneticContributor` is not a valid ontology identity.

## Latest JMD/Aristotle Lean bridge

`LeanWikidataParentingPullbackBridge.agda` now pins the exact supplied source files by SHA-256 rather than merely paraphrasing them. It imports theorem contracts for the latest:

- `RequestProject.Parenting`
- `RequestProject.ParentingExamples`
- `RequestProject.ParentingDiagnostics`
- `RequestProject.PullbackComparison`
- `RequestProject.PullbackRetraction`
- `RequestProject.MetaFrobenius`
- `RequestProject.CategoryOfOntologies`
- `RequestProject.CubicalTypes`

The consumed Lean theorem surface includes `ParentingKB.descendsFromB_iff`, `geneticDescendsFromB_iff`, `card_geneticParentsF_le_two`, `FKB.pValid_toParentingKB`, `ParentingKB.rainbow_four_parents`, `adoption_legal_disjoint_genetic`, `surrogacy_birth_not_genetic`, `ParentingKB.report_eq_nil_iff_pValid`, `Ontology.Retract.baseChange`, the two base-change conservativity theorems, and `KB.metaLift_isPullback`.

The source scopes are preserved exactly: JMD proves **at most two** genetic parents under `geneticSlotsTyped = true` and `singleGeneticParents = true`; DASHI does not rewrite this as the stronger statement that every ordinary generation has exactly two contributors. The latter remains a separate reproductive-profile theorem.

JMD's eight `ParentRole` constructors and the exact `isGenetic`, `isLegal`, and `isSocial` predicate surfaces are reified in Agda. `refineJMDRole` then maps those coarse role tags into the richer DASHI relation vector while proving the three source predicates are preserved. `jmdRecordedParentProjectionIsLossy` shows why the refinement is strict: donor and adoptive roles are both recorded as `ParentEdge`s in JMD, yet their richer genealogical-parent coordinates differ.

## PNF / predicate lattice / hyperfabric pullback

`ProgenitorParentPNFPullbackLattice.agda` places the parent construction directly on existing DASHI infrastructure rather than defining a parallel category-theory vocabulary.

`ParentPredicate = ParentCarrier → Bool` supplies decidable local predicates. Pointwise meet and join form the local predicate lattice:

- `p ⊓p q` = both predicates hold;
- `p ⊔p q` = either predicate holds.

The primitive lattice elements include progenitor, genetic, gametic, mitochondrial, gestational, genealogical-parent, intended-parent, legal-parent, social-parent, and caregiver predicates.

`ParentPredicateFibre slot predicate` is the concrete pullback/fibre object: it retains a hidden `ParentCarrier`, a proof that it projects to the requested Wikidata slot, and a proof that the requested semantic predicate holds. Thus the surface slot and semantic predicate are matched without identifying either with the carrier.

`parentFibreRestrictionCore` is an exact specialization of the pre-existing `DASHI.Core.FibreRestrictionCore`: evidence restricts a parent fibre, `doesNotRecoverCarrier = true`, and `promotesTruth = false`. `pnfUsesSameFibreCore` witnesses that this is exactly the fibre-core type already carried by `PNFEvidenceHyperformalism`.

`parentRelationHyperfabric` is a `DASHI.Reasoning.TypedHyperfabricCore.TypedHyperfabric`: the vertex stalk contains the whole `RelationVector`, while edge stalks are the individual semantic Boolean coordinates. Restriction maps are literal coordinate projections. The anonymous-donor witness therefore restricts to `true` on the genetic edge and `false` on the genealogical-parent edge without any type conflict or forced exclusive role tag.

`ProgenitorParentPredicateBaseChange.agda` adds the predicate order `p ⊑p q`, proves meet projects to each factor and each factor maps into join, and defines `predicateBaseChange`. Therefore a fibre under a stronger predicate canonically maps to the corresponding fibre under a weaker predicate. This is the concrete PNF/predicate counterpart of JMD's categorical result that retracts are stable under base change; the imported Lean theorem contract and the concrete Agda base-change carrier are retained side by side rather than conflated.

## Wikidata projection

P22, P25, P8810 and P1531 are represented as surface slots rather than the carrier ontology. Individual generic parenthood projects to P8810; lineage-level progeniture projects to P1531. The cultivar/hybrid/breed rule is therefore modeled as representation specialization, not as proof that cultivars are ontologically incapable of progeniture.

Crucially, the cultivar witness has `progenitorRelation = true` while `genealogicalParent = false`: lineage parentage is not silently collapsed into person/family parenthood.

The exact `ParentSlotFibre` contains multiple hidden relation carriers over the same P8810 surface. In particular, anonymous donor and adoptive-parent carriers share the P8810 slot while disagreeing on the genetic coordinate. Thus the visible Wikidata slot cannot recover the hidden parent semantics.

A compatible surface-plus-carrier view is provided with `liftCarrier` and `forgetCompatibility`, with `forgetAfterLift` proving the carrier is a retract of the compatible representation. The latest JMD bridge now gives this construction an explicit source-side categorical reference rather than merely an analogy.

## Main theorem surface

- `causalInputDoesNotImplyProgenitor`
- `triparentalPlantHasThreeContributors`
- `binaryBoundRequiresBiparentalProfile`
- `geneticContributionCannotDetermineParenthood`
- `parenthoodCannotDetermineGeneticContribution`
- `gestationCannotDetermineParenthood`
- `mitochondrialContributionCannotDetermineParenthood`
- `anonymousContributionDoesNotRevealIdentity`
- `entityTypeDoesNotDetermineParentEligibility`
- `wikidataParentSlotDoesNotDetermineParentSemantics`
- `cultivarConflictIsRepresentationRestriction`
- `p1531AndP8810ShareProgenitorCarrier`
- `p8810FibreContainsGeneticallyDistinctCarriers`
- `p1531SpecializationPreservesProgenitorCoordinate`
- `carrierRetractionIsExact`
- `oneParentTwoGeneticContributors`
- `parentGeneticsBiconditionalFailsBothDirections`
- `jmdGeneticPredicatePreserved`
- `jmdLegalPredicatePreserved`
- `jmdSocialPredicatePreserved`
- `jmdRecordedParentProjectionIsLossy`
- `cultivarProgenitorDoesNotCollapseToGenealogicalParent`
- `anonymousDonorFabricNonCollapse`
- `predicateBaseChange`
- `meetFibreToLeft`
- `meetFibreToRight`
- `parentPullbackKeepsProjectionBoundary`

The intended synthesis is:

`generative carrier ≠ local predicate ≠ PNF fibre ≠ Wikidata surface ≠ constraint on preferred encoding ≠ disclosure authority`.
