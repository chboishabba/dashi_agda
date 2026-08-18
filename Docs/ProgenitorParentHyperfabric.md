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

`LeanWikidataParentingPullbackBridge.agda` pins the exact supplied source files by SHA-256 rather than merely paraphrasing them. It imports theorem contracts for the latest `Parenting`, `ParentingExamples`, `ParentingDiagnostics`, `PullbackComparison`, `PullbackRetraction`, `MetaFrobenius`, `CategoryOfOntologies`, and `CubicalTypes` files.

The consumed Lean theorem surface includes `ParentingKB.descendsFromB_iff`, `geneticDescendsFromB_iff`, `card_geneticParentsF_le_two`, `FKB.pValid_toParentingKB`, `ParentingKB.rainbow_four_parents`, `adoption_legal_disjoint_genetic`, `surrogacy_birth_not_genetic`, `ParentingKB.report_eq_nil_iff_pValid`, `Ontology.Retract.baseChange`, the two base-change conservativity theorems, and `KB.metaLift_isPullback`.

JMD's eight `ParentRole` constructors and exact `isGenetic`, `isLegal`, and `isSocial` predicates are reified in Agda. `refineJMDRole` maps those coarse role tags into the richer DASHI relation vector while proving those source predicates are preserved. `jmdRecordedParentProjectionIsLossy` proves the refinement is strict: donor and adoptive roles are both recorded as `ParentEdge`s in JMD, yet their richer genealogical-parent coordinates differ.

### Cardinality scope boundary

`LeanWikidataParentingCardinalityBoundary.agda` prevents a common scope error. JMD proves **at most two** genetic parents only under `geneticSlotsTyped = true` and `singleGeneticParents = true`. The explicit `AtMostTwo` carrier has zero-, one-, and two-element cases; `oneGeneticContributorGeneration` is a concrete singleton witness. Hence an upper bound cannot determine exact-two cardinality or select a reproductive mechanism. DASHI's exact-two theorem remains separately indexed by `BiparentalNuclearWitness`.

## PNF / predicate lattice / hyperfabric pullback

`ProgenitorParentPNFPullbackLattice.agda` places the parent construction directly on existing DASHI infrastructure rather than defining a parallel category-theory vocabulary.

`ParentPredicate = ParentCarrier → Bool` supplies decidable local predicates. Pointwise meet and join form the local predicate lattice:

- `p ⊓p q` = both predicates hold;
- `p ⊔p q` = either predicate holds.

The primitive lattice elements include progenitor, genetic, gametic, mitochondrial, gestational, genealogical-parent, intended-parent, legal-parent, social-parent, and caregiver predicates.

`ParentPredicateFibre slot predicate` is a concrete pullback/fibre object: it retains a hidden `ParentCarrier`, a proof that it projects to the requested Wikidata slot, and a proof that the requested semantic predicate holds. Thus surface slot and semantic predicate are matched without identifying either with the carrier.

`parentFibreRestrictionCore` is an exact specialization of pre-existing `DASHI.Core.FibreRestrictionCore`: evidence restricts a parent fibre, `doesNotRecoverCarrier = true`, and `promotesTruth = false`. `pnfUsesSameFibreCore` witnesses that this is exactly the fibre-core type already carried by `PNFEvidenceHyperformalism`.

The hyperfabric is carrier-indexed. `parentRelationHyperfabric carrier` is a `DASHI.Reasoning.TypedHyperfabricCore.TypedHyperfabric` with the full `RelationVector` at the vertex stalk and individual semantic Boolean coordinates at edge stalks. `parentRelationSection carrier` is a canonical `GlobalSection`: every edge value is literally the restriction of that carrier's complete relation vector. Therefore donor, adoptive, and cultivar non-collapse results are compatibility theorems in the fabric rather than unrelated Boolean examples.

`ProgenitorParentPredicateBaseChange.agda` adds the predicate order `p ⊑p q`, proves meet projects to each factor and each factor maps into join, and defines `predicateBaseChange`. A fibre under a stronger predicate therefore maps canonically to the corresponding fibre under a weaker predicate.

`ProgenitorParentPredicatePullbackExact.agda` strengthens this from one-way maps to exact data equivalence: a fibre over `p ⊓p q` is interconvertible with one slot-compatible hidden carrier carrying separate proofs of `p` and `q`. `meetFibreToPullbackPair` and `pullbackPairToMeetFibre` preserve the hidden carrier in both round trips. Thus predicate conjunction is literally realized as fibre-product data over the common carrier.

## Pullback topology boundary

JMD's own `PullbackComparison` source prevents overclaiming. `LeanWikidataPullbackTopologyBoundary.agda` imports both `isHomeomorph_pbCompare_of_componentwise` and `exists_not_isHomeomorph_pbCompare`: componentwise compatibility suffices for the positive comparison theorem, while arbitrary categorical pullbacks need not be homeomorphic. Therefore categorical pullback, semantic/topological equivalence, and local PNF compatibility remain distinct notions.

This is why the parent construction keeps explicit slot, predicate, stalk-restriction, and componentwise witnesses rather than treating the word “pullback” as automatic semantic identity.

## Wikidata projection

P22, P25, P8810 and P1531 are represented as surface slots rather than the carrier ontology. Individual generic parenthood projects to P8810; lineage-level progeniture projects to P1531. The cultivar/hybrid/breed rule is therefore modeled as representation specialization, not as proof that cultivars are ontologically incapable of progeniture.

Crucially, the cultivar witness has `progenitorRelation = true` while `genealogicalParent = false`: lineage parentage is not silently collapsed into person/family parenthood.

The exact `ParentSlotFibre` contains multiple hidden relation carriers over the same P8810 surface. Anonymous donor and adoptive-parent carriers share the P8810 slot while disagreeing on the genetic coordinate. Thus the visible Wikidata slot cannot recover hidden parent semantics.

A compatible surface-plus-carrier view is provided with `liftCarrier` and `forgetCompatibility`, with `forgetAfterLift` proving the carrier is a retract of the compatible representation. The latest JMD bridge gives this construction an explicit source-side categorical reference rather than merely an analogy.

## Main theorem surface

Core non-collapse:

- `causalInputDoesNotImplyProgenitor`
- `triparentalPlantHasThreeContributors`
- `binaryBoundRequiresBiparentalProfile`
- `geneticContributionCannotDetermineParenthood`
- `parenthoodCannotDetermineGeneticContribution`
- `gestationCannotDetermineParenthood`
- `mitochondrialContributionCannotDetermineParenthood`
- `oneParentTwoGeneticContributors`
- `parentGeneticsBiconditionalFailsBothDirections`

Wikidata/fibre:

- `entityTypeDoesNotDetermineParentEligibility`
- `wikidataParentSlotDoesNotDetermineParentSemantics`
- `cultivarConflictIsRepresentationRestriction`
- `p1531AndP8810ShareProgenitorCarrier`
- `p8810FibreContainsGeneticallyDistinctCarriers`
- `p1531SpecializationPreservesProgenitorCoordinate`
- `carrierRetractionIsExact`

JMD refinement and scope:

- `jmdGeneticPredicatePreserved`
- `jmdLegalPredicatePreserved`
- `jmdSocialPredicatePreserved`
- `jmdRecordedParentProjectionIsLossy`
- `jmdCapDoesNotMeanExactlyTwo`
- `jmdCapDoesNotDetermineReproductiveProfile`
- `pullbackDoesNotCollapseSemanticTopology`
- `componentwiseCompatibilityRemainsExplicit`

PNF/lattice/pullback:

- `cultivarProgenitorDoesNotCollapseToGenealogicalParent`
- `anonymousDonorFabricNonCollapse`
- `adoptiveFabricNonCollapse`
- `cultivarFabricSeparatesProgenitorFromParent`
- `predicateBaseChange`
- `meetFibreToLeft`
- `meetFibreToRight`
- `meetFibreToPullbackPair`
- `pullbackPairToMeetFibre`
- `meetPullbackCarrierRoundTrip`
- `pullbackMeetCarrierRoundTrip`
- `parentPullbackKeepsProjectionBoundary`

The intended synthesis is:

`generative carrier ≠ local predicate ≠ PNF fibre ≠ Wikidata surface ≠ preferred-encoding constraint ≠ disclosure authority`,

while compatible predicate intersections and representation views are glued by explicit pullback/base-change witnesses rather than semantic collapse.
