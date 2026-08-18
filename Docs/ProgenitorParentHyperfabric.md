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

`ParentPredicate = ParentCarrier → Bool` supplies decidable local predicates. Pointwise meet and join form the local predicate lattice. `ParentPredicateFibre slot predicate` retains a hidden carrier, its Wikidata-slot equality, and a semantic predicate witness. `parentFibreRestrictionCore` is the pre-existing `DASHI.Core.FibreRestrictionCore`; evidence restricts a parent fibre without recovering the carrier or promoting truth.

The hyperfabric is carrier-indexed. `parentRelationHyperfabric carrier` is a `DASHI.Reasoning.TypedHyperfabricCore.TypedHyperfabric` with the full `RelationVector` at the vertex stalk and individual semantic Boolean coordinates at edge stalks. `parentRelationSection carrier` is a canonical `GlobalSection`: every edge value is literally the restriction of that carrier's complete relation vector.

`ProgenitorParentPredicateBaseChange.agda` adds the predicate order `p ⊑p q`; `ProgenitorParentPredicatePullbackExact.agda` proves a fibre over `p ⊓p q` is interconvertible with one slot-compatible carrier carrying separate proofs of `p` and `q`.

## Observer refinement and residual fibres

`DASHI.Core.ObserverRefinementLatticeExact` extracts the observer theorem pattern already present independently in the parent and Hecke lanes. An observer is `State → Value`; `Separating` means equal observations force equal states; `StrictRefinement coarse fine` means the fine observer implies coarse agreement but has an explicit pair the coarse observer collides on and the fine observer separates.

For finite homogeneous observer families, `ResidualObservationFibre family x` is the set of states agreeing with `x` on that family. `addingObserverShrinksResidualFibre` proves monotonic refinement: adding an observer maps the new residual fibre into the old one. It deliberately does **not** assert that a richer family is automatically separating.

`ProgenitorParentObserverDynamicsBridge.agda` gives concrete parent instances:

- P8810 alone is not separating;
- `(P8810, genetic)` is a strict refinement of P8810 using anonymous donor versus adoptive parent;
- genetic contribution alone is still not separating, since anonymous donor and ordinary genetic mother can agree genetically while disagreeing on genealogical parenthood.

The old saturated Hecke lane independently instantiates the same core in `Ontology.Hecke.CurrentSaturatedObserverRefinementBridgeExact.agda`: the current full `DefectOrbitSummary` is proved to collide on `balancedCycle` and `supportCascade`; a future histogram or correlation inequality witness is converted generically into a strict refinement. The still-postulated histogram/correlation separator targets are not promoted to proved facts.

## Fibre-preserving dynamics

`DASHI.Core.FibrePreservingDynamicsExact` sits directly over `FibreRestrictionCore`. A `HiddenTransition` changes the fine carrier while leaving the coarse projection fixed; a nontrivial `FibreAutomorphism` therefore proves the coarse projection is noninjective.

The parent instance is legal finalization: `preFinalizationCarrier` and `postFinalizationCarrier` differ in the `legalParent` coordinate while both remain in the same P8810 fibre. Thus a real relational transition can occur vertically inside an unchanged public parent edge. Disclosure can likewise change while P8810 remains fixed.

This is not merely a social example. The live Brandt/Fricke branch now instantiates the same generic core directly on the source-native p=11 marked carrier. The marked Frobenius involution swaps `a0` and `a1`, preserves their coarse `j=0` class, and is therefore a nontrivial fibre automorphism. Its source-facing arithmetic context remains Betina–Lecouturier, *Congruence formulae for Legendre modular polynomials*, DOI `10.1016/j.jnt.2018.01.006`, and Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, DOI `10.1515/9781400881710`.

## Sectioned quotient, residual reopening, and predicate descent

`DASHI.Core.SectionedProjectionProvenanceBridgeExact` sharpens the quotient story. A section chooses a representative for each coarse class and is enough to reconstruct fibre-constant observables, but **not** arbitrary fine states. Exact reopening into the existing `ProvenanceBearingQuotient` requires a separate residual coordinate.

The arithmetic branch supplies a concrete realization: the 5-state marked p=11 carrier projects to two coarse supersingular j-classes, and coarse j plus a three-valued residual sheet coordinate exactly reopens all five marked states. This is the exact PNF pattern `surface + proof-relevant residual = reopenable fine state`.

`DASHI.Core.PredicatePullbackLatticeExact` proves that coarse Boolean predicates pull back to fibre-constant fine predicates and that pullback preserves pointwise meet/join. With a section, every fibre-constant fine predicate is reconstructed from representative values.

`ProgenitorParentPredicateDescentBoundary.agda` then gives an exact Wikidata criterion: a semantic coordinate can live faithfully on the slot surface only if it is constant on slot fibres. `isP8810` descends; `geneticP`, `genealogicalParentP`, and `progenitorP` do not, because the same P8810 fibre contains explicit carriers on which those coordinates differ. The arithmetic p=11 bridge independently proves the analogous fact: a coarse `j=0` predicate descends while the marked-sheet predicate `isA0` does not.

## Separation is not authority

`ProgenitorParentObservationAuthorityBridge.agda` reuses `ProofRelevantIdentityFibres` and `ConsumerIndexedRelevanceMeasure` instead of inventing a new permission layer. A disclosure observer is mathematically separating on the explicit two-state donor disclosure fibre, yet surface-local evidence still cannot claim world-canonical identity. Likewise consumer relevance normalization cannot manufacture world truth or completeness.

Therefore:

`separating observer ≠ epistemic availability ≠ disclosure/world-identity authority`.

## Pullback topology boundary

JMD's own `PullbackComparison` source prevents overclaiming. `LeanWikidataPullbackTopologyBoundary.agda` imports both `isHomeomorph_pbCompare_of_componentwise` and `exists_not_isHomeomorph_pbCompare`: componentwise compatibility suffices for the positive comparison theorem, while arbitrary categorical pullbacks need not be homeomorphic. Therefore categorical pullback, semantic/topological equivalence, and local PNF compatibility remain distinct notions.

## Wikidata projection

P22, P25, P8810 and P1531 are represented as surface slots rather than the carrier ontology. Individual generic parenthood projects to P8810; lineage-level progeniture projects to P1531. The cultivar/hybrid/breed rule is therefore modeled as representation specialization, not as proof that cultivars are ontologically incapable of progeniture.

Crucially, the cultivar witness has `progenitorRelation = true` while `genealogicalParent = false`: lineage parentage is not silently collapsed into person/family parenthood.

## Main theorem surface

Core non-collapse includes `causalInputDoesNotImplyProgenitor`, `triparentalPlantHasThreeContributors`, `binaryBoundRequiresBiparentalProfile`, `geneticContributionCannotDetermineParenthood`, `parenthoodCannotDetermineGeneticContribution`, `gestationCannotDetermineParenthood`, `mitochondrialContributionCannotDetermineParenthood`, `oneParentTwoGeneticContributors`, and `parentGeneticsBiconditionalFailsBothDirections`.

The new observer/descent/dynamics tranche adds `addingObserverShrinksResidualFibre`, `collisionBlocksSeparation`, `p8810GeneticStrictRefinement`, `p8810SlotNotSeparating`, `geneticObserverNotSeparating`, `legalFinalizationIsHiddenP8810Transition`, `variantDisclosureObserverSeparating`, `geneticPredicateNotFibreConstant`, `genealogicalParentPredicateNotFibreConstant`, `progenitorPredicateNotFibreConstantOnP8810`, `residualReopeningGivesProvenanceBearingQuotient`, `pullbackPreservesMeet`, and `pullbackPreservesJoin`.

The independent arithmetic instantiation supplies `minusTwoT2ToFrobeniusStrictRefinement`, `jointT3T5FNotSeparating`, `jointFingerprintToDeckTypeStrictRefinement`, `markedFrobeniusNontrivialFibreAutomorphism`, `markedFrobeniusHiddenTransition`, `fine5PNFProvenanceQuotient`, and `markedA0PredicateNotFibreConstant` on its own live branch.

The intended synthesis is:

`fine carrier ≠ local predicate ≠ observer fingerprint ≠ PNF fibre ≠ coarse quotient ≠ public representation ≠ disclosure authority`,

while explicit pullback, base-change, residual-reopening, observer-refinement, and fibre-automorphism witnesses say exactly what survives each projection and exactly what is lost.
