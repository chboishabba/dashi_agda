# Progenitor / Parent Hyperfabric

This tranche separates generative provenance, parenthood, Wikidata representation, and disclosure rather than overloading one `ParentRole` or one property slot.

## Carrier

The base object is an arbitrary finite `GenerationEvent` whose `progenitors` are immediate lineage-bearing predecessors/contributors. Mere causal inputs are separate: the canonical incubator witness participates causally but is not lineage-bearing.

The base carrier has no universal two-parent cardinality axiom. `triparentalPlantGeneration` has three direct gametic progenitors, grounded by Mao et al., *Selective egg cell polyspermy bypasses the triploid block*, eLife 9:e52976 (2020), DOI `10.7554/eLife.52976`. Binary cardinality is recovered only from an explicit `BiparentalNuclearWitness`.

Mitochondrial contribution is kept distinct from ordinary nuclear/gametic contribution, with source metadata for Tachibana et al., *Towards germline gene therapy of inherited mitochondrial diseases*, Nature 493, 627–631 (2013), DOI `10.1038/nature11647`.

## Orthogonal fibres

`RelationVector` retains independent coordinates for genetic, gametic, mitochondrial, gestational, genealogical-parent, intended-parent, legal-parent, social-parent, caregiver, identity-known, and identity-disclosable status.

This yields executable countermodels:

- anonymous IVF donor: genetic/gametic contributor, not genealogical/intended/legal/social parent;
- adoptive parent: genealogical/intended/legal/social parent, not genetic contributor;
- gestational surrogate-only witness: gestational contributor without genealogical parenthood;
- mitochondrial donor: mitochondrial/genetic contribution without automatic parenthood.

The concrete donor-conception family computes to **one genealogical parent and two genetic contributors**. This is the central witness that `Parent ≡ GeneticContributor` is not a valid ontology identity.

## Wikidata projection

P22, P25, P8810 and P1531 are represented as surface slots rather than the carrier ontology. Individual generic parenthood projects to P8810; lineage-level parentage projects to P1531. The cultivar/hybrid/breed rule is therefore modeled as representation specialization, not as proof that cultivars are ontologically incapable of parent/progenitor relations.

The exact `ParentSlotFibre` contains multiple hidden relation carriers over the same P8810 surface. In particular, anonymous donor and adoptive-parent carriers share the P8810 slot while disagreeing on the genetic coordinate. Thus the visible Wikidata slot cannot recover the hidden parent semantics.

A compatible surface-plus-carrier view is provided with `liftCarrier` and `forgetCompatibility`, with `forgetAfterLift` proving the carrier is a retract of the compatible representation. This is the parenting-specific bridge to the pullback/retraction discipline already present in the Lean ontology work.

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
- `p1531SpecializationPreservesLineageParentCoordinate`
- `carrierRetractionIsExact`
- `oneParentTwoGeneticContributors`
- `parentGeneticsBiconditionalFailsBothDirections`

The intended boundary is:

`world/generative relation ≠ ontology projection ≠ constraint on preferred encoding ≠ disclosure authority`.
