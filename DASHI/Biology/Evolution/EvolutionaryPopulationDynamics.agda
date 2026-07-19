module DASHI.Biology.Evolution.EvolutionaryPopulationDynamics where

-- Evolution is a population-level process coupling inheritance, variation,
-- selection, drift, development, and ecological feedback.  It is not identified
-- with development or goal-directed repair inside one organism.
record EvolutionarySystem : Set₁ where
  field
    Genotype    : Set
    Phenotype   : Set
    Individual  : Set
    Population  : Set
    Environment : Set
    Generation  : Set
    Variation   : Set
    Fitness     : Set
    Distribution : Set

    genotypeOf : Individual → Genotype
    develop    : Environment → Genotype → Distribution
    phenotypeOf : Environment → Individual → Phenotype

    reproduce  : Environment → Population → Population
    mutate     : Variation → Genotype → Genotype
    recombine  : Genotype → Genotype → Genotype
    select     : Environment → Phenotype → Fitness
    drift      : Generation → Population → Population
    ecologicalFeedback : Population → Environment → Environment

    Inherited : Individual → Individual → Set
    RealisesPhenotype : Genotype → Environment → Phenotype → Set

record EvolutionStepWitness
  (E : EvolutionarySystem) : Set₁ where
  open EvolutionarySystem E
  field
    generation : Generation
    environment : Environment
    population  : Population
    variation   : Variation

    nextPopulation : Population
    reproductionStep : nextPopulation ≡ reproduce environment population

    SelectionActsOnRealisedPhenotype : Set
    selectionWitness : SelectionActsOnRealisedPhenotype

    DriftAccountedFor : Set
    driftWitness : DriftAccountedFor

record GenotypePhenotypeContextWitness
  (E : EvolutionarySystem) : Set₁ where
  open EvolutionarySystem E
  field
    genotype : Genotype
    environment₁ environment₂ : Environment
    phenotype₁ phenotype₂ : Phenotype

    firstRealisation  : RealisesPhenotype genotype environment₁ phenotype₁
    secondRealisation : RealisesPhenotype genotype environment₂ phenotype₂

    PhenotypesDiffer : Phenotype → Phenotype → Set
    contextDependence : PhenotypesDiffer phenotype₁ phenotype₂

record MultilevelSelectionBoundary
  (E : EvolutionarySystem) : Set₁ where
  field
    SelectionLevel : Set
    FitnessAtLevel : SelectionLevel → EvolutionarySystem.Population E → Set
    CrossLevelCoupling : SelectionLevel → SelectionLevel → Set

record EvolutionAuthorityBoundary : Set₁ where
  field
    developmentIsNotEvolution : Set
    adaptationIsNotIndividualIntent : Set
    genotypeIsNotPhenotypeBlueprint : Set
    selectionIsNotMoralProgress : Set
    evolutionaryModelIsNotHistoricalProof : Set

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
