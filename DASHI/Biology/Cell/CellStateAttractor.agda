module DASHI.Biology.Cell.CellStateAttractor where

-- A cell state couples genome regulation, chromatin, RNA, proteome, metabolism,
-- membrane organisation, environment, and developmental history.  Cell type is
-- therefore a phenotype quotient/attractor class, not a gene list.
record CoupledCellState : Set₁ where
  field
    GenomeState     : Set
    ChromatinState  : Set
    RNAState        : Set
    ProteomeState   : Set
    MetabolicState  : Set
    MembraneState   : Set
    Environment     : Set
    History         : Set
    CellState       : Set

    assemble :
      GenomeState → ChromatinState → RNAState → ProteomeState →
      MetabolicState → MembraneState → Environment → History → CellState

    step : Environment → CellState → CellState

record CellPhenotypeQuotient
  (C : CoupledCellState) : Set₁ where
  open CoupledCellState C
  field
    Phenotype : Set
    CellType  : Set

    phenotype : CellState → Phenotype
    classify  : Phenotype → CellType

    EquivalentPhenotype : CellState → CellState → Set
    equivalentSound :
      (x y : CellState) → EquivalentPhenotype x y → Set

record CellStateAttractor
  (C : CoupledCellState) : Set₁ where
  open CoupledCellState C
  field
    Attractor : Set
    InBasin   : Attractor → CellState → Set
    StableIn  : Environment → Attractor → Set

    forwardInvariant :
      (environment : Environment) (attractor : Attractor) →
      StableIn environment attractor →
      (x : CellState) → InBasin attractor x →
      InBasin attractor (step environment x)

record CellTypeAttractorWitness
  {C : CoupledCellState}
  (Q : CellPhenotypeQuotient C)
  (A : CellStateAttractor C) : Set₁ where
  open CoupledCellState C
  open CellPhenotypeQuotient Q
  open CellStateAttractor A
  field
    environment : Environment
    state       : CellState
    attractor   : Attractor

    basinMembership : InBasin attractor state
    stability       : StableIn environment attractor

    AttractorRealisesCellType : Attractor → CellType → Set
    realisedType : AttractorRealisesCellType attractor (classify (phenotype state))

record CellStateBoundary : Set₁ where
  field
    genomeIsNotCellState : Set
    expressionIsNotCellTypeByDefinition : Set
    attractorIsNotSemanticIdentityByDefinition : Set
    historyAndEnvironmentRemainExplicit : Set
