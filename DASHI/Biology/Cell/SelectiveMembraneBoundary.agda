module DASHI.Biology.Cell.SelectiveMembraneBoundary where

data Side : Set where
  inside outside : Side

data TransportMode : Set where
  simpleDiffusion facilitatedDiffusion activePump vesicular : TransportMode

-- A membrane establishes an oriented compartment and context-dependent selective
-- transport.  Enclosure alone is not promoted to cellular life.
record SelectiveMembraneSystem : Set₁ where
  field
    Species     : Set
    Membrane    : Set
    CellState   : Set
    Gradient    : Set
    Resource    : Set
    Flux        : Set

    concentrationGradient : Species → CellState → Gradient
    transportFlux :
      TransportMode → Membrane → Species → CellState → Flux

    PermeableTo    : Membrane → Species → Set
    DownGradient   : Species → CellState → Set
    AgainstGradient : Species → CellState → Set
    ResourceAvailable : Resource → CellState → Set
    MaintainsOrientation : Membrane → Side → Side → Set

record PassiveTransportWitness
  (M : SelectiveMembraneSystem) : Set₁ where
  open SelectiveMembraneSystem M
  field
    membrane : Membrane
    species  : Species
    state    : CellState

    permeable : PermeableTo membrane species
    downGradient : DownGradient species state

record ActiveTransportWitness
  (M : SelectiveMembraneSystem) : Set₁ where
  open SelectiveMembraneSystem M
  field
    membrane : Membrane
    species  : Species
    state    : CellState
    resource : Resource

    againstGradient : AgainstGradient species state
    resourceAvailable : ResourceAvailable resource state

record MembraneClosureBoundary : Set₁ where
  field
    enclosureIsNotMetabolism : Set
    permeabilityIsNotAgency  : Set
    voltageIsNotMemoryByDefinition : Set
    membraneIsNotSufficientForLife : Set
