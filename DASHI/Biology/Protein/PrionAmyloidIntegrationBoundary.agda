module DASHI.Biology.Protein.PrionAmyloidIntegrationBoundary where

-- Integration facade for the focused prion lane.  The four evidence levels are
-- strictly separated so a structural amyloid state cannot be promoted directly
-- to transmissibility, pathology, or lethality.
record PrionAmyloidIntegrationBoundary : Set₁ where
  field
    Protein : Set
    Host    : Set
    Tissue  : Set
    Burden  : Set

    AmyloidStructure      : Protein → Set
    CompatibleTemplating  : Protein → Protein → Set
    Transmissible         : Host → Host → Protein → Set
    PathologicalBurden    : Tissue → Burden → Set
    LethalBurden          : Burden → Set

    contact  : Protein → Protein → Protein
    transfer : Host → Host → Protein → Protein
    expose   : Protein → Tissue → Tissue

record PrionTemplatingWitness
  (P : PrionAmyloidIntegrationBoundary) : Set₁ where
  open PrionAmyloidIntegrationBoundary P
  field
    seed substrate : Protein
    seedIsAmyloid  : AmyloidStructure seed
    compatible     : CompatibleTemplating seed substrate
    convertedIsAmyloid : AmyloidStructure (contact seed substrate)

record PrionTransmissionWitness
  (P : PrionAmyloidIntegrationBoundary) : Set₁ where
  open PrionAmyloidIntegrationBoundary P
  field
    source target : Host
    seed : Protein
    transmissible : Transmissible source target seed
    transferredRemainsStructured : AmyloidStructure (transfer source target seed)

record PrionPathologyWitness
  (P : PrionAmyloidIntegrationBoundary) : Set₁ where
  open PrionAmyloidIntegrationBoundary P
  field
    seed   : Protein
    tissue : Tissue
    burden : Burden
    burdenAfterExposure : PathologicalBurden (expose seed tissue) burden

record PrionAuthorityBoundary : Set₁ where
  field
    amyloidDoesNotImplyPrion : Set
    templatingDoesNotImplyHostTransmission : Set
    transmissionDoesNotImplyPathology : Set
    pathologyDoesNotImplyImmediateLethality : Set
    singleMoleculeDoesNotImplyOrganismDeath : Set
