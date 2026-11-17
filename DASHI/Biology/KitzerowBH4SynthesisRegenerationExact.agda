module DASHI.Biology.KitzerowBH4SynthesisRegenerationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Biology.KitzerowBH4ReactionChemistryExact as BH4

------------------------------------------------------------------------
-- Explicit de-novo synthesis and hydroxylase-cycle regeneration around the
-- shared BH4 species already used by PAH/TH/TPH/NOS/AGMO.
------------------------------------------------------------------------

triphosphate pyruvoylTetrahydropterin hydroxyBH4 nadh nad hPlus : Chemistry.Species
triphosphate = BH4.mkSpecies "triphosphate" "inorganic triphosphate"
pyruvoylTetrahydropterin = BH4.mkSpecies "6-pyruvoyl-5,6,7,8-tetrahydropterin" "PTPS product / SPR substrate"
hydroxyBH4 = BH4.mkSpecies "4a-hydroxytetrahydrobiopterin" "aromatic-amino-acid-hydroxylase pterin product"
nadh = BH4.mkSpecies "NADH" "reduced nicotinamide adenine dinucleotide"
nad = BH4.mkSpecies "NAD+" "oxidized nicotinamide adenine dinucleotide"
hPlus = BH4.mkSpecies "H+" "proton; biochemical standard-state bookkeeping"

ptps spr pcd dhpr : Chemistry.Species
ptps = BH4.mkSpecies "PTPS" "6-pyruvoyltetrahydropterin synthase; EC 4.2.3.12"
spr = BH4.mkSpecies "SPR" "sepiapterin reductase; EC 1.1.1.153"
pcd = BH4.mkSpecies "PCD" "4a-hydroxytetrahydrobiopterin dehydratase; EC 4.2.1.96"
dhpr = BH4.mkSpecies "DHPR" "6,7-dihydropteridine reductase; EC 1.5.1.34"

ptpsReaction : Chemistry.Transition
ptpsReaction = record
  { transitionId = "BH4-S2 PTPS triphosphate elimination"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = BH4.term BH4.dhnTriphosphate 1 ∷ []
  ; products = BH4.term pyruvoylTetrahydropterin 1 ∷ BH4.term triphosphate 1 ∷ []
  ; catalysts = ptps ∷ []
  ; rateLaw = BH4.mmRate "BRENDA EC 4.2.3.12"
  ; condition = BH4.biochemicalCondition "PTPS; Mg2+ and cellular context required"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

sprReaction : Chemistry.Transition
sprReaction = record
  { transitionId = "BH4-S3 SPR BH4-forming reduction"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      BH4.term pyruvoylTetrahydropterin 1
      ∷ BH4.term BH4.nadph 2
      ∷ BH4.term hPlus 2
      ∷ []
  ; products = BH4.term BH4.bh4 1 ∷ BH4.term BH4.nadp 2 ∷ []
  ; catalysts = spr ∷ []
  ; rateLaw = BH4.mmRate "BRENDA EC 1.1.1.153; two reductive NADPH steps in de-novo BH4 synthesis"
  ; condition = BH4.biochemicalCondition "SPR cytosolic reduction context"
  ; reversibility = Chemistry.conditionallyReversible
  ; evidence = Chemistry.literatureEstablished
  }

pcdReaction : Chemistry.Transition
pcdReaction = record
  { transitionId = "BH4-C1 PCD pterin dehydration"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = BH4.term hydroxyBH4 1 ∷ []
  ; products = BH4.term BH4.bh2 1 ∷ BH4.term BH4.h2o 1 ∷ []
  ; catalysts = pcd ∷ []
  ; rateLaw = BH4.mmRate "BRENDA EC 4.2.1.96 / Reactome R-HSA-71146"
  ; condition = BH4.biochemicalCondition "hydroxylase-cycle pterin regeneration"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

dhprReaction : Chemistry.Transition
dhprReaction = record
  { transitionId = "BH4-C2 DHPR reduction back to BH4"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = BH4.term BH4.bh2 1 ∷ BH4.term nadh 1 ∷ BH4.term hPlus 1 ∷ []
  ; products = BH4.term BH4.bh4 1 ∷ BH4.term nad 1 ∷ []
  ; catalysts = dhpr ∷ []
  ; rateLaw = BH4.mmRate "BRENDA EC 1.5.1.34 quinonoid-dihydrobiopterin reduction"
  ; condition = BH4.biochemicalCondition "DHPR pterin recycling context"
  ; reversibility = Chemistry.conditionallyReversible
  ; evidence = Chemistry.literatureEstablished
  }

canonicalBH4SupplyAndRecycleTransitions : List Chemistry.Transition
canonicalBH4SupplyAndRecycleTransitions =
  BH4.gch1Reaction ∷ ptpsReaction ∷ sprReaction ∷ pcdReaction ∷ dhprReaction ∷ []

record SharedBH4PoolBoundary : Set where
  constructor sharedBH4PoolBoundary
  field
    synthesisProducesSameBH4SpeciesConsumedDownstream : Bool
    synthesisProducesSameBH4SpeciesConsumedDownstreamIsTrue :
      synthesisProducesSameBH4SpeciesConsumedDownstream ≡ true
    regenerationProducesSameBH4SpeciesConsumedDownstream : Bool
    regenerationProducesSameBH4SpeciesConsumedDownstreamIsTrue :
      regenerationProducesSameBH4SpeciesConsumedDownstream ≡ true
    sharedSpeciesImpliesMeasuredAllocationShift : Bool
    sharedSpeciesImpliesMeasuredAllocationShiftIsFalse :
      sharedSpeciesImpliesMeasuredAllocationShift ≡ false
    fluxCompetitionQuantified : Bool
    fluxCompetitionQuantifiedIsFalse : fluxCompetitionQuantified ≡ false

canonicalSharedBH4PoolBoundary : SharedBH4PoolBoundary
canonicalSharedBH4PoolBoundary =
  sharedBH4PoolBoundary true refl true refl false refl false refl
